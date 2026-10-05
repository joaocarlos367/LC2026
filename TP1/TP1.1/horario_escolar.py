# /// script
# requires-python = ">=3.11"
# dependencies = [
#     "marimo>=0.24.2",
#     "pandas",
#     "ortools",
# ]
# ///

import marimo

__generated_with = "0.24.2"
app = marimo.App(width="medium")


@app.cell
def _():
    import statistics
    import time
    from collections import defaultdict
    from itertools import product
    from pathlib import Path

    import marimo as mo
    import pandas as pd
    from ortools.sat.python import cp_model

    return Path, cp_model, defaultdict, mo, pd, product, statistics, time


@app.cell
def _(mo):
    mo.md(r"""
    # Trabalho Prático: Gerador de Horário Escolar

    ## Abordagem e justificação das escolhas

    - **Modelação: CP-SAT (OR-Tools).** O problema é um CSP com objetivo,
      composto quase só por restrições lineares sobre variáveis booleanas
      (`x[turma, disciplina, sala, dia, período] = 1` se há aula). O CP-SAT
      lida bem com este tipo de modelo, permite *hints* (`AddHint`) e
      permite fixar partes do modelo — as duas coisas de que a construção
      incremental (R9) precisa.
    - **Leitura de dados: `pandas`.** Lê os CSV com tipos corretos e
      permite derivar as variações de dados (sala avariada, turma nova...)
      com poucas linhas. Todos os dados vêm de ficheiros (R8).
    - **Representação do horário:** um conjunto de tuplos
      `(turma, disciplina, sala, dia, período)`. É independente do solver,
      por isso serve para comparar horários (`H0` vs `H1`), para o
      verificador de restrições e para apresentar resultados.
    - **Estrutura:** (1) dados → (2) modelo R1–R7 + O1 → (3) verificador
      independente → (4) resolução do zero e incremental → (5) evidência
      (tempo e aulas alteradas) → (6) testes.
    """)
    return


@app.cell
def _(Path, pd):
    # O enunciado fixa a semana em 5 dias x 5 tempos.
    DIAS = ["Seg", "Ter", "Qua", "Qui", "Sex"]
    PERIODOS = [1, 2, 3, 4, 5]


    def ler_dados(pasta):
        """R8: lê SEMPRE os dados de uma pasta com os 4 CSV do enunciado."""
        pasta = Path(pasta)
        dados = {
            "turmas": pd.read_csv(pasta / "turmas.csv"),
            "disciplinas": pd.read_csv(pasta / "disciplinas.csv"),
            "salas": pd.read_csv(pasta / "salas.csv"),
            "excecoes": pd.read_csv(pasta / "disponibilidade_excecoes.csv"),
        }
        # limpar espaços em colunas de texto
        for _df in dados.values():
            for _col in _df.columns:
                if _df[_col].dtype == object or str(_df[_col].dtype).startswith("str"):
                    _df[_col] = _df[_col].astype("string").str.strip()
        return dados


    def preparar(dados):
        """Converte os DataFrames numa estrutura simples (dicionários/conjuntos)
        usada pelo modelo, pelo verificador e pelos cenários."""
        qtd = {r["sala"]: int(r["quantidade"]) for _, r in dados["salas"].iterrows()}
        normais = dados["salas"].loc[dados["salas"]["tipo"] == "normal", "sala"].tolist()
        disc = {}
        for _, r in dados["disciplinas"].iterrows():
            esp = r["sala_especial"]
            if pd.isna(esp) or str(esp).strip() == "":
                permitidas = list(normais)
            else:
                if str(esp) not in qtd:
                    raise ValueError(f"sala_especial '{esp}' não existe em salas.csv")
                permitidas = [str(esp)]
            disc[r["disciplina"]] = {
                "prof": r["professor"],
                "carga": int(r["carga_semanal"]),
                "duplo": str(r["duplo_periodo"]).strip().lower() == "sim",
                "salas": permitidas,
            }
        return {
            "turmas": dados["turmas"]["turma"].tolist(),
            "salas": list(qtd),
            "qtd": qtd,
            "disc": disc,
            "profs": sorted({v["prof"] for v in disc.values()}),
            "indisp": {
                (r["professor"], r["dia"], int(r["periodo"]))
                for _, r in dados["excecoes"].iterrows()
            },
        }

    return DIAS, PERIODOS, ler_dados, preparar


@app.cell
def _(mo):
    mo.md(r"""
    ## Modelo CP-SAT

    Variável: $x_{t,disc,s,d,p}\in\{0,1\}$ (turma, disciplina, tipo de sala, dia, período).

    **R7.1 por construção:** só se criam variáveis para os tipos de sala que
    a disciplina pode usar (a especial exigida, ou as normais).

    - **R1** $\sum_{disc,s} x_{t,disc,s,d,p}\le 1$
    - **R2** $\sum_{s,d,p} x_{t,disc,s,d,p}=\text{carga}_{disc}$
    - **R3** (disciplinas simples) $\sum_{s,p} x_{t,disc,s,d,p}\le 1$
    - **R4** (duplo período) no máximo 2 tempos por dia e, se há aula em $p$,
      há em $p-1$ ou $p+1$ ⇒ um único bloco de 2 tempos consecutivos
    - **R5** $\sum_{t,disc\in prof,s} x_{t,disc,s,d,p}\le 1$
    - **R6** $=0$ nos $(prof,d,p)$ de `disponibilidade_excecoes.csv`
    - **R7.2** $\sum_{t,disc} x_{t,disc,s,d,p}\le \text{quantidade}_s$
    - **O1** minimizar buracos: para $q<p<r$,
      $b_{prof,d,p}\ge a_q+a_r-a_p-1$, com $a_p=1$ se o professor dá aula em $p$.

    O construtor aceita `fixas`: pares (turma, disciplina) cujas aulas ficam
    **fixas como constantes** (não geram variáveis). É isto que torna o
    subproblema incremental pequeno.
    """)
    return


@app.cell
def _(DIAS, PERIODOS, cp_model, defaultdict, product):
    def _ad(modelo, expr):
        """Add que aceita expressões já constantes (bool), vindas das aulas fixas."""
        if isinstance(expr, bool):
            if not expr:
                modelo.AddBoolOr([])  # restrição impossível
            return
        modelo.Add(expr)


    def _registar(idx, P, t, disc, s, d, p, elem):
        prof = P["disc"][disc]["prof"]
        idx["turma_slot"][(t, d, p)].append(elem)
        idx["prof_slot"][(prof, d, p)].append(elem)
        idx["sala_slot"][(s, d, p)].append(elem)
        idx["par"][(t, disc)].append(elem)
        idx["par_dia"][(t, disc, d)].append(elem)
        idx["par_slot"][(t, disc, d, p)].append(elem)


    def construir(P, fixas=None):
        """Cria as variáveis. `fixas[(t,disc)] = [(s,d,p),...]` entram como constantes."""
        fixas = fixas or {}
        modelo = cp_model.CpModel()
        x = {}
        idx = {
            n: defaultdict(list)
            for n in ("turma_slot", "prof_slot", "sala_slot", "par", "par_dia", "par_slot")
        }
        for t in P["turmas"]:
            for disc, info in P["disc"].items():
                if (t, disc) in fixas:
                    for s, d, p in fixas[(t, disc)]:
                        _registar(idx, P, t, disc, s, d, p, 1)
                    continue
                for s in info["salas"]:
                    for d, p in product(DIAS, PERIODOS):
                        v = modelo.NewBoolVar(f"x_{t}_{disc}_{s}_{d}_{p}")
                        x[t, disc, s, d, p] = v
                        _registar(idx, P, t, disc, s, d, p, v)
        return modelo, x, idx


    def aplicar_r1(m, idx, P):
        # R1. Uma turma não pode ter duas aulas em simultâneo.
        for t, d, p in product(P["turmas"], DIAS, PERIODOS):
            _ad(m, sum(idx["turma_slot"].get((t, d, p), [])) <= 1)


    def aplicar_r2(m, idx, P):
        # R2. Cada disciplina cumpre exatamente a carga semanal, por turma.
        for t in P["turmas"]:
            for disc, info in P["disc"].items():
                _ad(m, sum(idx["par"].get((t, disc), [])) == info["carga"])


    def aplicar_r3(m, idx, P):
        # R3. No máximo uma aula da mesma disciplina por dia (exceto duplo período).
        for t in P["turmas"]:
            for disc, info in P["disc"].items():
                if info["duplo"]:
                    continue
                for d in DIAS:
                    _ad(m, sum(idx["par_dia"].get((t, disc, d), [])) <= 1)


    def aplicar_r4(m, idx, P):
        # R4. Duplo período: só blocos de 2 tempos consecutivos no mesmo dia.
        for t in P["turmas"]:
            for disc, info in P["disc"].items():
                if not info["duplo"]:
                    continue
                for d in DIAS:
                    aula = {p: sum(idx["par_slot"].get((t, disc, d, p), [])) for p in PERIODOS}
                    _ad(m, sum(aula.values()) <= 2)
                    for p in PERIODOS:
                        viz = [aula[q] for q in (p - 1, p + 1) if q in aula]
                        _ad(m, aula[p] <= sum(viz))


    def aplicar_r5(m, idx, P):
        # R5. Um professor não pode dar duas aulas em simultâneo.
        for prof, d, p in product(P["profs"], DIAS, PERIODOS):
            _ad(m, sum(idx["prof_slot"].get((prof, d, p), [])) <= 1)


    def aplicar_r6(m, idx, P):
        # R6. Um professor só dá aulas quando está disponível.
        for prof, d, p in sorted(P["indisp"]):
            _ad(m, sum(idx["prof_slot"].get((prof, d, p), [])) == 0)


    def aplicar_r7(m, idx, P):
        # R7.1 (tipo de sala por disciplina) já está garantido na construção.
        # R7.2: em cada tempo, nº de aulas num tipo de sala <= quantidade.
        for s, d, p in product(P["salas"], DIAS, PERIODOS):
            _ad(m, sum(idx["sala_slot"].get((s, d, p), [])) <= P["qtd"][s])


    def aplicar_o1(m, idx, P):
        # O1. Expressão com o nº total de buracos dos professores.
        buracos = []
        for prof in P["profs"]:
            for d in DIAS:
                aula = {}
                for p in PERIODOS:
                    aula[p] = m.NewBoolVar(f"aula_{prof}_{d}_{p}")
                    _ad(m, aula[p] == sum(idx["prof_slot"].get((prof, d, p), [])))
                for p in PERIODOS:
                    b = m.NewBoolVar(f"buraco_{prof}_{d}_{p}")
                    buracos.append(b)
                    for q, r in product(PERIODOS, PERIODOS):
                        if q < p < r:
                            m.Add(b >= aula[q] + aula[r] - aula[p] - 1)
        return sum(buracos)


    def construir_completo(P, fixas=None):
        m, x, idx = construir(P, fixas)
        for regra in (aplicar_r1, aplicar_r2, aplicar_r3, aplicar_r4,
                      aplicar_r5, aplicar_r6, aplicar_r7):
            regra(m, idx, P)
        buracos = aplicar_o1(m, idx, P)
        return m, x, buracos

    return (construir_completo,)


@app.cell
def _(mo):
    mo.md(r"""
    ## Verificador independente (R1–R7)

    Recebe um horário (conjunto de aulas) e os dados e devolve a lista de
    violações, **sem usar o solver**. Serve para três coisas: testar R1–R7,
    validar `H0`/`H1` e **detetar que aulas de `H0` deixam de ser válidas**
    quando os recursos mudam (base da construção incremental).
    R8 (dados vindos de ficheiros) cumpre-se na leitura (`ler_dados`).
    """)
    return


@app.cell
def _(DIAS, PERIODOS, defaultdict):
    def verificar(P, H):
        """Devolve [(regra, descrição, {(turma, disciplina) envolvidos})]."""
        viol = []
        por_ts, por_ps, por_ss = defaultdict(list), defaultdict(list), defaultdict(list)
        por_par, por_dia = defaultdict(list), defaultdict(list)
        turmas = set(P["turmas"])
        for k in sorted(H):
            t, disc, s, d, p = k
            if (t not in turmas or disc not in P["disc"] or s not in P["qtd"]
                    or d not in DIAS or p not in PERIODOS):
                viol.append(("R0", f"aula inválida {k}", set()))
                continue
            prof = P["disc"][disc]["prof"]
            por_ts[(t, d, p)].append(k)
            por_ps[(prof, d, p)].append(k)
            por_ss[(s, d, p)].append(k)
            por_par[(t, disc)].append(k)
            por_dia[(t, disc, d)].append(k)
            if s not in P["disc"][disc]["salas"]:
                viol.append(("R7", f"{disc} em sala não permitida ({s})", {(t, disc)}))
            if (prof, d, p) in P["indisp"]:
                viol.append(("R6", f"{prof} indisponível {d} {p}", {(t, disc)}))
        for (t, d, p), ks in por_ts.items():
            if len(ks) > 1:
                viol.append(("R1", f"{t} com {len(ks)} aulas em {d} {p}",
                             {(k[0], k[1]) for k in ks}))
        for t in P["turmas"]:
            for disc, info in P["disc"].items():
                n = len(por_par.get((t, disc), []))
                if n != info["carga"]:
                    viol.append(("R2", f"{t} {disc}: {n} aulas (carga {info['carga']})",
                                 {(t, disc)}))
                for d in DIAS:
                    ks = por_dia.get((t, disc, d), [])
                    if not info["duplo"]:
                        if len(ks) > 1:
                            viol.append(("R3", f"{t} {disc}: {len(ks)} aulas em {d}",
                                         {(t, disc)}))
                    else:
                        ps = sorted(k[4] for k in ks)
                        if ps and not (len(ps) == 2 and ps[1] - ps[0] == 1):
                            viol.append(("R4", f"{t} {disc}: tempos {ps} em {d} não formam um bloco",
                                         {(t, disc)}))
        for (prof, d, p), ks in por_ps.items():
            if len(ks) > 1:
                viol.append(("R5", f"{prof} com {len(ks)} aulas em {d} {p}",
                             {(k[0], k[1]) for k in ks}))
        for (s, d, p), ks in por_ss.items():
            if len(ks) > P["qtd"][s]:
                viol.append(("R7", f"{s}: {len(ks)} aulas > {P['qtd'][s]} em {d} {p}",
                             {(k[0], k[1]) for k in ks}))
        return viol


    def contar_buracos(P, H):
        """O1 calculado diretamente no horário (independente do solver)."""
        ocupados = defaultdict(set)
        for t, disc, s, d, p in H:
            ocupados[(P["disc"][disc]["prof"], d)].add(p)
        return sum((max(ps) - min(ps) + 1) - len(ps) for ps in ocupados.values())


    def alteracoes(Ha, Hb):
        """Aulas de `Ha` que não existem em `Hb` (mudaram de tempo/sala ou desapareceram)."""
        return len(set(Ha) - set(Hb))

    return alteracoes, contar_buracos, verificar


@app.cell
def _(mo):
    mo.md(r"""
    ## Construção incremental (R9)

    **Ideia.** Em vez de resolver tudo de novo, partimos de `H0` e tratamos
    só o que a mudança estragou. É uma pesquisa em *vizinhança* (LNS) com
    alargamento progressivo:

    1. **Detetar o que deixou de ser válido.** Corre-se o verificador sobre
       `H0` com os dados novos. Os pares (turma, disciplina) envolvidos em
       violações (professor indisponível, sala sem capacidade, professor
       substituído com choques...) mais os pares novos (turma nova) formam
       o conjunto de pares **livres**.
    2. **Fixar o resto.** As aulas dos restantes pares de `H0` entram no
       modelo como **constantes** — não geram variáveis. O subproblema é
       muito mais pequeno.
    3. **Objetivo lexicográfico:** primeiro minimizar as aulas de `H0`
       que mudam (peso grande), depois os buracos (desempate). Todas as
       variáveis recebem *hint* da solução `H0`.
    4. **Se o subproblema for impossível, alargar:** nível 1 liberta também
       os pares das mesmas turmas e dos mesmos professores; nível 2
       liberta tudo (equivale a resolver tudo, mas com *hints*). Em todos
       os níveis a solução respeita R1–R7.
    """)
    return


@app.cell
def _(
    DIAS,
    PERIODOS,
    alteracoes,
    construir_completo,
    contar_buracos,
    cp_model,
    time,
    verificar,
):
    def _resolver(m, tempo):
        solver = cp_model.CpSolver()
        solver.parameters.max_time_in_seconds = tempo
        solver.parameters.random_seed = 1
        return solver, solver.Solve(m)


    def _resultado(P, solver, status, x, fixas, t0, nivel):
        ok = status in (cp_model.OPTIMAL, cp_model.FEASIBLE)
        H = None
        if ok:
            H = {k for k, v in x.items() if solver.Value(v)}
            H |= {(t, disc, s, d, p) for (t, disc), L in fixas.items() for s, d, p in L}
        return {
            "H": H,
            "estado": solver.StatusName(status),
            "tempo": time.perf_counter() - t0,
            "buracos": contar_buracos(P, H) if ok else None,
            "nivel": nivel,
        }


    def resolver_do_zero(P, tempo=30.0):
        """H do zero: R1–R7 e minimiza O1 (buracos)."""
        t0 = time.perf_counter()
        m, x, buracos = construir_completo(P)
        m.Minimize(buracos)
        solver, status = _resolver(m, tempo)
        return _resultado(P, solver, status, x, {}, t0, "completo")


    def pares_em_conflito(P, H0):
        """Pares (turma, disciplina) cujas aulas em H0 deixam de ser válidas com os dados P."""
        H0r = {k for k in H0 if k[0] in P["turmas"] and k[1] in P["disc"]}
        livres = set()
        for _, _, pares in verificar(P, H0r):
            livres |= pares
        return H0r, livres


    def resolver_incremental(P, H0, tempo=30.0):
        """Novo horário válido a partir de H0, mudando o mínimo de aulas."""
        t0 = time.perf_counter()
        H0r, livres0 = pares_em_conflito(P, H0)
        todos = {(t, d) for t in P["turmas"] for d in P["disc"]}
        if not livres0:  # H0 continua válido
            return {"H": set(H0r), "estado": "H0 mantém-se válido",
                    "tempo": time.perf_counter() - t0,
                    "buracos": contar_buracos(P, H0r), "nivel": 0}
        profs0 = {P["disc"][d]["prof"] for _, d in livres0}
        turmas0 = {t for t, _ in livres0}
        vizinhancas = [
            livres0,
            livres0 | {(t, d) for t, d in todos
                       if t in turmas0 or P["disc"][d]["prof"] in profs0},
            todos,
        ]
        peso = len(P["profs"]) * len(DIAS) * len(PERIODOS) + 1  # > nº máximo de buracos
        for nivel, livres in enumerate(vizinhancas):
            fixas = {
                par: [(s, d, p) for (t, disc, s, d, p) in H0r if (t, disc) == par]
                for par in todos - livres
            }
            m, x, buracos = construir_completo(P, fixas)
            mudancas = []
            for k, v in x.items():
                m.AddHint(v, int(k in H0r))
                if k in H0r:
                    mudancas.append(1 - v)
            m.Minimize(peso * sum(mudancas) + buracos)
            solver, status = _resolver(m, tempo)
            if status in (cp_model.OPTIMAL, cp_model.FEASIBLE):
                return _resultado(P, solver, status, x, fixas, t0, nivel)
        return {"H": None, "estado": "INFEASIBLE", "tempo": time.perf_counter() - t0,
                "buracos": None, "nivel": 2}

    return resolver_do_zero, resolver_incremental


@app.cell
def _(PERIODOS, DIAS, pd):
    def grelha_turma(H, turma):
        g = pd.DataFrame("", index=PERIODOS, columns=DIAS)
        g.index.name = turma
        for t, disc, s, d, p in H:
            if t == turma:
                g.loc[p, d] = f"{disc} ({s})"
        return g


    def grelha_prof(P, H, prof):
        g = pd.DataFrame("", index=PERIODOS, columns=DIAS)
        g.index.name = prof
        for t, disc, s, d, p in H:
            if P["disc"][disc]["prof"] == prof:
                g.loc[p, d] = f"{t} · {disc}"
        return g


    def diferencas(Ha, Hb):
        linhas = [("removida (H0)", *k) for k in sorted(set(Ha) - set(Hb))]
        linhas += [("nova (H1)", *k) for k in sorted(set(Hb) - set(Ha))]
        return pd.DataFrame(
            linhas, columns=["", "turma", "disciplina", "sala", "dia", "período"]
        )

    return diferencas, grelha_prof, grelha_turma


@app.cell
def _(
    alteracoes,
    ler_dados,
    pd,
    preparar,
    resolver_do_zero,
    resolver_incremental,
    statistics,
    verificar,
):
    def medir(f, reps):
        tempos, out = [], None
        for _ in range(reps):
            out = f()
            tempos.append(out["tempo"])
        out["tempo_mediana"] = statistics.median(tempos)
        return out


    def comparar(P0, H0, P1, reps=5):
        """H1 do zero vs H1 incremental, com os mesmos dados novos P1."""
        zero = medir(lambda: resolver_do_zero(P1), reps)
        inc = medir(lambda: resolver_incremental(P1, H0), reps)
        linhas = []
        for nome, r in (("H1 do zero (sem H0)", zero), ("H1 incremental (a partir de H0)", inc)):
            ok = r["H"] is not None
            linhas.append({
                "método": nome,
                "estado": r["estado"],
                "tempo (ms)": round(r["tempo_mediana"] * 1000, 1),
                "aulas alteradas vs H0": alteracoes(H0, r["H"]) if ok else None,
                "buracos": r["buracos"],
                "violações R1–R7": len(verificar(P1, r["H"])) if ok else None,
                "nível": r["nivel"],
            })
        return zero, inc, pd.DataFrame(linhas)


    def fluxo(pasta0, pasta1, reps=5):
        """Fluxo completo do enunciado: dados → H0; dados novos → H1."""
        P0 = preparar(ler_dados(pasta0))
        r0 = resolver_do_zero(P0)
        P1 = preparar(ler_dados(pasta1))
        zero, inc, tabela = comparar(P0, r0["H"], P1, reps)
        return {"P0": P0, "r0": r0, "P1": P1, "zero": zero, "inc": inc, "tabela": tabela}

    return comparar, fluxo


@app.cell
def _(mo):
    mo.md(r"""
    ## Resultados — dados fornecidos (`dados/` → `dados_v2/`)
    """)
    return


@app.cell
def _(Path, fluxo, mo):
    _base = mo.notebook_dir() or Path.cwd()
    base = fluxo(_base / "dados", _base / "dados_v2")
    base["tabela"]
    return (base,)


@app.cell
def _(base, diferencas, grelha_prof, grelha_turma, mo):
    _H0, _H1 = base["r0"]["H"], base["inc"]["H"]
    mo.vstack([
        mo.md(f"**H0**: estado `{base['r0']['estado']}`, buracos = {base['r0']['buracos']}."),
        mo.hstack([grelha_turma(_H0, t) for t in base["P0"]["turmas"]]),
        mo.md("**H1 incremental** (dados_v2): grelhas por turma"),
        mo.hstack([grelha_turma(_H1, t) for t in base["P1"]["turmas"]]),
        mo.md("**Prof. Ana em H1** (indisponível à sexta nos tempos 4 e 5)"),
        grelha_prof(base["P1"], _H1, "Prof. Ana"),
        mo.md("**Aulas que mudaram entre H0 e H1**"),
        diferencas(_H0, _H1),
    ])
    return


@app.cell
def _(mo):
    mo.md(r"""
    ## Outras alterações de recursos

    Variações sobre `dados/`, geradas com `pandas` (sem ficheiros novos):
    professor indisponível, sala com menos capacidade (avaria), turma nova,
    professor substituído. Cada uma é comparada: do zero vs incremental a
    partir do mesmo `H0`.
    """)
    return


@app.cell
def _(Path, base, comparar, ler_dados, mo, pd, preparar):
    def _copia(d):
        return {k: v.copy() for k, v in d.items()}


    def com_indisponibilidade(d, prof, dia, periodo):
        d = _copia(d)
        nova = pd.DataFrame([{"professor": prof, "dia": dia, "periodo": periodo}])
        d["excecoes"] = pd.concat([d["excecoes"], nova], ignore_index=True)
        return d


    def com_sala(d, sala, quantidade):
        d = _copia(d)
        d["salas"].loc[d["salas"]["sala"] == sala, "quantidade"] = quantidade
        return d


    def com_turma(d, turma):
        d = _copia(d)
        d["turmas"] = pd.concat([d["turmas"], pd.DataFrame([{"turma": turma}])], ignore_index=True)
        return d


    def com_professor(d, disciplina, novo):
        d = _copia(d)
        d["disciplinas"].loc[d["disciplinas"]["disciplina"] == disciplina, "professor"] = novo
        return d


    _dados0 = ler_dados((mo.notebook_dir() or Path.cwd()) / "dados")
    _cenarios = {
        "Prof. Ana indisponível Sex 4–5": lambda d: com_indisponibilidade(
            com_indisponibilidade(d, "Prof. Ana", "Sex", 4), "Prof. Ana", "Sex", 5),
        "Prof. Diana indisponível Seg 1–3": lambda d: com_indisponibilidade(
            com_indisponibilidade(
                com_indisponibilidade(d, "Prof. Diana", "Seg", 1), "Prof. Diana", "Seg", 2),
            "Prof. Diana", "Seg", 3),
        "Sala Normal passa de 6 para 1 (avaria)": lambda d: com_sala(d, "Sala Normal", 1),
        "Turma nova 7ºC": lambda d: com_turma(d, "7ºC"),
        "Inglês passa de Prof. Diana para Prof. Bruno": lambda d: com_professor(d, "Inglês", "Prof. Bruno"),
    }
    _linhas = []
    for _nome, _f in _cenarios.items():
        _P = preparar(_f(_dados0))
        _zero, _inc, _t = comparar(base["P0"], base["r0"]["H"], _P, reps=3)
        _t.insert(0, "cenário", _nome)
        _linhas.append(_t)
    cenarios_tabela = pd.concat(_linhas, ignore_index=True)
    cenarios_tabela
    return (cenarios_tabela,)


@app.cell
def _(mo):
    mo.md(r"""
    ## Testes automáticos de R1–R7

    Parte-se de um horário válido (`H0`) e **estraga-se** de propósito, de
    uma forma por restrição. O teste passa se o verificador deteta essa
    regra. Também se confirma que o horário original não tem violações.
    """)
    return


@app.cell
def _(DIAS, PERIODOS, base, pd, verificar):
    _P, _H = base["P0"], base["r0"]["H"]


    def _mut_r1():
        t, disc, s, d, p = sorted(_H)[0]
        outra = next(x for x in _P["disc"] if x != disc)
        return _H | {(t, outra, _P["disc"][outra]["salas"][0], d, p)}


    def _mut_r2():
        return _H - {sorted(_H)[0]}


    def _mut_r3():
        t, disc, s, d, p = next(k for k in sorted(_H) if not _P["disc"][k[1]]["duplo"])
        q = 1 if p != 1 else 2
        return _H | {(t, disc, s, d, q)}


    def _mut_r4():
        t, disc, s, d, p = next(k for k in sorted(_H) if _P["disc"][k[1]]["duplo"])
        bloco = sorted(k for k in _H if k[:2] == (t, disc) and k[3] == d)
        resto = bloco[1]
        q = next(q for q in PERIODOS if abs(q - resto[4]) > 1)
        return (_H - {bloco[0]}) | {(t, disc, s, d, q)}


    def _mut_r5():
        t, disc, s, d, p = sorted(_H)[0]
        t2 = next(x for x in _P["turmas"] if x != t)
        return _H | {(t2, disc, s, d, p)}


    def _mut_r6():
        prof, d, p = sorted(_P["indisp"])[0]
        disc = next(x for x, i in _P["disc"].items() if i["prof"] == prof)
        return _H | {(_P["turmas"][0], disc, _P["disc"][disc]["salas"][0], d, p)}


    def _mut_r7_sala():
        t, disc, s, d, p = sorted(_H)[0]
        errada = next(x for x in _P["salas"] if x not in _P["disc"][disc]["salas"])
        return (_H - {(t, disc, s, d, p)}) | {(t, disc, errada, d, p)}


    def _mut_r7_cap():
        s = next(x for x in _P["salas"] if _P["qtd"][x] < len(_P["turmas"]))
        disc = next(x for x, i in _P["disc"].items() if s in i["salas"])
        return _H | {(t, disc, s, "Seg", 5) for t in _P["turmas"][: _P["qtd"][s] + 1]}


    _casos = [
        ("R1", "duas aulas da mesma turma no mesmo tempo", _mut_r1),
        ("R2", "falta uma aula (carga não cumprida)", _mut_r2),
        ("R3", "disciplina simples duas vezes no mesmo dia", _mut_r3),
        ("R4", "tempo de duplo período isolado", _mut_r4),
        ("R5", "professor em duas turmas ao mesmo tempo", _mut_r5),
        ("R6", "aula quando o professor está indisponível", _mut_r6),
        ("R7", "disciplina numa sala de tipo errado", _mut_r7_sala),
        ("R7", "mais aulas do que salas desse tipo", _mut_r7_cap),
    ]
    _linhas = [{"regra": "—", "caso": "horário gerado (H0) sem violações",
                "detetado": len(verificar(_P, _H)) == 0}]
    for _r, _desc, _f in _casos:
        _linhas.append({"regra": _r, "caso": _desc,
                        "detetado": any(v[0] == _r for v in verificar(_P, _f()))})
    testes = pd.DataFrame(_linhas)
    assert testes["detetado"].all(), testes
    testes
    return (testes,)


@app.cell
def _(mo):
    mo.md(r"""
    ## Outro conjunto de dados (sem nada *hardcoded*)

    `dados_teste/`: **4 turmas**, **2 disciplinas novas** (Geografia, Artes
    com sala `Ateliê`), um professor novo por disciplina e outra exceção de
    disponibilidade. `dados_teste_v2/`: **turma nova** (7ºE), Prof. Ana
    indisponível à sexta (tempos 4–5) e menos uma sala normal.
    """)
    return


@app.cell
def _(Path, fluxo, mo):
    _base = mo.notebook_dir() or Path.cwd()
    extra = fluxo(_base / "dados_teste", _base / "dados_teste_v2", reps=3)
    extra["tabela"]
    return (extra,)


if __name__ == "__main__":
    app.run()
