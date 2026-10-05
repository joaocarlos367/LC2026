import marimo

__generated_with = "0.25.0"
app = marimo.App(width="medium")

with app.setup:
    import marimo as mo
    import pandas as pd
    from pathlib import Path
    from ortools.sat.python import cp_model

    import glob
    import os


@app.cell
def _():
    def ler_dados(pasta):
        pasta = Path(pasta)
        return {
            "turmas": pd.read_csv(pasta / "turmas.csv"),
            "disciplinas": pd.read_csv(pasta / "disciplinas.csv"),
            "salas": pd.read_csv(pasta / "salas.csv"),
            "excecoes": pd.read_csv(pasta / "disponibilidade_excecoes.csv"),
        }

    dados = ler_dados("/mnt/c/Users/jotas/Desktop/TP1-LC/TP1.1/dados")
    dados2 = ler_dados("/mnt/c/Users/jotas/Desktop/TP1-LC/TP1.1/dados_v2") 
    dados_t = ler_dados("/mnt/c/Users/jotas/Desktop/TP1-LC/TP1.1/dados_teste")
    return dados, dados2, dados_t


@app.cell(hide_code=True)
def _():
    mo.md(r"""
    ### Implementação

    - Começamos por criar uma instância do solver.
    - Aqui estamos a carregar os dados de `turmas`, `salas` e `disciplinas` a partir de ficheiros CSV.
    - Definimos as opções de tempo (`dias` e `períodos`).
    - Pega nas listas de turmas, disciplinas, salas, dias e períodos e junta-as todas num dicionário X.
    """)
    return


@app.function
def criar_variaveis(dados):
    horario = cp_model.CpModel()

    turmas = dados["turmas"]["turma"].tolist()
    salas = dados["salas"]["sala"].tolist()
    dias = ["Seg", "Ter", "Qua", "Qui", "Sex"]
    periodos = list(range(1, 6))
    disciplinas = dados["disciplinas"]["disciplina"].tolist()

    x = {}
    for disc in disciplinas:
        for t in turmas:
            for s in salas:
                for d in dias:
                    for p in periodos:
                        x[t, disc, s, d, p] = horario.NewBoolVar(
                            f"x_{t}_{disc}_{s}_{d}_{p}"
                        )
                    
    return horario, x, turmas, salas, dias, periodos, disciplinas


@app.cell(hide_code=True)
def _():
    mo.md(r"""
    ### Primeira restrição

    A Restrição:
    R1. Uma turma não pode ter duas aulas em simultâneo.

    Esta restrição pode ser expressada da seguinte forma:

    $$\forall t \in \text{Turmas}, \quad \forall d \in \text{Dias}, \quad \forall p \in \text{Periodos}: \sum_{\text{disc} \in \text{Disciplinas                        }}\sum_{s \in \text{Salas}} x_{t, \text{disc}, s, d, p} \le 1$$
    """)
    return


@app.function
#R1. Uma turma não pode ter duas aulas em simultâneo.

#os for procuram em todas as salas, em todos os dias, em todos as horas
def aplicar_r1(horario, x, turmas, salas, dias, periodos, disciplinas):
    
    #fixa uma turma, um dia e um periodo de cada vez para aplicar a regra nesse momento
    for t in turmas:
        for d in dias:
            for p in periodos:
                
                #fixando uma turma, dia e período verifica se há mais alguma aula (sala + disciplina) a decorrer naquela turma, dia e periodo fixado
                horario.Add(
                    sum(
                        x[t, disc, s, d, p]
                        for disc in disciplinas
                        for s in salas
                        #se a soma for 0 ou 1 não há sobreposição.
                        #se for 0 essa turma nesse dia nesse período não têm aula
                        #se for 1 essa turma nesse dia nesse período têm uam aula
                        #se for 2+ essa turma nesse dia nesse período têm sobreposição
                    ) <= 1
                )


@app.cell(hide_code=True)
def _():
    mo.md(r"""
    ### Segunda restrição

    A restrição: R2 Cada disciplina cumpre *exatamente* a carga semanal definida em `disciplinas.csv`, para cada turma.

    Aqui queremos garantir que uma certa disciplina cumpre exatamente a quantidade de periodos estipulada na pasta "dados", para todas as disciplinas em todas as turmas. Essa restrição pode ser definida da seguinte forma:

    $$\forall t \in \text{Turmas}, \quad \forall \text{disc} \in \text{Disciplinas}: \sum_{s \in \text{Salas}} \sum_{d \in \text{Dias}} \sum_{p \in \text{Periodos}} x_{t, \text{disc}, s, d, p} = \text{carga}_{\text{disc}}$$
    """)
    return


@app.function
def aplicar_r2(horario, x, turmas, salas, dias, periodos, disciplinas,dados_usar):
    #R2. Cada disciplina cumpre *exatamente* a carga semanal definida em `disciplinas.csv`, para cada turma.
    for t in turmas:
        for _, row in dados_usar["disciplinas"].iterrows():
            # Extrai a carga horária específica desta disciplina na tabela
            disc = row["disciplina"]
            carga = row["carga_semanal"]

            #Fixa uma turma de cada vez e para cada turma verifica se a quantidade de aulas condiz com a carga horaria
            horario.Add(
                sum(
                    #tb pasas por salas pq caso contrario iria afixar uma sala e analisar apenas essa sala em todas as d e p
                    x[t, disc, s, d, p]
                    for s in salas
                    for d in dias
                    for p in periodos
                    #tendo a turma e disciplina fixada, percorre todas as salas, dias e periodos.
                    #Oq nos resta no 'pre' sum são todos as combinações possiveis da disciplina naquela turma, podendo haver 0 e 1
                    #se for 0 aquela discplina naquela turma n ocorre naquela s,d,p e se for 1 acontece
                    #o sum soma todas as ocorrências de
                ) == carga
            )


@app.cell(hide_code=True)
def _():
    mo.md(r"""
    ### Terceira restrição

    A restrição: R3. No máximo uma aula da mesma disciplina por dia, por turma — exceto disciplinas de duplo período (ver R4), em que o bloco de 2 tempos conta como uma só ocorrência nesse dia.

    Pretendemos agora fixar uma turma, uma disciplina e um dia para garantir que essa disciplina ocorra, no máximo, uma vez nesse dia (para disciplinas sem período duplo). A expressão que traduz esta restrição é:

    $$\forall t \in \text{Turmas}, \quad \forall \text{disc} \in \text{Disciplinas}_{\text{simples}}, \quad \forall d \in \text{Dias}: \sum_{s \in \text{Salas}} \sum_{p \in \text{Periodos}} x_{t, \text{disc}, s, d, p} \le 1$$
    """)
    return


@app.function
def aplicar_r3(horario, x, dados_usar, turmas, salas, dias, periodos):
    for t in turmas:
        for _, row in dados_usar["disciplinas"].iterrows():
            if row["duplo_periodo"] == "sim":
                continue
            disc = row["disciplina"]
            for d in dias:
                horario.Add(sum(x[t, disc, s, d, p] for s in salas for p in periodos) <= 1)


@app.cell(hide_code=True)
def _():
    mo.md(r"""
    ### Quarta restrição

    A restrição: R4. Disciplinas marcadas `duplo_periodo=sim` só podem ser dadas em blocos de 2 tempos consecutivos, no mesmo dia (nunca um tempo isolado)

    Neste código, fixamos uma turma e uma disciplina. Verificamos se a disciplina tem duplo período: se não tiver, é ignorada nesta restrição. Se for de duplo período, fixamos um dia e criamos um dicionário auxiliar com as aulas desse dia, utilizando-o para garantir que existem, no máximo, duas aulas dessa disciplina no dia. Após isso, fixamos cada período e verificamos se a aula nesse período tem aulas adjacentes. Devido à combinação destas duas regras, haverá exatamente uma aula adjacente (quando ocorre o bloco duplo de 2 tempos) ou nenhuma (quando não há aula nesse dia). Caso exista uma aula isolada, a condição falha.
    """)
    return


@app.function
def aplicar_r4(horario, x, dados_usar, turmas, salas, dias, periodos):
    # R4: disciplinas duplo_periodo=sim só em blocos de 2 tempos consecutivos
    for t in turmas:
        for _, row in dados_usar["disciplinas"].iterrows():
            if row["duplo_periodo"] != "sim":
                continue
            disc = row["disciplina"]
            for d in dias:
                #cria um dicionario auxiliar que armazena as aulas e períodos
                aula = {p: sum(x[t, disc, s, d, p] for s in salas) for p in periodos}

                # no máximo 2 tempos por dia (um único bloco)
                # se a soma for 0; não há aulas daquela disciplina naquele dia
                # se a soma for 1; há uma aula daquela disciplina naquele dia
                # se a soma for 2; há duas aulas daquela disciplina naquele dia
                # se a soma for 2+; há mais de duas aulas - Inválido
                horario.Add(sum(aula.values()) <= 2)

                # nenhum tempo isolado: se há aula em p, tem de haver em p-1 ou p+1
                for p in periodos:
                    #cria uma lista com os periodos que estão antes ou depois de p
                    vizinhos = [aula[q] for q in (p - 1, p + 1) if q in aula]
                    #se há aula em p, aula[p] == 1 ent a soma dos vizinhos tem de ser pelo menos 1, se for 0 então p não têm aulas adjacentes
                    horario.Add(aula[p] <= sum(vizinhos))


@app.cell(hide_code=True)
def _():
    mo.md(r"""
    ### Quinta restrição

    A restrição: R5. Um professor não pode dar duas aulas em simultâneo, mesmo que sejam a turmas ou disciplinas diferentes.

    Para impor esta restrição, começamos por agrupar as disciplinas por professor, obtendo para cada um a lista das disciplinas que leciona. Depois, para cada professor, dia e período, somamos as variáveis x sobre todas as turmas, todas as disciplinas desse professor e todas as salas. Essa soma conta o número de aulas que o professor tem nesse instante, e a restrição impõe que seja no máximo 1. Assim, o professor nunca fica atribuído a duas turmas, disciplinas ou salas ao mesmo tempo, mas pode ter períodos livres.
    Esta restrição pode ser traduzida nesta expressão:

    $$
    \forall \text{prof}, \, d \in \text{Dias}, \, p \in \text{Períodos}: \quad \sum_{t \in \text{Turmas}} \quad \sum_{disc \in \text{Disciplinas}(\text{prof})} \quad \sum_{s \in \text{Salas}} x_{t, \, disc, \, s, \, d, \, p} \le 1
    $$
    """)
    return


@app.function
def aplicar_r5(horario, x, turmas, salas, dias, periodos, dados_usar):
    # R5. Um professor não pode dar duas aulas em simultâneo
    # faz uma lista com todos os professores e as respetivas materias que lecionam
    prof_disciplinas = dados_usar["disciplinas"].groupby("professor")["disciplina"].apply(list)

    for prof, disciplinas_do_prof in prof_disciplinas.items():
        for d in dias:
            for p in periodos:
                horario.Add(
                    sum(
                        x[t, disc, s, d, p]
                        for t in turmas
                        for disc in disciplinas_do_prof 
                        for s in salas
                    ) <= 1
                )


@app.cell(hide_code=True)
def _():
    mo.md(r"""
    ### Sexta restrição

    A restrição: R6. Um professor só pode dar aulas nos tempos em que está disponível (`disponibilidade_excecoes.csv`)

    Para impor esta restrição, começamos por associar a cada professor as disciplinas que leciona. Depois, para cada linha do ficheiro, fixamos o professor, o dia e o período indisponíveis e somamos as variáveis x sobre todas as turmas, todas as disciplinas desse professor e todas as salas. Essa soma conta o número de aulas que o professor teria nesse instante, e a restrição impõe que seja igual a 0. Assim, nenhuma aula do professor pode ser atribuída aos períodos em que está indisponível.

    $$
    \forall (\text{prof}, d, p) \in \text{Exceções}: \quad \sum_{t \in \text{Turmas}} \quad \sum_{disc \in \text{Disciplinas}(\text{prof})} \quad \sum_{s \in \text{Salas}} x_{t, \, disc, \, s, \, d, \, p} = 0
    $$
    """)
    return


@app.cell
def _(dados):
    #R6. Um professor só pode dar aulas nos tempos em que está disponível (`disponibilidade_excecoes.csv`).
    def aplicar_r6(horario, x, turmas, salas, dias, periodos, dados_usar):
        # Mapeia cada disciplina ao respetivo professor
        disc_para_prof = dict(zip(dados_usar["disciplinas"]["disciplina"], dados["disciplinas"]["professor"]))

        # Para cada linha de indisponibilidade no CSV de exceções
        for _, linha in dados_usar["excecoes"].iterrows():
            prof = linha["professor"]
            d = linha["dia"]
            p = linha["periodo"]
            # este for percorre o ficheiro de disponibilidades e extrai os 3 dados de cada coluna
            # em cada for dá me um professor X e o dia e o periodo que não pdoe ter aula
        
        
            # Descobre as disciplinas que este professor leciona
            disciplinas_do_prof = [disc for disc, p_nome in disc_para_prof.items() if p_nome == prof]

            # Depois verifica que no dia e periodo indexados, o professor X vai ter o numero de aulas (turmas e salas) igual a 0
            horario.Add(
                sum(
                    x[t, disc, s, d, p]
                    for t in turmas
                    for disc in disciplinas_do_prof
                    for s in salas
                ) == 0
            )

    return (aplicar_r6,)


@app.cell(hide_code=True)
def _():
    mo.md(r"""
    ### Sétima restrição

    A restrição: R7. Cada aula ocupa uma sala. Disciplinas com `sala_especial`só podem usar salas desse tipo; as restantes usam salas
    `normal`. Em nenhum tempo o número de aulas a decorrer num tipo de sala pode exceder a `quantidade` desse tipo definida em `salas.csv`.

    Para fazer esta restrição primeiramente, determinamos, para cada disciplina, os tipos de sala que pode utilizar: se a disciplina tem sala_especial, apenas esse tipo (Laboratório ou Ginásio), caso contrário, apenas a Sala Normal. Para todos os restantes tipos de sala, impomos que a variável x seja 0, para todas as turmas, dias e períodos. Assim garantimos que cada disciplina corresponde á sua respetiva sala.

    Depois para cada tipo de sala, dia e período, somamos as variáveis x de todas as turmas e disciplinas e impomos que o total seja no máximo igual à quantidade desse tipo definida em salas.csv. Assim, em cada tempo nunca decorrem mais aulas num tipo de sala do que as salas existentes.
    """)
    return


@app.cell
def _(dados):
    def aplicar_r7(horario, x, dados_usar, turmas, salas, dias, periodos):
        df_salas = dados_usar["salas"]
        quantidade = {r["sala"]: int(r["quantidade"]) for _, r in df_salas.iterrows()}
        salas_normais = df_salas.loc[df_salas["tipo"] == "normal", "sala"].tolist()
        #cria uma lista com as diciplinas
        discs = dados["disciplinas"]["disciplina"].tolist()

        # R7.1: cada disciplina só pode usar as salas do tipo que exige
        #para cada disciplina extrai o nome da dsiciplina e a especialidade da sala
        for _, row in dados_usar["disciplinas"].iterrows():
            disc = row["disciplina"]
            esp = row["sala_especial"]
            #se a sala especial for vazia ent é pq é lecionada numa sala normal, caso contrario guarda o tipo de sala especial
            if pd.isna(esp) or str(esp).strip() == "":
                permitidas = salas_normais
            else:
                permitidas = [str(esp).strip()]
        
            #para cada sala:
            for s in salas:
                #verifica se está na lista de permitidas para a disciplina fixada
                if s not in permitidas:
                    for t in turmas:
                        for d in dias:
                            for p in periodos:
                                #e se não estiver proibe a ocorrência dessa disciplina nessa sala para todas as turmas, dais e periodos
                                horario.Add(x[t, disc, s, d, p] == 0)

        # R7.2: em cada tempo, aulas numa sala <= quantidade dessa sala
        #verificar que só há a quantidade definida de aulas nas salas
        for s in salas:
            for d in dias:
                for p in periodos:
                    horario.Add(
                        sum(x[t, disc, s, d, p] for t in turmas for disc in discs)
                        <= quantidade[s]
                    )

    return (aplicar_r7,)


@app.cell(hide_code=True)
def _():
    mo.md(r"""
    ### Objetivo

    Objetivo O1. Minimizar o número total de "buracos" no horário de cada professor — um buraco é um tempo livre, no meio do dia, entre a
    primeira e a última aula desse professor nesse dia.

    Para cada professor e dia, definimos uma variável booleana aula[p] que vale 1 se o professor leciona no período p, ligada às variáveis x pela soma das aulas desse professor nesse período. Em seguida, para cada período p, definimos uma variável buraco que é forçada a 1 sempre que existe um período anterior e um período posterior com aula e p está livre, através da desigualdade buraco ≥ aula[q] + aula[r] − aula[p] − 1, para q < p < r. O objetivo é minimizar a soma de todas as variáveis buraco, o que reduz os períodos livres intercalados entre aulas dos professores.
    """)
    return


@app.function
def aplicar_o1(horario, x, dados_usar, turmas, salas, dias, periodos):
    # O1: minimizar o número total de buracos nos horários dos professores
    discs_do_prof = dados_usar["disciplinas"].groupby("professor")["disciplina"].apply(list)

    buracos = []
    for prof, discs in discs_do_prof.items():
        for d in dias:
            # aula[p] = 1 se o professor dá aula no período p desse dia
            aula = {}
            for p in periodos:
                #um bool q vê se o prof tem aula no dia d no periodo p
                aula[p] = horario.NewBoolVar(f"aula_{prof}_{d}_{p}")
                horario.Add(
                    aula[p] == sum(x[t, disc, s, d, p] for t in turmas for disc in discs for s in salas)
                )
                # regista se o professor está a dar aula no período p

            # buraco[p] = 1 se p está livre entre duas aulas desse dia
            for p in periodos:
                b = horario.NewBoolVar(f"buraco_{prof}_{d}_{p}")
                buracos.append(b)
                for q in periodos:
                    for r in periodos:
                        #garante q só é buraco qnd tem aula antes e depois e no meio está livre
                        #se for 1 é pq é buraco se for 0 ou negativo n é buraco
                        if q < p < r:
                            horario.Add(b >= aula[q] + aula[r] - aula[p] - 1)

    horario.Minimize(sum(buracos))


@app.cell(hide_code=True)
def _():
    mo.md(r"""
    ### Código auxiliar de teste para as restrições

    Esta célula executa o solver para verificar a viabilidade do modelo e validar se todas as restrições assim como o objetivo foram aplicadas corretamente conseguindo, por sua vez, gerar um horario válido.
    """)
    return


@app.cell
def _(aplicar_r6, aplicar_r7, dados):
    def _resolver_modelo():
        modelo, x, turmas, salas, dias, periodos, disciplinas = criar_variaveis(dados)
        aplicar_r1(modelo, x, turmas, salas, dias, periodos, disciplinas)
        aplicar_r2(modelo, x, turmas, salas, dias, periodos, disciplinas, dados)
        aplicar_r3(modelo, x, dados, turmas, salas, dias, periodos)  # lê a variável dados
        aplicar_r4(modelo, x, dados, turmas, salas, dias, periodos)
        aplicar_r5(modelo, x, turmas, salas, dias, periodos, dados)
        aplicar_r6(modelo, x, turmas, salas, dias, periodos, dados)
        aplicar_r7(modelo, x, dados, turmas, salas, dias, periodos)
        solver = cp_model.CpSolver()
        solver.parameters.max_time_in_seconds = 30
        res = solver.Solve(modelo)
        print('Status:', solver.StatusName(res))
        if res in (cp_model.OPTIMAL, cp_model.FEASIBLE):
            print('Buracos:', int(solver.ObjectiveValue()))
        return (solver, res, x, turmas, salas, dias, periodos)
    solver_final, res, x, turmas, salas, dias, periodos = _resolver_modelo()
    return dias, periodos, res, salas, solver_final, turmas, x


@app.cell(hide_code=True)
def _():
    mo.md(r"""
    ### Construção do horário

    Caso o solver encontre uma solução viável, este trecho processa os resultados para apresentar uma grelha simplificada da agenda semanal de cada professor.

    - X: Indica um período com aula atribuída a esse docente.
    - .: Indica um período livre.
    """)
    return


@app.cell
def _(dados, dias, periodos, res, salas, solver_final, turmas, x):
    if res in (cp_model.OPTIMAL, cp_model.FEASIBLE):
        H0 = {k for k, v in x.items() if solver_final.Value(v)}  # H0: conjunto de aulas (turma, disciplina, sala, dia, período)
        print('Aulas em H0:', len(H0))
        _discs_do_prof = dados['disciplinas'].groupby('professor')['disciplina'].apply(list)
        for _prof, _discs in _discs_do_prof.items():
            print(f'\n{_prof}')
            for _d in dias:
                _linha = []
                for _p in periodos:
                    _ocupado = any(((t, disc, s, _d, _p) in H0 for t in turmas for disc in _discs for s in salas))
                    _linha.append('X' if _ocupado else '.')
                print(_d, ' '.join(_linha))
    else:
        H0 = None
    return (H0,)


@app.cell
def _(H0, aplicar_r6, aplicar_r7, dados2):
    import time

    def construir():
        modelo, x, turmas, salas, dias, periodos, disciplinas = criar_variaveis(dados2)
        aplicar_r1(modelo, x, turmas, salas, dias, periodos, disciplinas)
        aplicar_r2(modelo, x, turmas, salas, dias, periodos, disciplinas, dados2)
        aplicar_r3(modelo, x, dados2, turmas, salas, dias, periodos)  # lê a variável dados
        aplicar_r4(modelo, x, dados2, turmas, salas, dias, periodos)
        aplicar_r5(modelo, x, turmas, salas, dias, periodos, dados2)
        aplicar_r6(modelo, x, turmas, salas, dias, periodos, dados2)
        aplicar_r7(modelo, x, dados2, turmas, salas, dias, periodos)
        return (modelo, x, turmas, salas, dias, periodos)
    inicio = time.time()
    modelo, x_1, turmas_1, salas_1, dias_1, periodos_1 = construir()
    aplicar_o1(modelo, x_1, dados2, turmas_1, salas_1, dias_1, periodos_1)
    # H1 do zero (sem usar H0), só para comparar
    solver = cp_model.CpSolver()
    solver.parameters.max_time_in_seconds = 30
    solver.Solve(modelo)
    H1_zero = {k for k, v in x_1.items() if solver.Value(v)}
    tempo_zero = time.time() - inicio
    inicio = time.time()
    modelo, x_1, turmas_1, salas_1, dias_1, periodos_1 = construir()
    mudancas = []
    for k, v in x_1.items():
    # H1 incremental (a partir de H0)
        modelo.AddHint(v, 1 if k in H0 else 0)
        if k in H0:
            mudancas.append(1 - v)
    modelo.Minimize(sum(mudancas))
    solver = cp_model.CpSolver()  # começa a procurar no H0
    solver.parameters.max_time_in_seconds = 30
    solver.Solve(modelo)  # conta as aulas de H0 que deixam de existir
    H1 = {k for k, v in x_1.items() if solver.Value(v)}  # queremos mudar o menos possível
    tempo_inc = time.time() - inicio
    print('H1 do zero:      ', round(tempo_zero, 3), 's |', len(H0 - H1_zero), 'aulas alteradas')
    print('H1 incremental:  ', round(tempo_inc, 3), 's |', len(H0 - H1), 'aulas alteradas')
    print('Aulas que mudaram:')
    for aula in sorted(H0 - H1):
        print('  antes:', aula)
    for aula in sorted(H1 - H0):
        print('  agora:', aula)
    return H1, dias_1, periodos_1, salas_1, turmas_1


@app.cell
def _(H1, dados2, dias_1, periodos_1, salas_1, turmas_1):
    _discs_do_prof = dados2['disciplinas'].groupby('professor')['disciplina'].apply(list)
    for _prof, _discs in _discs_do_prof.items():
        print(f'\n{_prof}')
        for _d in dias_1:
            _linha = []
            for _p in periodos_1:
                _ocupado = any(((t, disc, s, _d, _p) in H1 for t in turmas_1 for disc in _discs for s in salas_1))
                _linha.append('X' if _ocupado else '.')
            print(_d, ' '.join(_linha))
    return


@app.cell
def _(aplicar_r6, aplicar_r7, dados_t):
    def _resolver_modelo():
        modelo, x, turmas, salas, dias, periodos, disciplinas = criar_variaveis(dados_t)
        aplicar_r1(modelo, x, turmas, salas, dias, periodos, disciplinas)
        aplicar_r2(modelo, x, turmas, salas, dias, periodos, disciplinas, dados_t)
        aplicar_r3(modelo, x, dados_t, turmas, salas, dias, periodos)
        aplicar_r4(modelo, x, dados_t, turmas, salas, dias, periodos)
        aplicar_r5(modelo, x, turmas, salas, dias, periodos, dados_t)
        aplicar_r6(modelo, x, turmas, salas, dias, periodos, dados_t)
        aplicar_r7(modelo, x, dados_t, turmas, salas, dias, periodos)
        aplicar_o1(modelo, x, dados_t, turmas, salas, dias, periodos)
        solver = cp_model.CpSolver()
        solver.parameters.max_time_in_seconds = 30
        res = solver.Solve(modelo)
        print('Status:', solver.StatusName(res))
        if res in (cp_model.OPTIMAL, cp_model.FEASIBLE):
            print('Buracos:', int(solver.ObjectiveValue()))
        return (solver, res, x, turmas, salas, dias, periodos)
    solver_final_1, res_1, x_2, turmas_2, salas_2, dias_2, periodos_2 = _resolver_modelo()
    if res_1 in (cp_model.OPTIMAL, cp_model.FEASIBLE):
        Ht = {k for k, v in x_2.items() if solver_final_1.Value(v)}
        print('Aulas em Ht:', len(Ht))
        _discs_do_prof = dados_t['disciplinas'].groupby('professor')['disciplina'].apply(list)
        for _prof, _discs in _discs_do_prof.items():
            print(f'\n{_prof}')
            for _d in dias_2:
                _linha = []
                for _p in periodos_2:
                    _ocupado = any(((t, disc, s, _d, _p) in Ht for t in turmas_2 for disc in _discs for s in salas_2))
                    _linha.append('X' if _ocupado else '.')
                print(_d, ' '.join(_linha))
    else:
        Ht = None
    return


@app.cell
def _(aplicar_r6, aplicar_r7):
    def gerar_horario_detalhado():
        import glob
        import os
        import pandas as pd
        from ortools.sat.python import cp_model

        pasta_base = "/mnt/c/Users/jotas/Desktop/TP1-LC/TP1.1"

        pasta_input = input(
            "Escolha a pasta dentro de TP1.1 (ex: dados, dados_teste, dados_v2): "
        ).strip()

        caminho_completo = (
            pasta_input
            if pasta_input.startswith(pasta_base)
            else os.path.join(pasta_base, pasta_input)
        )

        if not os.path.exists(caminho_completo):
            print(f"[ERRO] A pasta '{caminho_completo}' não existe.")
            return

        def obter_csv(palavra):
            ficheiros = glob.glob(os.path.join(caminho_completo, "*.csv"))
            for f in ficheiros:
                if palavra.lower() in os.path.basename(f).lower():
                    return f
            return None

        f_disc = obter_csv("disciplina")
        f_turmas = obter_csv("turma")
        f_salas = obter_csv("sala")
        f_excecoes = obter_csv("exceco") or obter_csv("indisponibilid")

        dados_t = {
            "disciplinas": pd.read_csv(f_disc) if f_disc else pd.DataFrame(),
            "turmas": pd.read_csv(f_turmas) if f_turmas else pd.DataFrame(),
            "salas": pd.read_csv(f_salas) if f_salas else pd.DataFrame(),
            "excecoes": pd.read_csv(f_excecoes)
            if f_excecoes
            else pd.DataFrame(columns=["professor", "dia", "periodo"]),
        }

        if dados_t["disciplinas"].empty:
            print("Não foi possível carregar os dados de disciplinas.")
            return

        print("\nComo deseja visualizar o horário?")
        print("1. Por Professor (Materia + Turma)")
        print("2. Por Turma (Disciplina + Sala + Professor)")
        opcao = input("Opção (1 ou 2): ").strip()

        modelo, x, turmas, salas, dias, periodos, disciplinas = criar_variaveis(
            dados_t
        )

        aplicar_r1(modelo, x, turmas, salas, dias, periodos, disciplinas)
        aplicar_r2(modelo, x, turmas, salas, dias, periodos, disciplinas, dados_t)
        aplicar_r3(modelo, x, dados_t, turmas, salas, dias, periodos)
        aplicar_r4(modelo, x, dados_t, turmas, salas, dias, periodos)
        aplicar_r5(modelo, x, turmas, salas, dias, periodos, dados_t)
        aplicar_r6(modelo, x, turmas, salas, dias, periodos, dados_t)
        aplicar_r7(modelo, x, dados_t, turmas, salas, dias, periodos)
        aplicar_o1(modelo, x, dados_t, turmas, salas, dias, periodos)

        solver = cp_model.CpSolver()
        solver.parameters.max_time_in_seconds = 30
        res = solver.Solve(modelo)

        print(f"\nStatus: {solver.StatusName(res)}")

        if res in (cp_model.OPTIMAL, cp_model.FEASIBLE):
            prof_por_disc = (
                dados_t["disciplinas"]
                .set_index("disciplina")["professor"]
                .to_dict()
            )

            aloc_prof = {}
            aloc_turma = {}

            for (t, disc, s, d, p), var in x.items():
                if solver.Value(var):
                    prof = prof_por_disc.get(disc, "")

                    # Formatação para Professor: Matéria + Turma (ex: MA 7ºA)
                    aloc_prof[(prof, d, p)] = f"{disc[:2].upper()} {t}"

                    # Formatação para Turma: P.Nome - Matéria - Sala (ex: P.Ana - MA - SN)
                    partes_sala = s.split()
                    if len(partes_sala) > 1:
                        sala_fmt = "".join(
                            p_nome[0].upper()
                            for p_nome in partes_sala
                            if p_nome.isalnum()
                        )
                    else:
                        sala_fmt = s[:2].upper()

                    aloc_turma[(t, d, p)] = (
                        f"{disc[:2].upper()}"
                    )

            if opcao == "2":
                # --- IMPRESSÃO POR TURMA ---
                for turma in sorted(turmas):
                    print(f"\n=== Turma {turma} ===")
                    for d in dias:
                        linha = []
                        for p in periodos:
                            info = aloc_turma.get(
                                (turma, d, p), "................."
                            )
                            linha.append(f"{info:^19}")
                        print(f"{d:<4} | " + " | ".join(linha))
            else:
                # --- IMPRESSÃO POR PROFESSOR ---
                professores = sorted(dados_t["disciplinas"]["professor"].unique())
                for prof in professores:
                    print(f"\n=== Prof. {prof} ===")
                    for d in dias:
                        linha = []
                        for p in periodos:
                            info = aloc_prof.get((prof, d, p), ".......")
                            linha.append(f"{info:^9}")
                        print(f"{d:<4} | " + " | ".join(linha))
        else:
            print("Sem solução viável.")


    gerar_horario_detalhado()
    return


if __name__ == "__main__":
    app.run()
