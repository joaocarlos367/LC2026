#!/usr/bin/env python
# coding: utf-8

# # Exercício 3 – Multiplicação de inteiros (Lógica Computacional)
# 
# Este notebook modela, em pySMT com `BitVec`'s, o algoritmo de multiplicação de inteiros (por somas e deslocamentos) como um **SFOTS** e verifica propriedades sobre ele com **k-indução** (usando o Z3 como solver).
# 

# ## Alínea a) – Modelo SFOTS em pySMT com BitVec's

# Importamos o pySMT e fixamos o tamanho $n$ dos bitvectors

# In[3]:


from pysmt.shortcuts import *
from pysmt.typing import BVType

n = 8
BV_N = BVType(n)
BV_PC = BVType(3)   


# Codificamos os nodos do CFA como constantes e criamos duas funções auxiliares para construir constantes bitvector.

# In[4]:


INIT, SKIP, LEFT, RIGHT, STOP, ERROR = range(6)
NOMES = ["init", "skip", "left", "right", "stop", "error"]

def pcv(v): return BV(v, 3)
def bv(v):  return BV(v, n)


# `declare(i)` cria a $i$-ésima cópia das variáveis de estado.

# In[5]:


def declare(i):
    state = {}
    state['pc'] = Symbol(f'pc{i}', BV_PC)
    for v in ['a', 'b', 'x', 'y', 'z']:
        state[v] = Symbol(f'{v}{i}', BV_N)
    return state


# ### Estado inicial e estado de erro
# 
# - `init`: $pc = \text{init} \wedge x = a \wedge y = b \wedge z = 0$
# - `error`: $pc = \text{error}$

# In[6]:


def init(state):
    return And(Equals(state['pc'], pcv(INIT)),
               Equals(state['x'], state['a']),
               Equals(state['y'], state['b']),
               Equals(state['z'], bv(0)))

def error(state):
    return Equals(state['pc'], pcv(ERROR))


# ### Predicados auxiliares
# 
# - `par(y)`: o bit menos significativo de `y` é 0.
# - `ovf_x(x)`: `x << 1` perde o bit mais significativo, ou seja, $x \ge 2^{n-1}$ (sem sinal).
# - `ovf_z(z, x)`: a soma `z + x` dá *carry*, isto é, o resultado (módulo $2^n$) é menor do que `z`.
# - `mantem(c, p, vs)`: as variáveis em `vs` não mudam na transição.

# In[7]:


def par(y):      return Equals(BVAnd(y, bv(1)), bv(0))
def ovf_x(x):    return BVUGE(x, bv(2**(n-1)))
def ovf_z(z, x): return BVULT(BVAdd(z, x), z)

def mantem(c, p, vs):
    return And([Equals(p[v], c[v]) for v in vs])


# ### Relação de transição
# 
# Uma disjunção com uma cláusula por ramo do CFA:
# 
# | Transição | Condição | Efeito |
# |---|---|---|
# | init → skip | – | nada muda |
# | skip → left | $y \neq 0 \wedge \text{even}(y)$ | nada muda |
# | skip → right | $y \neq 0 \wedge \text{odd}(y)$ | nada muda |
# | skip → stop | $y = 0$ | nada muda |
# | left → skip | sem overflow em $x$ | $x'=x\ll1,\ y'=y\gg1,\ z'=z$ |
# | left → error | overflow em $x$ | nada muda |
# | right → skip | sem overflow em $z+x$ | $x'=x,\ y'=y-1,\ z'=z+x$ |
# | right → error | overflow em $z+x$ | nada muda |
# | stop → stop, error → error | – | nada muda (para a relação ser total) |
# 
# As condições de overflow e de não-overflow são mutuamente exclusivas, o que implementa a precedência do erro.

# In[8]:


def trans(curr, prox):
    ab  = mantem(curr, prox, ['a', 'b'])
    xyz = mantem(curr, prox, ['x', 'y', 'z'])
    pc  = lambda s, v: Equals(s['pc'], pcv(v))

    t_init  = And(pc(curr, INIT), pc(prox, SKIP), xyz, ab)

    t_to_left = And(pc(curr,SKIP), pc(prox,LEFT), xyz, ab, NotEquals(curr['y'],bv(0)), par(curr['y']))
    t_to_right = And(pc(curr,SKIP), pc(prox,RIGHT), xyz, ab, NotEquals(curr['y'],bv(0)), Not(par(curr['y'])))
    t_to_stop = And(pc(curr,SKIP), pc(prox,STOP), xyz, ab, Equals(curr['y'],bv(0)))

    t_left = And(pc(curr, LEFT), pc(prox,SKIP), Not(ovf_x(curr['x'])), ab,
                Equals(prox['x'], BVLShl(curr['x'], bv(1))),
                Equals(prox['y'], BVLShr(curr['y'], bv(1))),
                Equals(prox['z'], curr['z'])
                )
    t_left_error = And(pc(curr, LEFT), pc(prox,ERROR), ovf_x(curr['x']), xyz, ab)
                    
    t_right = And(pc(curr, RIGHT), pc(prox,SKIP), Not(ovf_z(curr['z'], curr['x'])), ab,
                Equals(prox['x'], curr['x']),
                Equals(prox['y'], BVSub(curr['y'], bv(1))),
                Equals(prox['z'], BVAdd(curr['z'],curr['x']))
                )
    t_right_error = And(pc(curr, RIGHT), pc(prox,ERROR), ovf_z(curr['z'], curr['x']), xyz, ab)
                    
    t_stop_loop =  And(pc(curr,STOP), pc(prox,STOP), xyz, ab)
    t_err_loop  = And(pc(curr, ERROR), pc(prox, ERROR), xyz, ab)

    return Or(t_init, t_to_left, t_to_right, t_to_stop,
              t_left, t_left_error, t_right, t_right_error,
              t_stop_loop, t_err_loop)


# ### Verificação por k-indução
# 
# A função `k_induction` recebe o estado inicial, a relação de transição e a propriedade a provar, e faz duas verificações com o Z3:
# 
# 1. **Caso base:** vê se a propriedade vale nos primeiros `k` estados, a partir do estado inicial.
# 2. **Passo indutivo:** assume que a propriedade vale em `k` estados seguidos e vê se continua a valer no seguinte.
# 
# Em cada uma, o Z3 tenta encontrar um contra-exemplo. Se não encontrar nenhum, a propriedade está provada. Se encontrar, a função mostra-o e devolve `False`. Quando falha o passo indutivo, o contra-exemplo pode ser um estado que nunca acontece de facto, por isso isso não quer dizer que a propriedade seja falsa.

# In[16]:


def k_induction(k, init_f, declare_f, trans_f, prop_f):
    # caso base
    with Solver(name="z3") as s:
        st = [declare_f(i) for i in range(k)]
        s.add_assertion(init_f(st[0]))

        for i in range(k - 1):
            s.add_assertion(trans_f(st[i], st[i + 1]))

        s.add_assertion(Not(And([prop_f(x) for x in st])))

        if s.solve():
            print(f"Caso base falhou para k = {k}.")
            print("CE:", s.get_model())
            return False

    # passo indutivo
    with Solver(name="z3") as s:
        states = [declare_f(i) for i in range(k + 1)]
        constraints = []

        for i in range(k):
            constraints.append(prop_f(states[i]))
            constraints.append(trans_f(states[i], states[i + 1]))

        constraints.append(Not(prop_f(states[k])))

        s.add_assertion(And(constraints))

        if s.solve():
            print(f"Passo indutivo falhou para k = {k}")
            print("CE:", s.get_model())
            return False

    print(f"SUCESSO: propriedade provada com k = {k}")
    return True


# ## Alínea b) – Invariante $x*y+z=a*b$
# 
# O invariante do algoritmo é $x*y+z=a*b$.
# 
# No código, `prop` escreve o invariante com a aritmética dos próprios `BitVec`'s (módulo $2^n$), e `k_induction` prova-o com $k=2$.
# 
# Notas sobre o valor de $k$:
# - Com $k=1$ o passo indutivo falha, porque `prop` sozinho não diz que $y$ é par no nodo `left`. Esse facto vem da transição `skip → left`, que só aparece quando se olha dois passos para trás.
# - Por isso $k=2$ já chega para esta propriedade. O valor $k=14$ usado aqui é maior do que o necessário, mas continua a ser uma prova válida.

# In[22]:


prop = lambda st: Equals(
    BVAdd(BVMul(st['x'], st['y']), st['z']),
    BVMul(st['a'], st['b'])
)

k_induction(2, init, declare, trans, prop)


# ## Alínea c) – O estado de erro é inalcançável quando $a,b<2^{n/2}$
# 
# Aqui queremos provar que o `pc` nunca chega a `error`, assumindo $a,b<2^{n/2}$ no estado inicial. Com $n=8$, isto dá $a,b<16$, logo $a*b<256$ e o resultado cabe em $n$ bits.
# 
# - **`init_c`**: o estado inicial de a), com as duas restrições sobre $a$ e $b$.
# - **`prop_c`**: a propriedade a provar. Provar só $\neg\text{error}$ não funciona, porque o Z3 encontra estados impossíveis de onde se chega ao erro. Por isso juntamos:
#   - $a,b<2^{n/2}$, que se mantém porque $a$ e $b$ não mudam;
#   - o invariante $x*y+z=a*b$, mas calculado em $2n$ bits para o produto nunca dar a volta. Assim garantimos $x*y+z<256$, e os overflows deixam de acontecer.
# 
# Como esta propriedade implica $\neg\text{error}$, prová-la com k-indução (aqui basta $k=2$) mostra que o erro é inalcançável.

# In[20]:


m = n // 2
def init_c(state):
    return And(init(state), 
               BVULT(state['a'], bv(2**m)), 
               BVULT(state['b'], bv(2**m))
              )

def prop_c(state):
    z = lambda v: BVZExt(state[v], n)         
    return And(Not(error(state)),
               BVULT(state['a'], bv(2**m)), BVULT(state['b'], bv(2**m)),
               Equals(BVAdd(BVMul(z('x'), z('y')), z('z')),
                      BVMul(z('a'), z('b'))))

k_induction(32, init_c, declare, trans, prop_c)


# ## Alínea d) – Propriedade de animação
# 
# Mostramos duas coisas, que juntas dão a animação do sistema:
# 
# 1. **Não há bloqueios**: qualquer estado tem pelo menos um sucessor, isto é, a execução nunca fica presa.
# 2. **Terminação**: existe um **variante** $V$ (um valor natural que decresce estritamente em cada passo de um estado não terminal), pelo que não há execuções infinitas.
# 
# ### Invariante auxiliar
# 
# O variante só decresce se $y\neq0$ nos nodos `left` e `right` (e $y$ par em `left`). Isso é um invariante do sistema: `inv_d`. Diz que em `left` temos $y\neq0\wedge y$ par, e em `right` temos $y\neq0$. É 1-indutivo, porque só se entra em `left`/`right` a partir de `skip`, cujas transições impõem exatamente essas condições. A célula seguinte prova-o com `k_induction` e $k=1$.

# In[24]:


def inv_d(state):
    pc = lambda v: Equals(state['pc'], pcv(v))
    return And(Implies(pc(LEFT),  And(NotEquals(state['y'], bv(0)), par(state['y']))),
               Implies(pc(RIGHT), And(NotEquals(state['y'], bv(0)), Not(par(state['y'])))))

k_induction(1, init, declare, trans, inv_d)


# ### Variante e verificação de que decresce
# 
# O variante usa $n+2$ bits, para que $2y+2$ não dê a volta:
# 
# $$V(s)=\begin{cases}0 & \text{se } pc\in\{\text{stop},\text{error}\}\\ 2y+c(pc) & \text{caso contrário}\end{cases}\qquad c(\text{init})=2,\; c(\text{skip})=1,\; c(\text{left})=c(\text{right})=0$$
# 
# Como o variante decresce em todas as transições:
# 
# | Transição | $V$ antes | $V$ depois |
# |---|---|---|
# | init → skip | $2y+2$ | $2y+1$ |
# | skip → left / right | $2y+1$ | $2y$ |
# | skip → stop | $2y+1$ | $0$ |
# | left → skip | $2y$ | $y+1$ (menor, pois $y\ge2$) |
# | right → skip | $2y$ | $2y-1$ |
# | left / right → error | $2y>0$ | $0$ |
# 
# O código pede ao Z3 um contra-exemplo: um estado que satisfaz `inv_d`, **não é terminal**, tem uma transição para um sucessor onde $V$ **não** diminuiu (comparação sem sinal, `BVULT`). Se não existe (*unsat*), o variante decresce sempre, e imprime-se `True`.

# In[25]:


W = n + 2
def V(s):
    y2 = BVMul(BVZExt(s['y'], 2), BV(2, W))
    c = Ite(Equals(s['pc'], pcv(INIT)), BV(2, W),
        Ite(Equals(s['pc'], pcv(SKIP)), BV(1, W), BV(0, W)))
    return Ite(Or(Equals(s['pc'], pcv(STOP)), Equals(s['pc'], pcv(ERROR))),
               BV(0, W), BVAdd(y2, c))

terminal = lambda s: Or(Equals(s['pc'], pcv(STOP)), Equals(s['pc'], pcv(ERROR)))

with Solver(name="z3") as s:
    c = declare(0)
    p = declare(1)
    s.add_assertion(inv_d(c))
    s.add_assertion(trans(c, p))
    s.add_assertion(Not(terminal(c)))
    s.add_assertion(Not(BVULT(V(p), V(c))))   
    print("Variante decresce:", not s.solve())   


# ### Ausência de bloqueios
# 
# Pedimos ao Z3 um estado válido ($pc\le5$) que **não tenha nenhum sucessor**. Se não existir (*unsat*), o sistema nunca fica preso: `init`, `skip`, `left` e `right` têm sempre uma transição possível (as condições de overflow e de não-overflow são complementares) e `stop`/`error` têm um ciclo sobre si próprios.
# 
# Como o sistema nunca bloqueia e o variante diminui sempre, qualquer execução acaba em `stop` ou em `error`. Com as hipóteses da alínea c), o `error` é inalcançável, logo a execução termina em `stop`.

# In[14]:


with Solver(name="z3") as s:
    c, p = declare(0), declare(1)
    s.add_assertion(BVULE(c['pc'], pcv(5)))
    s.add_assertion(Not(Exists(list(p.values()), trans(c, p))))
    print("Sem bloqueios:", not s.solve())


# In[ ]:





# In[ ]:




