"""Independent re-computation of the classes for n <= 6:
 - posets generated from scratch (adding maximal elements), isomorphism via networkx;
 - Ladkani's Theorem 1.1 applied by brute force to ALL partitions X|_|Y and ALL
   families (Y_x) satisfying his hypotheses (no use of Theorem 3.2);
 - Coxeter polynomials and ranks via sympy.
Compares the number of classes with the census.

usage: python3 independent_check.py NMAX      (NMAX = 6 in the paper)"""
import sys, itertools
import networkx as nx
import sympy as sp
from networkx.algorithms.isomorphism import DiGraphMatcher

def closure(n, rel):
    R = [[i == j or (i, j) in rel for j in range(n)] for i in range(n)]
    for k in range(n):
        for i in range(n):
            if R[i][k]:
                for j in range(n):
                    if R[k][j]: R[i][j] = True
    return R

def to_graph(n, R):
    G = nx.DiGraph(); G.add_nodes_from(range(n))
    G.add_edges_from((i, j) for i in range(n) for j in range(n) if i != j and R[i][j])
    return G

def gen_posets(n):
    # all posets on n points up to iso: add a maximal element above an ideal
    if n == 0: return [[]]
    res = []
    for R in gen_posets(n - 1):
        m = n - 1
        for S in range(1 << m):
            els = [i for i in range(m) if S >> i & 1]
            if any(R[j][i] and not (S >> j & 1) for i in els for j in range(m)):
                continue
            R2 = [row[:] + [bool(S >> i & 1)] for i, row in enumerate(R)] + [[False] * m + [True]]
            res.append(R2)
    # dedupe by isomorphism
    uniq = []
    buckets = {}
    for R in res:
        G = to_graph(n, R)
        key = tuple(sorted((G.in_degree(v), G.out_degree(v)) for v in G))
        lst = buckets.setdefault(key, [])
        if any(nx.is_isomorphic(G, H) for H in lst): continue
        lst.append(G); uniq.append(R)
    return uniq

def find(G, reps):
    key = tuple(sorted((G.in_degree(v), G.out_degree(v)) for v in G))
    for idx, H in reps.get(key, []):
        if nx.is_isomorphic(G, H): return idx
    raise KeyError

def ladkani_pairs(n, R):
    """All negative posets obtained with P as positive poset, by brute force."""
    out = []
    full = range(n)
    for Xmask in range(1, (1 << n) - 1):
        X = [i for i in full if Xmask >> i & 1]; Y = [i for i in full if not Xmask >> i & 1]
        up = lambda y: {z for z in Y if R[y][z]}
        dn = lambda y: {z for z in Y if R[z][y]}
        subsets = [frozenset(s) for r in range(len(Y) + 1) for s in itertools.combinations(Y, r)]
        good_sub = [s for s in subsets if all(not (up(a) & up(b)) and not (dn(a) & dn(b)) for a, b in itertools.combinations(s, 2))]
        for fam in itertools.product(good_sub, repeat=len(X)):
            F = dict(zip(X, fam))
            ok = True
            for x in X:
                for x2 in X:
                    if x != x2 and R[x][x2]:
                        a, b = list(F[x]), list(F[x2])
                        if len(a) != len(b) or not any(all(R[u][v] for u, v in zip(a, perm)) for perm in itertools.permutations(b)):
                            ok = False; break
                if not ok: break
            if not ok: continue
            # positive poset must equal P
            same = True
            for x in X:
                for y in Y:
                    plus = any(R[yx][y] for yx in F[x])
                    if plus != R[x][y] or R[y][x]:
                        same = False; break
                if not same: break
            if not same: continue
            # negative poset
            Rm = [[R[i][j] if ((i in X) == (j in X)) else False for j in full] for i in full]
            for x in X:
                for y in Y:
                    Rm[y][x] = any(R[y][yx] for yx in F[x])
            out.append(Rm)
    return out

def coxeter(n, R):
    C = sp.Matrix(n, n, lambda i, j: 1 if R[i][j] else 0)
    Phi = -C.inv().T * C
    return tuple(sp.Poly(Phi.charpoly(sp.symbols('t')).as_expr(), sp.symbols('t')).all_coeffs())

for n in range(1, int(sys.argv[1]) + 1):
    Ps = gen_posets(n)
    reps = {}
    Gs = []
    for i, R in enumerate(Ps):
        G = to_graph(n, R); Gs.append(G)
        key = tuple(sorted((G.in_degree(v), G.out_degree(v)) for v in G))
        reps.setdefault(key, []).append((i, G))
    parent = list(range(len(Ps)))
    def f(x):
        while parent[x] != x: x = parent[x]
        return x
    for i, R in enumerate(Ps):
        for Rm in ladkani_pairs(n, R):
            j = find(to_graph(n, Rm), reps)
            a, b = f(i), f(j)
            if a != b: parent[max(a, b)] = min(a, b)
    conn = [i for i in range(len(Ps)) if nx.is_weakly_connected(Gs[i])]
    classes = len({f(i) for i in conn})
    cox = len({coxeter(n, Ps[i]) for i in conn})
    print("n=%d posets=%d connected=%d  Ladkani-classes(connected)=%d  distinct Coxeter polys(connected)=%d" % (n, len(Ps), len(conn), classes, cox))
    sys.stdout.flush()
