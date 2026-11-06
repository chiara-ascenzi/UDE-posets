#!/usr/bin/env python3
"""Generate the LaTeX appendix listing the ~L-classes of connected posets with n <= 6 elements.

Everything is recomputed from scratch (posets, admissible cuts, classes, Coxeter polynomials),
so the appendix agrees by construction with the definitions of the paper:
  admissible cut = Definition 3.1, negative poset = Corollary 3.3.
Usage: python3 gen_appendix.py > appendix_classes.tex
(the drawings and the table of Appendix A of the paper; about one minute)
"""
import itertools, sys
from fractions import Fraction

NMAX = 6

# ---------------------------------------------------------------- posets
# A poset on {0..n-1} is a tuple `down`: down[j] = bitmask of {i : i <= j}.

def naturally_labelled(n):
    """All posets on {0..n-1} in which i < j implies i < j as integers."""
    def rec(down):
        k = len(down)
        if k == n:
            yield tuple(down); return
        for I in range(1 << k):            # I = strict down-set of the new element k
            if all(down[i] & ~I == 0 for i in range(k) if I >> i & 1):
                yield from rec(down + [I | (1 << k)])
    yield from rec([])

def up_sets(P):
    n = len(P)
    return [sum(1 << j for j in range(n) if P[j] >> i & 1) for i in range(n)]

def leq(P, i, j):
    return P[j] >> i & 1 == 1

def covers(P):
    n = len(P); out = []
    for i in range(n):
        for j in range(n):
            if i != j and leq(P, i, j) and not any(k not in (i, j) and leq(P, i, k) and leq(P, k, j) for k in range(n)):
                out.append((i, j))
    return out

def from_covers(n, cov):
    down = [1 << j for j in range(n)]
    changed = True
    while changed:
        changed = False
        for (i, j) in cov:
            new = down[j] | down[i]
            if new != down[j]: down[j] = new; changed = True
        for j in range(n):
            for i in range(n):
                if down[j] >> i & 1 and down[i] & ~down[j]:
                    down[j] |= down[i]; changed = True
    return tuple(down)

def connected(P):
    n = len(P); seen = {0}; todo = [0]
    while todo:
        x = todo.pop()
        for y in range(n):
            if y not in seen and (leq(P, x, y) or leq(P, y, x)):
                seen.add(y); todo.append(y)
    return len(seen) == n

def canon(P):
    """Canonical form: minimum relation matrix over relabellings preserving simple invariants."""
    n = len(P); U = up_sets(P)
    inv = [(bin(P[v]).count('1'), bin(U[v]).count('1')) for v in range(n)]
    cells = {}
    for v in range(n): cells.setdefault(inv[v], []).append(v)
    keys = sorted(cells)
    best = None
    for choice in itertools.product(*[itertools.permutations(cells[k]) for k in keys]):
        order = [v for block in choice for v in block]
        mat = tuple(int(leq(P, order[a], order[b])) for a in range(n) for b in range(n))
        if best is None or mat < best: best = mat
    return (tuple(sorted(inv)), best)

def from_canon(key, n):
    mat = key[1]
    return tuple(sum(1 << a for a in range(n) if mat[a * n + b]) for b in range(n))

# ---------------------------------------------------------------- admissible cuts
def negative_posets(P):
    """All negative posets P^- of admissible cuts P = A u B with A, B nonempty (Def. 3.1, Cor. 3.3)."""
    n = len(P); full = (1 << n) - 1; U = up_sets(P); out = []
    for A in range(1, full):
        if any(P[a] & ~A for a in range(n) if A >> a & 1):          # A must be an ideal
            continue
        B = full & ~A
        M = {}
        for a in range(n):
            if A >> a & 1:
                UB = U[a] & B
                M[a] = [m for m in range(n) if UB >> m & 1 and P[m] & UB == 1 << m]
        ok = True
        for a, Ma in M.items():                                        # separation
            for m1, m2 in itertools.combinations(Ma, 2):
                if U[m1] & U[m2] & B or P[m1] & P[m2] & B: ok = False
        for a in M:                                                    # compatibility
            for a2 in M:
                if a != a2 and leq(P, a, a2):
                    for m in M[a]:
                        if not any(leq(P, m, m2) for m2 in M[a2]): ok = False
        if not ok: continue
        down = []
        for x in range(n):
            if A >> x & 1:
                d = P[x] & A
                for m in M[x]: d |= P[m] & B
            else:
                d = P[x] & B
            down.append(d)
        out.append(tuple(down))
    return out

# ---------------------------------------------------------------- invariants
def coxeter_poly(P):
    """chi_P(t) = det(t I - Phi_P), Phi_P = -C^{-T} C, as integer coefficient list (leading first)."""
    n = len(P)
    C = [[Fraction(int(leq(P, i, j))) for j in range(n)] for i in range(n)]
    # inverse of C by Gauss-Jordan
    A = [row[:] + [Fraction(int(i == j)) for j in range(n)] for i, row in enumerate(C)]
    for c in range(n):
        p = next(r for r in range(c, n) if A[r][c] != 0)
        A[c], A[p] = A[p], A[c]
        piv = A[c][c]; A[c] = [x / piv for x in A[c]]
        for r in range(n):
            if r != c and A[r][c] != 0:
                f = A[r][c]; A[r] = [x - f * y for x, y in zip(A[r], A[c])]
    Cinv = [row[n:] for row in A]
    Phi = [[-sum(Cinv[k][i] * C[k][j] for k in range(n)) for j in range(n)] for i in range(n)]
    # Faddeev-LeVerrier
    coeffs = [Fraction(1)]; Mk = [[Fraction(0)] * n for _ in range(n)]; c = Fraction(1)
    for k in range(1, n + 1):
        Mk = [[sum(Phi[i][l] * Mk[l][j] for l in range(n)) + (c if i == j else 0) for j in range(n)] for i in range(n)]
        AM = [[sum(Phi[i][l] * Mk[l][j] for l in range(n)) for j in range(n)] for i in range(n)]
        c = -sum(AM[i][i] for i in range(n)) / k
        coeffs.append(c)
    assert all(x.denominator == 1 for x in coeffs)
    return [int(x) for x in coeffs]

def hasse_paths_unique(P):
    """True iff the Hasse diagram has no two distinct paths with the same endpoints (kP hereditary)."""
    n = len(P); cov = covers(P)
    succ = {i: [j for (a, j) in cov if a == i] for i in range(n)}
    order = sorted(range(n), key=lambda x: bin(P[x]).count('1'))
    for s in range(n):
        cnt = [0] * n; cnt[s] = 1
        for x in order:
            if cnt[x]:
                for y in succ[x]: cnt[y] += cnt[x]
        if any(c > 1 for c in cnt): return False
    return True

def graph_type(P):
    """Type of the underlying Hasse graph, when it is a tree or a cycle (else None)."""
    n = len(P); cov = covers(P)
    adj = {v: set() for v in range(n)}
    for i, j in cov: adj[i].add(j); adj[j].add(i)
    deg = {v: len(adj[v]) for v in range(n)}
    if len(cov) == n - 1:                                   # tree
        branch = [v for v in range(n) if deg[v] >= 3]
        if not branch: return (0, r'$\mathbb{A}_{%d}$' % n)
        if len(branch) == 1:
            c = branch[0]; arms = []
            for w in adj[c]:
                length, prev, cur = 1, c, w
                while deg[cur] == 2:
                    nxt = next(u for u in adj[cur] if u != prev); prev, cur = cur, nxt; length += 1
                arms.append(length)
            arms.sort()
            if len(arms) == 3 and arms[:2] == [1, 1]: return (1, r'$\mathbb{D}_{%d}$' % n)
            if arms == [1, 2, 2]: return (2, r'$\mathbb{E}_6$')
            if arms == [1, 1, 1, 1]: return (3, r'$\widetilde{\mathbb{D}}_4$')
            return (5, 'wild')
        if len(branch) == 2 and all(deg[b] == 3 for b in branch) and \
           all(sum(1 for u in adj[b] if deg[u] == 1) == 2 for b in branch):
            return (3, r'$\widetilde{\mathbb{D}}_{%d}$' % (n - 1))
        return (5, 'wild')
    if len(cov) == n and all(deg[v] == 2 for v in range(n)) and hasse_paths_unique(P):   # cycle
        # p, q = numbers of arrows in the two directions along the cycle
        cyc = [0]; prev = None
        while len(cyc) < n:
            cur = cyc[-1]; nxt = next(u for u in sorted(adj[cur]) if u != prev and u not in cyc[1:] + ([cyc[0]] if len(cyc) > 1 else []))
            prev = cur; cyc.append(nxt)
        fwd = sum(1 for k in range(n) if (cyc[k], cyc[(k + 1) % n]) in cov)
        p, q = sorted((fwd, n - fwd))
        return (4, r'$\widetilde{\mathbb{A}}_{%d,%d}$' % (p, q))
    return None

def height(P):
    n = len(P); lev = levels(P); return max(lev)

def levels(P):
    n = len(P); lev = [0] * n
    order = sorted(range(n), key=lambda x: bin(P[x]).count('1'))
    for x in order:
        for (i, j) in covers(P):
            pass
    cov = covers(P)
    for x in order:
        lev[x] = max([lev[i] + 1 for (i, j) in cov if j == x], default=0)
    return lev

def ordinal_sum_of_antichains(P):
    """Return the level sizes if P = L_1 (+) ... (+) L_r with antichains of size >= 2, r >= 2."""
    n = len(P); lev = levels(P); r = max(lev) + 1
    sizes = [lev.count(i) for i in range(r)]
    if r < 2 or min(sizes) < 2: return None
    for x in range(n):
        for y in range(n):
            if x != y and (leq(P, x, y) != (lev[x] < lev[y])): return None
    return sizes

# ---------------------------------------------------------------- drawing
LAYOUT_COST = {}
def layout(P):
    n = len(P); lev = levels(P); cov = covers(P)
    L = max(lev) + 1
    byl = [[v for v in range(n) if lev[v] == l] for l in range(L)]
    best = None
    def seg_cross(p1, p2, p3, p4):
        def orient(a, b, c):
            v = (b[0]-a[0])*(c[1]-a[1]) - (b[1]-a[1])*(c[0]-a[0])
            return (v > 1e-9) - (v < -1e-9)
        o1, o2, o3, o4 = orient(p1,p2,p3), orient(p1,p2,p4), orient(p3,p4,p1), orient(p3,p4,p2)
        return o1 * o2 < 0 and o3 * o4 < 0
    offs = [0.0, -0.5, 0.5, -1.0, 1.0]
    for perms in itertools.product(*[itertools.permutations(b) for b in byl]):
        for off in itertools.product(offs, repeat=L - 1):
            off = (0.0,) + off
            pos = {}
            for l, b in enumerate(perms):
                k = len(b)
                for i, v in enumerate(b): pos[v] = (i - (k - 1) / 2 + off[l], l)
            cost = 0.0
            for (a, b), (c, d) in itertools.combinations(cov, 2):
                if len({a, b, c, d}) == 4 and seg_cross(pos[a], pos[b], pos[c], pos[d]): cost += 100
            for (a, b) in cov:
                (x1, y1), (x2, y2) = pos[a], pos[b]
                for w in range(n):
                    if w in (a, b): continue
                    xw, yw = pos[w]
                    if y1 < yw < y2:
                        t = (yw - y1) / (y2 - y1); xs = x1 + t * (x2 - x1)
                        if abs(xs - xw) < 0.3: cost += 1000
                cost += abs(x1 - x2) ** 2
            cost += 0.01 * sum(abs(o) for o in off)
            if best is None or cost < best[0]: best = (cost, pos)
    LAYOUT_COST[tuple(P)] = best[0]
    return best[1], cov

def tikz(P, name='', scale_note=None, baseline='bottom'):
    pos, cov = layout(P)
    bl = r'baseline=0pt' if baseline == 'bottom' else \
         r'baseline={([yshift=-.6ex]current bounding box.center)}'
    s = [r'\begin{tikzpicture}[poset,%s]' % bl]
    for v, (x, y) in sorted(pos.items()):
        s.append(r'\node[pt] (v%d) at (%g,%g) {};' % (v, round(x, 2), y))
    for (a, b) in cov:
        s.append(r'\draw[cov] (v%d) -- (v%d);' % (a, b))
    if name:
        s.append(r'\node[tag] at (current bounding box.south) {%s};' % name)
    if baseline != 'bottom':
        s.append(r'\path ([yshift=-4pt]current bounding box.south) ([yshift=4pt]current bounding box.north);')
    s.append(r'\end{tikzpicture}')
    return '\n'.join(s)

def latex_poly(c):
    n = len(c) - 1; terms = []
    for k, a in enumerate(c):
        e = n - k
        if a == 0: continue
        mon = '' if e == 0 else ('t' if e == 1 else 't^{%d}' % e)
        mag = abs(a)
        coef = ('%d' % mag) if (mag != 1 or e == 0) else ''
        sign = '-' if a < 0 else '+'
        terms.append((sign, coef + mon))
    out = ('-' if terms[0][0] == '-' else '') + terms[0][1]
    for sg, t in terms[1:]: out += ' %s %s' % (sg, t)
    return out

# ---------------------------------------------------------------- data
P_ALPHA = from_covers(6, [(0, 2), (0, 3), (1, 3), (1, 5), (2, 4), (2, 5), (3, 4)])
P_BETA = from_covers(6, [(0, 3), (0, 5), (1, 5), (2, 3), (2, 4), (4, 5)])
T3 = from_covers(5, [(0, 1), (1, 3), (3, 4), (0, 2), (2, 4)])
SQUARE = from_covers(4, [(0, 1), (0, 2), (1, 3), (2, 3)])

def classes(n):
    reps = {}
    for P in naturally_labelled(n):
        if connected(P):
            reps.setdefault(canon(P), P)
    keys = list(reps); idx = {k: i for i, k in enumerate(keys)}
    parent = list(range(len(keys)))
    def f(x):
        while parent[x] != x: parent[x] = parent[parent[x]]; x = parent[x]
        return x
    for k in keys:
        for Q in negative_posets(reps[k]):
            j = idx[canon(Q)]
            a, b = f(idx[k]), f(j)
            if a != b: parent[max(a, b)] = min(a, b)
    groups = {}
    for k in keys: groups.setdefault(f(idx[k]), []).append(reps[k])
    return list(groups.values())

TYPE_ORDER = ['A', 'D', 'E', r'\widetilde{\mathbb{D}', r'\widetilde{\mathbb{A}', 'wild']
def class_info(members):
    n = len(members[0])
    chi = coxeter_poly(members[0])
    assert all(coxeter_poly(Q) == chi for Q in members)
    types = {graph_type(Q) for Q in members if hasse_paths_unique(Q)} - {None}
    assert len(types) <= 1, types
    typ = types.pop() if types else None
    cat = typ[0] if typ else 9
    typ = typ[1] if typ else None
    keys = {canon(Q) for Q in members}
    remarks = []
    if n == 5 and canon(T3) in keys: remarks.append(('T3', r'$T_3$, Example~\ref{ex:tamari}'))
    if n == 4 and canon(SQUARE) in keys: remarks.append(('sq', r'$I_2\times I_2$, Example~\ref{ex:D4-square}'))
    sums = sorted({tuple(s) for Q in members if (s := ordinal_sum_of_antichains(Q))})
    if sums:
        remarks.append(('os', ', '.join('$' + r'\oplus'.join(map(str, s)) + '$' for s in sums)
                        + r', Proposition~\ref{prop:ordinal-sums}'))
    special = None
    if n == 6 and canon(P_ALPHA) in keys: special = 'alpha'
    if n == 6 and canon(P_BETA) in keys: special = 'beta'
    return dict(n=n, members=members, chi=chi, type=typ, cat=cat, remarks=remarks, special=special,
                hered=sum(1 for Q in members if hasse_paths_unique(Q)))

def sort_key(info):
    spec = {'alpha': 1, 'beta': 2}.get(info['special'], 0)
    return (spec, info['cat'], -len(info['members']), info['chi'])

def member_key(P):
    return (height(P), len(covers(P)), canon(P))

def tag_for(P, info):
    if len(P) == 5 and canon(P) == canon(T3): return '$T_3$'
    if len(P) == 4 and canon(P) == canon(SQUARE): return r'$I_2\times I_2$'
    s = ordinal_sum_of_antichains(P)
    if s: return '$' + r'\oplus'.join(map(str, s)) + '$'
    return ''

def representative(info):
    mem = info['members']
    if info['special'] == 'alpha': return P_ALPHA
    if info['special'] == 'beta': return P_BETA
    trees = [Q for Q in mem if len(covers(Q)) == len(Q) - 1]
    if trees:          # a tree orientation, preferably of height one (bipartite)
        return min(trees, key=lambda Q: (height(Q), canon(Q)))
    hered = [Q for Q in mem if hasse_paths_unique(Q)]
    pool = hered if hered else mem
    return min(pool, key=lambda Q: (len(covers(Q)), height(Q), canon(Q)))

def smith_cc(P):
    import sympy as sp
    from sympy.matrices.normalforms import smith_normal_form
    from sympy.polys.domains import ZZ
    m = len(P)
    C = sp.Matrix(m, m, lambda a, b: int(leq(P, a, b)))
    S = smith_normal_form(C + C.T, domain=ZZ)
    d = [abs(int(S[t, t])) for t in range(m)]
    nz = sorted(x for x in d if x); return nz + [0] * (m - len(nz))

# ---------------------------------------------------------------- fixed text
HEADER = r"""% =====================================================================
% Appendix generated by gen_appendix.py (do not edit the lists by hand).
% Packages needed in the preamble: tikz, longtable, booktabs, array, xcolor, amssymb, hyperref.
% Paste after \appendix (the \tikzset and \newcommand lines may also go in the preamble).
% The \ref and \cite labels are those of the LaTeX source of the paper.
% Output of: python3 gen_appendix.py > appendix_classes.tex
% =====================================================================
\tikzset{
  poset/.style={x=0.5cm, y=0.5cm},
  pt/.style={circle, fill, inner sep=0pt, minimum size=3pt},
  cov/.style={line width=0.5pt},     % arrows instead of segments: cov/.style={-{Stealth[length=3pt]}, shorten >=1pt}
  tag/.style={below=2pt, font=\scriptsize, inner sep=1pt},
}
\newcommand{\classhead}[5]{\par\medskip\noindent\textbf{Class #1.}\ #2~poset\ifnum#2>1 s\fi,
  $\chi_P(t) = #3$\if\relax\detokenize{#4}\relax\else, type #4\fi
  \if\relax\detokenize{#5}\relax\else; #5\fi.\par\nopagebreak}
\newenvironment{posetrow}{\par\noindent\raggedright\setlength{\lineskip}{7pt}}{\par\smallskip}
\newcommand{\posetsep}{\hspace{1.4em plus 0.8em}}

\section{The \texorpdfstring{$\sim_L$}{~L}-classes of connected posets with at most six elements}
\label{app:classes}

In this appendix we list the $\sim_L$-classes of connected posets with at most six elements, up to
isomorphism. Each $\sim_L$-class is contained in a class of universal derived equivalence
(Corollary~\ref{The associated universally derived equivalent poset}). By
Theorem~\ref{thm:classification-small-posets}, for posets with at most five elements the two
coincide, and they also coincide with the classes of derived equivalence of incidence algebras over
any field; for six elements the same holds except possibly for the classes $\alpha$ and $\beta$ of
Section~\ref{the case of six elements}. For more elements, distinct $\sim_L$-classes might still
consist of universally derived equivalent posets (Section~\ref{sec:completeness}); for this reason we
speak of $\sim_L$-classes.

It suffices to consider connected posets. If $P = X \sqcup Y$ is a disjoint union, the admissible
cuts of $P$ are exactly the partitions whose restrictions to $X$ and to $Y$ are admissible cuts,
possibly with an empty part, and the associated negative poset is the disjoint union of the two
negative posets. Hence the $\sim_L$-class of a poset is determined by the $\sim_L$-classes of its
connected components.

In the diagrams, larger elements are drawn higher and each segment is a covering relation. For each
class we give the number of its posets up to isomorphism, the Coxeter polynomial $\chi_P(t)$ of
Section~\ref{Derived invariants and the census}, which is the same for all posets of the class, and
the type of the class when it contains the orientations of a tree
(Corollary~\ref{cor:trees}) or an orientation of a cycle with no two distinct directed paths with the
same endpoints. For trees we use the names $\mathbb{A}_n$, $\mathbb{D}_n$, $\mathbb{E}_6$ of Dynkin
diagrams and $\widetilde{\mathbb{D}}_n$ of Euclidean diagrams, and we write \emph{wild} for the other
trees; $\widetilde{\mathbb{A}}_{p,q}$ denotes a cycle with $p$ arrows in one direction and $q$ in the
other. When a class contains neither, no type is given; in Table~\ref{tab:app-six} this is indicated
by a dash. In particular, the label \emph{wild} is used only for classes of orientations of trees,
and a dash gives no information on the representation type of the posets in the class. Posets that appear in the text are marked below their diagrams. The diagrams and the table
were generated by the script \texttt{gen\_appendix.py} of the repository, which recomputes the classes
directly from Definition~\ref{def admissible cuts} and
Corollary~\ref{The associated universally derived equivalent poset}; the numbers of posets and of
classes agree with Table~\ref{tab:small-poset-census}.
"""

FOOTER = r"""
\subsection{Connected posets with seven to nine elements}
\label{app:large}
For $n = 7, 8, 9$ there are $117$, $1\,284$ and $21\,197$ classes
(Table~\ref{tab:small-poset-census}), too many to be listed here. They are available in the
repository \url{https://github.com/chiara-ascenzi/UDE-posets} in machine-readable form: for each $n$, a file with one line per
connected poset, containing the digraph6 string of its Hasse diagram and the label of its
$\sim_L$-class. The digraph6 format, used by nauty~\cite{McKayPiperno}, encodes a directed graph as a
single line of printable ASCII characters.
"""

# ---------------------------------------------------------------- output
def main():
    out = []
    W = out.append
    data = {}
    for n in range(3, NMAX + 1):
        infos = sorted((class_info(m) for m in classes(n)), key=sort_key)
        data[n] = infos
        sys.stderr.write('n=%d: %d posets, %d classes, sizes %s\n' % (
            n, sum(len(i['members']) for i in infos), len(infos), [len(i['members']) for i in infos]))

    W(HEADER)
    W(r'\subsection{Connected posets with at most five elements}')
    W(r'\label{app:small}')
    W(r'For $n\le 2$ there is a single connected poset with $n$ elements. For $n=3,4,5$ we draw all '
      r'$3+10+44=57$ connected posets, grouped into their $1+3+6$ classes.')
    W('')
    for n in range(3, 6):
        for k, info in enumerate(data[n], 1):
            info['label'] = '%d.%d' % (n, k)
            mem = sorted(info['members'], key=member_key)
            head = r'\classhead{%s}{%d}{%s}{%s}{%s}' % (
                info['label'], len(mem), latex_poly(info['chi']),
                info['type'] or '', '; '.join(r for _, r in info['remarks']))
            W(head)
            W(r'\begin{posetrow}')
            W('\n\\posetsep\n'.join(tikz(P, tag_for(P, info)) for P in mem))
            W(r'\end{posetrow}')
            W('')
    # n = 6 table
    W(r'\subsection{Connected posets with six elements}')
    W(r'\label{app:six}')
    infos = data[6]
    for k, info in enumerate(infos, 1):
        info['label'] = {'alpha': r'$\alpha$', 'beta': r'$\beta$'}.get(info['special'], '6.%d' % k)
    same = {}
    for info in infos: same.setdefault(tuple(info['chi']), []).append(info['label'])
    dup = [v for v in same.values() if len(v) > 1]
    pair = [v for v in dup if r'\alpha' not in ''.join(v)][0]
    snf = {}
    for info in infos:
        if info['label'] in pair: snf[info['label']] = smith_cc(info['members'][0])
    W(r'Table~\ref{tab:app-six} lists the $23$ classes of the $238$ connected posets with six elements, '
      r'with one representative each; when a class contains the orientations of a tree, the '
      r'representative is one of them. Two pairs of rows have the same Coxeter polynomial. The classes '
      r'%s and %s are separated by the Smith normal form of $C_P+C_P^{T}$ '
      r'(Section~\ref{Derived invariants and the census}), which is $\operatorname{diag}(%s)$ and '
      r'$\operatorname{diag}(%s)$, respectively. The classes $\alpha$ and $\beta$ of '
      r'Section~\ref{the case of six elements} are not separated by any of our invariants.'
      % (pair[0], pair[1], ','.join(map(str, snf[pair[0]])), ','.join(map(str, snf[pair[1]]))))
    W('')
    W(r'{\setlength{\tabcolsep}{4pt}')
    W(r'\begin{longtable}{c c c >{$}l<{$} c >{\raggedright\arraybackslash}p{2.9cm}}')
    W(r'\caption{The $\sim_L$-classes of connected posets with six elements.}\label{tab:app-six}\\')
    W(r'\toprule class & representative & size & \chi_P(t) & type & remarks \\ \midrule \endfirsthead')
    W(r'\toprule class & representative & size & \chi_P(t) & type & remarks \\ \midrule \endhead')
    W(r'\bottomrule \endfoot')
    for info in infos:
        rep = representative(info)
        rem = '; '.join(r for _, r in info['remarks'])
        if info['special'] == 'alpha': rem = r'$P_\alpha$ of Section~\ref{the case of six elements}'
        if info['special'] == 'beta': rem = r'$P_\beta$ of Section~\ref{the case of six elements}'
        W(r'%s & %s & %d & %s & %s & %s \\[2pt]' % (
            info['label'], tikz(rep, '', baseline='center'), len(info['members']),
            latex_poly(info['chi']), info['type'] or '--', rem))
    W(r'\end{longtable}}')
    W(FOOTER)
    bad = [(len(P), c) for P, c in LAYOUT_COST.items() if c >= 100]
    sys.stderr.write('drawings with crossings or collisions (n, cost): %s\n' % sorted(bad))
    print('\n'.join(out))
    return data

if __name__ == '__main__':
    main()
