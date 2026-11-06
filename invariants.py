"""
invariants.py -- derived invariants of incidence algebras of finite posets.

If P and Q are universally derived equivalent then, for every field k,
kP and kQ are derived equivalent; hence the following are UDE invariants:

  * the Coxeter polynomial: characteristic polynomial of
        Phi = -C^{-T} C,   C_{xy} = 1 if x <= y else 0
    (all usual conventions give the same polynomial);
  * the Betti numbers of the order complex Delta(P) over k, since
    HH^*(kP) = H^*(Delta(P); k)  (Gerstenhaber-Schack) and Hochschild
    cohomology is a derived invariant.

Betti numbers are computed after removing beat points (Stong): this does
not change the homotopy type of Delta(P).
"""

from fractions import Fraction

from admissible_cuts import Poset, bit, members, popcount


# ----------------------------------------------------------------------------
# Coxeter polynomial
# ----------------------------------------------------------------------------

def cartan(P):
    return [[1 if P.leq(x, y) else 0 for y in range(P.n)] for x in range(P.n)]


def mobius_matrix(P):
    """Inverse of the zeta matrix C (integer matrix)."""
    n = P.n
    order = P.linear_extension()
    mu = [[0] * n for _ in range(n)]
    for x in range(n):
        mu[x][x] = 1
        # mu(x, y) = - sum_{x <= z < y} mu(x, z), for y > x, increasing y
        for y in order:
            if y != x and P.leq(x, y):
                s = 0
                for z in members(P.up[x] & P.down[y] & ~bit(y)):
                    s += mu[x][z]
                mu[x][y] = -s
    return mu


def charpoly_int(M):
    """Characteristic polynomial det(tI - M) of an integer matrix,
    Faddeev-LeVerrier with exact integer arithmetic.
    Returns coefficients [c_n=1, c_{n-1}, ..., c_0]."""
    n = len(M)
    coeffs = [1]
    Mk = [[0] * n for _ in range(n)]            # M_0 = 0
    c = 1
    for k in range(1, n + 1):
        # M_k = M * M_{k-1} + c_{n-k+1} I
        prod = [[sum(M[i][l] * Mk[l][j] for l in range(n)) for j in range(n)]
                for i in range(n)]
        for i in range(n):
            prod[i][i] += c
        Mk = prod
        AM = [[sum(M[i][l] * Mk[l][j] for l in range(n)) for j in range(n)]
              for i in range(n)]
        tr = sum(AM[i][i] for i in range(n))
        assert tr % k == 0
        c = -tr // k
        coeffs.append(c)
    return coeffs


def coxeter_polynomial(P):
    n = P.n
    if n == 0:
        return (1,)
    C = cartan(P)
    Ci = mobius_matrix(P)
    # -C^{-T} C
    Phi = [[-sum(Ci[l][i] * C[l][j] for l in range(n)) for j in range(n)]
           for i in range(n)]
    return tuple(charpoly_int(Phi))


# ----------------------------------------------------------------------------
# Betti numbers of the order complex
# ----------------------------------------------------------------------------

def core(P):
    """Remove beat points until none is left (Stong's core).
    Returns the list of remaining elements (original labels)."""
    alive = P.full()
    changed = True
    while changed:
        changed = False
        for x in members(alive):
            above = P.up[x] & alive & ~bit(x)
            below = P.down[x] & alive & ~bit(x)
            # up beat point: 'above' has a minimum
            if above and any(P.up[m] & above == above for m in members(above)):
                alive &= ~bit(x)
                changed = True
                break
            # down beat point: 'below' has a maximum
            if below and any(P.down[m] & below == below for m in members(below)):
                alive &= ~bit(x)
                changed = True
                break
    return list(members(alive))


def chains(P, elements):
    """All nonempty chains of the subposet on `elements`, grouped by size."""
    el = set(elements)
    order = [x for x in P.linear_extension() if x in el]
    pos = {x: i for i, x in enumerate(order)}
    res = {}

    def extend(ch):
        res.setdefault(len(ch), []).append(tuple(ch))
        last = ch[-1]
        for y in order[pos[last] + 1:]:
            if P.lt(last, y):
                ch.append(y)
                extend(ch)
                ch.pop()

    for x in order:
        extend([x])
    return res


def rank_mod_p(rows, p):
    rows = [r[:] for r in rows]
    rank = 0
    ncols = len(rows[0]) if rows else 0
    col = 0
    for col in range(ncols):
        piv = None
        for i in range(rank, len(rows)):
            if rows[i][col] % p:
                piv = i
                break
        if piv is None:
            continue
        rows[rank], rows[piv] = rows[piv], rows[rank]
        inv = pow(rows[rank][col], p - 2, p) if p > 2 else 1
        rows[rank] = [(v * inv) % p for v in rows[rank]]
        for i in range(len(rows)):
            if i != rank and rows[i][col] % p:
                f = rows[i][col]
                rows[i] = [(a - f * b) % p for a, b in zip(rows[i], rows[rank])]
        rank += 1
    return rank


def rank_rational(rows):
    rows = [[Fraction(v) for v in r] for r in rows]
    rank = 0
    ncols = len(rows[0]) if rows else 0
    for col in range(ncols):
        piv = None
        for i in range(rank, len(rows)):
            if rows[i][col] != 0:
                piv = i
                break
        if piv is None:
            continue
        rows[rank], rows[piv] = rows[piv], rows[rank]
        pv = rows[rank][col]
        rows[rank] = [v / pv for v in rows[rank]]
        for i in range(len(rows)):
            if i != rank and rows[i][col] != 0:
                f = rows[i][col]
                rows[i] = [a - f * b for a, b in zip(rows[i], rows[rank])]
        rank += 1
    return rank


def betti_numbers(P, field="Q"):
    """Betti numbers (b_0, b_1, ...) of Delta(P) over Q or GF(p) ('GF2')."""
    el = core(P)
    if len(el) <= 1:
        return (1,) if P.n else ()
    ch = chains(P, el)
    top = max(ch)
    index = {k: {c: i for i, c in enumerate(ch[k])} for k in ch}
    ranks = {}
    for k in range(2, top + 1):
        # boundary: chains of size k -> chains of size k-1
        rows = []
        for c in ch[k]:
            row = [0] * len(ch[k - 1])
            for i in range(k):
                face = c[:i] + c[i + 1:]
                row[index[k - 1][face]] += (-1) ** i
            rows.append(row)
        if field == "Q":
            ranks[k] = rank_rational(rows)
        elif field == "GF2":
            ranks[k] = rank_mod_p(rows, 2)
        else:
            raise ValueError(field)
    betti = []
    for k in range(1, top + 1):
        b = len(ch[k]) - ranks.get(k, 0) - ranks.get(k + 1, 0)
        betti.append(b)
    while len(betti) > 1 and betti[-1] == 0:
        betti.pop()
    return tuple(betti)
