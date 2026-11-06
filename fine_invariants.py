"""
fine_invariants.py -- refined derived invariants for posets with equal
Coxeter polynomial and Betti numbers, and a torsion check.

Derived equivalence over a field k gives an isometry of Grothendieck groups
for the Euler form, so the incidence matrices C_P, C_Q are Z-congruent
(Ladkani, math/0610685).  Invariants of the Z-congruence class of C used here:
  * Smith normal form of C + C^T and of C - C^T;
  * the Z-conjugacy class of Phi = -C^{-T} C, through the Smith normal forms
    of Phi - I, Phi + I, Phi^2 + I, Phi^2 + Phi + I, Phi^2 - Phi + I
    and the rational Jordan data (ranks of f(Phi)^j, f | charpoly).
Betti numbers of Delta(P) over k are field independent when H_*(Delta(P); Z)
is torsion free; torsion is checked through Smith normal forms of the
boundary maps of Delta(core(P)).
"""

from fractions import Fraction
import sympy as sp

from admissible_cuts import Poset
from invariants import cartan, mobius_matrix, core, chains


# ----------------------------------------------------------------------------
# integer linear algebra
# ----------------------------------------------------------------------------

def smith_diagonal(M):
    """Invariant factors of an integer matrix (list of positive ints; zeros
    for the rank deficiency), computed by elementary operations."""
    A = [list(r) for r in M]
    m = len(A)
    n = len(A[0]) if m else 0
    diag = []
    r0 = 0
    while r0 < min(m, n):
        # find smallest nonzero entry in the remaining block
        best = None
        for i in range(r0, m):
            for j in range(r0, n):
                if A[i][j] and (best is None or abs(A[i][j]) < abs(A[best[0]][best[1]])):
                    best = (i, j)
        if best is None:
            break
        i, j = best
        A[r0], A[i] = A[i], A[r0]
        for row in A:
            row[r0], row[j] = row[j], row[r0]
        while True:
            p = A[r0][r0]
            done = True
            for i in range(r0 + 1, m):
                q = A[i][r0] // p
                if q:
                    A[i] = [a - q * b for a, b in zip(A[i], A[r0])]
                if A[i][r0]:
                    done = False
            for j in range(r0 + 1, n):
                q = A[r0][j] // p
                if q:
                    for row in A:
                        row[j] -= q * row[r0]
                if A[r0][j]:
                    done = False
            if done:
                # divisibility condition on the rest of the block
                bad = None
                for i in range(r0 + 1, m):
                    for j in range(r0 + 1, n):
                        if A[i][j] % p:
                            bad = i
                            break
                    if bad is not None:
                        break
                if bad is None:
                    break
                A[r0] = [a + b for a, b in zip(A[r0], A[bad])]
                continue
            # move the smallest nonzero entry of row/col r0 to the pivot
            best = (r0, r0)
            for i in range(r0, m):
                if A[i][r0] and abs(A[i][r0]) < abs(A[best[0]][best[1]]):
                    best = (i, r0)
            for j in range(r0, n):
                if A[r0][j] and abs(A[r0][j]) < abs(A[best[0]][best[1]]):
                    best = (r0, j)
            i, j = best
            A[r0], A[i] = A[i], A[r0]
            for row in A:
                row[r0], row[j] = row[j], row[r0]
        diag.append(abs(A[r0][r0]))
        r0 += 1
    diag += [0] * (min(m, n) - len(diag))
    return tuple(diag)


def matmul(A, B):
    n, k, m = len(A), len(B), len(B[0])
    return [[sum(A[i][l] * B[l][j] for l in range(k)) for j in range(m)] for i in range(n)]


def matadd(A, B, c=1):
    return [[a + c * b for a, b in zip(ra, rb)] for ra, rb in zip(A, B)]


def eye(n):
    return [[1 if i == j else 0 for j in range(n)] for i in range(n)]


def rank_Q(M):
    rows = [[Fraction(v) for v in r] for r in M]
    rank = 0
    ncols = len(rows[0]) if rows else 0
    for col in range(ncols):
        piv = next((i for i in range(rank, len(rows)) if rows[i][col] != 0), None)
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


# ----------------------------------------------------------------------------
_factor_cache = {}


def coxeter_matrix(P):
    n = P.n
    C = cartan(P)
    Ci = mobius_matrix(P)
    Phi = [[-sum(Ci[l][i] * C[l][j] for l in range(n)) for j in range(n)]
           for i in range(n)]
    return C, Phi


def poly_of_matrix(coeffs, M):
    """coeffs = [a_d, ..., a_0] -> a_d M^d + ... + a_0 I (Horner)."""
    n = len(M)
    R = [[0] * n for _ in range(n)]
    for c in coeffs:
        R = matadd(matmul(R, M), eye(n), c)
    return R


def fine_invariants(P, coxeter_coeffs):
    n = P.n
    C, Phi = coxeter_matrix(P)
    CT = [list(r) for r in zip(*C)]
    I = eye(n)
    key = tuple(coxeter_coeffs)
    if key not in _factor_cache:
        t = sp.symbols("t")
        poly = sum(c * t ** (len(key) - 1 - i) for i, c in enumerate(key))
        _factor_cache[key] = [(tuple(int(a) for a in sp.Poly(f, t).all_coeffs()), e)
                              for f, e in sp.factor_list(poly)[1]]
    jordan = []
    for f, e in _factor_cache[key]:
        fPhi = poly_of_matrix(list(f), Phi)
        ranks = []
        Pk = eye(n)
        for _ in range(e):
            Pk = matmul(Pk, fPhi)
            ranks.append(rank_Q(Pk))
        jordan.append((f, e, tuple(ranks)))
    snfs = {
        "C+CT": smith_diagonal(matadd(C, CT)),
        "C-CT": smith_diagonal(matadd(C, CT, -1)),
    }
    for name, f in (("Phi-I", [1, -1]), ("Phi+I", [1, 1]), ("Phi^2+I", [1, 0, 1]),
                    ("Phi^2+Phi+I", [1, 1, 1]), ("Phi^2-Phi+I", [1, -1, 1])):
        snfs[name] = smith_diagonal(poly_of_matrix(f, Phi))
    return (tuple(sorted(jordan)), tuple(sorted(snfs.items())))


def integral_homology_torsion(P):
    """Torsion coefficients of H_*(Delta(P); Z) (empty tuple if torsion free)."""
    el = core(P)
    if len(el) <= 1:
        return ()
    ch = chains(P, el)
    top = max(ch)
    index = {k: {c: i for i, c in enumerate(ch[k])} for k in ch}
    tors = []
    for k in range(2, top + 1):
        rows = []
        for c in ch[k]:
            row = [0] * len(ch[k - 1])
            for i in range(k):
                row[index[k - 1][c[:i] + c[i + 1:]]] += (-1) ** i
            rows.append(row)
        tors += [d for d in smith_diagonal(rows) if d > 1]
    return tuple(tors)
