"""Similarity class of Phi modulo primes p (Ladkani, math/0610685, Cor. 3.15:
derived equivalent posets have Coxeter-type matrices similar over Z, hence mod p).
Invariant: for each monic irreducible factor f of charpoly mod p with multiplicity e,
the ranks over F_p of f(Phi)^k, k = 1..e."""
import sympy as sp
from fine_invariants import coxeter_matrix, matmul, eye

t = sp.symbols('t')

def rank_mod_p(M, p):
    rows = [[v % p for v in r] for r in M]
    rank = 0; ncols = len(rows[0])
    for col in range(ncols):
        piv = next((i for i in range(rank, len(rows)) if rows[i][col]), None)
        if piv is None: continue
        rows[rank], rows[piv] = rows[piv], rows[rank]
        inv = pow(rows[rank][col], p - 2, p)
        rows[rank] = [(v * inv) % p for v in rows[rank]]
        for i in range(len(rows)):
            if i != rank and rows[i][col]:
                f = rows[i][col]
                rows[i] = [(a - f * b) % p for a, b in zip(rows[i], rows[rank])]
        rank += 1
    return rank

def poly_eval_mod(coeffs, M, p):
    n = len(M); R = [[0]*n for _ in range(n)]
    for c in coeffs:
        R = matmul(R, M)
        for i in range(n): R[i][i] += c
        R = [[v % p for v in r] for r in R]
    return R

_cache = {}
def similarity_invariant(P, cox, p):
    C, Phi = coxeter_matrix(P)
    key = (tuple(cox), p)
    if key not in _cache:
        poly = sp.Poly(list(cox), t, modulus=p)
        _cache[key] = [(tuple(int(c) % p for c in f.all_coeffs()), e) for f, e in poly.factor_list()[1]]
    inv = []
    for f, e in _cache[key]:
        fPhi = poly_eval_mod(list(f), Phi, p)
        Pk = eye(len(Phi)); ranks = []
        for _ in range(e):
            Pk = [[v % p for v in r] for r in matmul(Pk, fPhi)]
            ranks.append(rank_mod_p(Pk, p))
        inv.append((f, e, tuple(ranks)))
    return tuple(sorted(inv))

PRIMES = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47]

def modp_invariants(P, cox):
    return tuple(similarity_invariant(P, cox, p) for p in PRIMES)

if __name__ == "__main__":
    import json, sys
    from admissible_cuts import Poset
    for n in map(int, sys.argv[1:]):
        det = json.load(open('census_n%d.json' % n))['detail']
        res = json.load(open('residual_n%d.json' % n))
        still = 0; resolved = 0; groups_left = []
        for g in res['undecided']:
            keys = {}
            for cl in g['classes']:
                i = cl['members'][0]
                P = Poset.from_relations(n, [tuple(c) for c in det['covers'][i]])
                k = modp_invariants(P, det['cox'][i])
                # sanity: another member gives the same invariant
                if len(cl['members']) > 1:
                    j = cl['members'][-1]
                    Q = Poset.from_relations(n, [tuple(c) for c in det['covers'][j]])
                    assert modp_invariants(Q, det['cox'][j]) == k
                keys.setdefault(k, []).append(cl)
            sub = [v for v in keys.values() if len(v) > 1]
            if sub: groups_left.extend(sub)
            still += len(sub)
            resolved += (len(g['classes']) - sum(len(v) for v in sub))
        print(json.dumps({"n": n, "undecided_groups_before": len(res['undecided']),
               "undecided_groups_after_modp": len(groups_left),
               "classes_in_undecided_after": sum(len(v) for v in groups_left),
               "posets_in_undecided_after": sum(cl['size'] for v in groups_left for cl in v)}))
        json.dump([[{"size": cl['size'], "rep_covers": cl['rep_covers'], "members": cl['members']} for cl in v] for v in groups_left],
                  open('undecided_modp_n%d.json' % n, 'w'))
