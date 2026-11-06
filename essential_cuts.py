"""
essential_cuts.py -- admissible cuts that join two classes which are NOT joined
by one-point moves (|A| = 1 or |B| = 1) or flip-flops (singleton type).

For n = 5 it prints the two cuts behind the row n = 5 of Table 2 of the paper
(8 classes with one-point cuts and flip-flops together, 6 with all cuts),
among them the cut of Corollary 3.8 relating the complete bipartite posets
with three minimal elements below two maximal ones and with two minimal
elements below three maximal ones (Section 5.4).

usage: python3 essential_cuts.py N
"""

import sys

from admissible_cuts import ideals, check_cut, negative_poset, popcount, to_set
from canonical import all_posets, canonical_strings, poset_to_d6
from census import UnionFind


def main(n):
    Ps = all_posets(n)
    N = len(Ps)
    canon = canonical_strings([poset_to_d6(P) for P in Ps])
    idx = {c: i for i, c in enumerate(canon)}
    rows = []
    for i, P in enumerate(Ps):
        full = P.full()
        for A in ideals(P):
            if A in (0, full):
                continue
            good, _, M = check_cut(P, A)
            if not good or all(v == 0 for v in M.values()):
                continue
            single = all(popcount(v) == 1 for v in M.values())
            click = popcount(A) == 1 or popcount(full & ~A) == 1
            rows.append((i, A, M, single, click, poset_to_d6(negative_poset(P, A, M))))
    tg = canonical_strings([r[5] for r in rows])
    uf = UnionFind(N)
    for (i, A, M, single, click, _), c in zip(rows, tg):
        if single or click:
            uf.union(i, idx[c])
    seen = set()
    for (i, A, M, single, click, _), c in zip(rows, tg):
        j = idx[c]
        if (single or click) or uf.find(i) == uf.find(j):
            continue
        key = (min(uf.find(i), uf.find(j)), max(uf.find(i), uf.find(j)))
        if key in seen:
            continue
        seen.add(key)
        P = Ps[i]
        print("P=#%d covers %s" % (i, P.covers()))
        print("   A=%s B=%s  M=%s" % (sorted(to_set(A)), sorted(to_set(P.full() & ~A)),
                                     {a: sorted(to_set(v)) for a, v in M.items()}))
        print("   P^- =#%d covers %s" % (j, negative_poset(P, A, M).covers()))
        print("   merges click/flip-flop classes of sizes",
              sum(1 for x in range(N) if uf.find(x) == uf.find(i)),
              sum(1 for x in range(N) if uf.find(x) == uf.find(j)))


if __name__ == "__main__":
    main(int(sys.argv[1]))
