"""
lex_new.py -- lexicographic sums along connected posets S of height at most one
(Ladkani, math/0610685, Theorem 4.14: the sum along S and the sum along S^op
are derived equivalent over every field) whose two sides are NOT in the same
class of LP (admissible cuts plus products), for n = 8.

Backs Section 5.5 of the paper: at n = 8 there are exactly 2 such pairs of
classes; the smallest example is (Lambda+1)(+)(V+1) versus (V+1)(+)(Lambda+1),
where Lambda is two minimal elements below a maximal one and V is its dual.

Needs census_n1..8.json and closure_n8.json.

usage: python3 lex_new.py
"""

import json
from itertools import product as iproduct

from canonical import canonical_strings, poset_to_d6
from closure import lex_sum, compositions, load


def main(n=8):
    Ps, d = load(n)
    idx = {c: i for i, c in enumerate(d["canon"])}
    with open("closure_n%d.json" % n) as f:
        labLP = json.load(f)["label_LP"]
    data = {k: load(k) for k in range(1, n + 1)}
    found = []
    for k in range(2, n + 1):
        PS, dS = data[k]
        for si, S in enumerate(PS):
            if not dS["connected"][si] or S.height() > 1:
                continue
            Sop = S.op()
            for comp_ in compositions(n, k):
                if all(c == 1 for c in comp_):
                    continue
                lists = [data[c][0] for c in comp_]
                batchP, batchQ, meta = [], [], []
                for choice in iproduct(*lists):
                    batchP.append(lex_sum(S, list(choice)))
                    batchQ.append(lex_sum(Sop, list(choice)))
                    meta.append(choice)
                cP = canonical_strings([poset_to_d6(P) for P in batchP])
                cQ = canonical_strings([poset_to_d6(P) for P in batchQ])
                for a, b, ch in zip(cP, cQ, meta):
                    i, j = idx[a], idx[b]
                    if labLP[i] != labLP[j]:
                        found.append((S.covers(), [X.covers() for X in ch],
                                      [X.n for X in ch], i, j))
    seen = set()
    for S, Xs, sizes, i, j in found:
        key = tuple(sorted((labLP[i], labLP[j])))
        if key in seen:
            continue
        seen.add(key)
        print("S covers", S, " block sizes", sizes, " blocks", Xs, "  -> #%d vs #%d" % (i, j))
    print(len(found), "lex pairs not in the same LP-class;", len(seen), "distinct class pairs")


if __name__ == "__main__":
    main()
