"""
residual.py -- what remains undecided after known constructions and invariants.

For connected posets with n points:
  * checks that H_*(Delta(P); Z) is torsion free (so Betti numbers are
    field independent);
  * refines the (Coxeter polynomial, Betti numbers) classes by the invariants
    of fine_invariants.py, computed on representatives of the classes of the
    closure LPS (checking agreement on a second member when available);
  * reports the refined invariant classes that still contain more than one
    LPS class ('undecided'), and those containing exactly one ('complete').

usage: python3 residual.py NMAX
"""

import json
import sys
from collections import defaultdict

from admissible_cuts import Poset
from fine_invariants import fine_invariants, integral_homology_torsion


def main(nmax):
    out = {}
    for n in range(1, nmax + 1):
        det = json.load(open("census_n%d.json" % n))["detail"]
        lab = json.load(open("closure_n%d.json" % n))
        LPS = lab["label_LPS"]
        N = len(det["covers"])
        conn = [i for i in range(N) if det["connected"][i]]
        Ps = {i: Poset.from_relations(n, [tuple(c) for c in det["covers"][i]]) for i in conn}
        torsion = [i for i in conn if integral_homology_torsion(Ps[i])]
        # representatives of LPS classes
        members = defaultdict(list)
        for i in conn:
            members[LPS[i]].append(i)
        fine = {}
        mismatch = 0
        for c, mem in members.items():
            f0 = fine_invariants(Ps[mem[0]], det["cox"][mem[0]])
            if len(mem) > 1:
                f1 = fine_invariants(Ps[mem[-1]], det["cox"][mem[-1]])
                if f1 != f0:
                    mismatch += 1
            fine[c] = f0
        refined = defaultdict(set)
        coarse = defaultdict(set)
        for c, mem in members.items():
            i = mem[0]
            base = (tuple(det["cox"][i]), tuple(det["betti"][i]))
            coarse[base].add(c)
            refined[(base, fine[c])].add(c)
        undecided = [(k, sorted(v)) for k, v in refined.items() if len(v) > 1]
        rep = {
            "n": n,
            "connected": len(conn),
            "torsion_posets": len(torsion),
            "fine_invariant_mismatch_within_class": mismatch,
            "classes_LPS": len(members),
            "coxeter_betti_classes": len(coarse),
            "refined_invariant_classes": len(refined),
            "refined_classes_with_several_LPS_classes": len(undecided),
            "LPS_classes_involved_in_undecided": sum(len(v) for _, v in undecided),
            "posets_involved_in_undecided": sum(len(members[c]) for _, v in undecided for c in v),
        }
        print(json.dumps(rep))
        sys.stdout.flush()
        out[n] = {"report": rep,
                  "undecided": [{"coxeter": list(k[0][0]), "betti": list(k[0][1]),
                                 "classes": [{"size": len(members[c]),
                                              "rep_covers": det["covers"][members[c][0]],
                                              "members": members[c]} for c in v]}
                                for k, v in undecided]}
        with open("residual_n%d.json" % n, "w") as f:
            json.dump(out[n], f)
    return out


if __name__ == "__main__":
    main(int(sys.argv[1]))
