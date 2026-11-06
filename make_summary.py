"""
make_summary.py -- collects the summaries of census.py, closure.py, residual.py
into results/summary_n1-NMAX.json and prints the census table
(Table 1 of the paper: connected posets, ~_L-classes, computed invariant
signatures), together with some further counts.

usage: python3 make_summary.py [NMAX]      (default 9)
"""

import json
import os
import sys


def main(nmax):
    out = {}
    for n in range(1, nmax + 1):
        with open("census_n%d.json" % n) as f:
            c = json.load(f)["summary"]
        with open("closure_n%d.json" % n) as f:
            cl = json.load(f)["report"]
        with open("residual_n%d.json" % n) as f:
            r = json.load(f)["report"]
        out[n] = {"census": c, "closure": cl, "residual": r}
    os.makedirs("results", exist_ok=True)
    with open("results/summary_n1-%d.json" % nmax, "w") as f:
        json.dump(out, f, indent=1)

    print("| n | posets | connected | ideals != 0,P | admissible cuts | effective | "
          "Aut-orbits | ~_L classes (connected) | invariant classes (connected) |")
    print("|---|---|---|---|---|---|---|---|---|")
    for n in range(3, nmax + 1):
        c, cl, r = out[n]["census"], out[n]["closure"], out[n]["residual"]
        print("| %d | %d | %d | %d | %d | %d | %d | %d | %d |" % (
            n, c["posets"], c["connected_posets"], c["nontrivial_ideals"],
            c["admissible_cuts"], c["effective_cuts"], c["effective_aut_orbits"],
            cl["classes_L"], r["refined_invariant_classes"]))
    print()
    print("further counts, by n:")
    for n in range(4, nmax + 1):
        c, cl, r = out[n]["census"], out[n]["closure"], out[n]["residual"]
        print("  n = %d: classes L/LP/LPS = %d/%d/%d; lex-sum merges = %d; "
              "not in class of opposite (L, LPS) = %d, %d; isolated connected = %d; "
              "distinct outputs = %d; torsion posets = %d; undecided groups = %d "
              "(%d classes, %d posets)" % (
                  n, cl["classes_L"], cl["classes_LP"], cl["classes_LPS"],
                  cl["lex_pairs_joining_new_classes"], cl["op_not_in_class_L"],
                  cl["op_not_in_class_LPS"], c["isolated_connected_posets"],
                  c["distinct_outputs_total"], r["torsion_posets"],
                  r["refined_classes_with_several_LPS_classes"],
                  r["LPS_classes_involved_in_undecided"],
                  r["posets_involved_in_undecided"]))


if __name__ == "__main__":
    main(int(sys.argv[1]) if len(sys.argv) > 1 else 9)
