"""
extra_checks.py -- checks of individual statements of the paper.

  * Lemma 3.5 (duality), on all admissible cuts of posets with n <= 7;
  * Section 5.3: for connected posets with six elements, the signature
    (Coxeter polynomial, Betti numbers, SNF(C + C^T)) takes 22 values, and
    exactly one of them occurs in two ~_L-classes, alpha (3 posets) and
    beta (10 posets);
  * Appendix A.2: the classes 6.6 and 6.20 have the same Coxeter polynomial
    and Betti numbers, and SNF(C + C^T) = diag(1,1,1,1,6,0), diag(1,1,1,1,4,0);
  * Example 4.7: the commutative square I2 x I2 is the negative poset of a
    cut of an orientation of D4.

Posets are identified by explicit covering relations (not by genposetg
indices), so the checks do not depend on the numbering.

Requires census_n6.json and closure_n6.json (produced by census.py and
closure.py).

usage: python3 extra_checks.py
"""

import json
from collections import defaultdict

import sympy as sp
from sympy.matrices.normalforms import smith_normal_form

from admissible_cuts import (Poset, admissible_cuts, check_cut, negative_poset,
                             to_mask, popcount)
from canonical import all_posets, canonical_strings, poset_to_d6
from invariants import cartan
from fine_invariants import smith_diagonal, matadd
from closure import product_poset


def canon(P):
    return canonical_strings([poset_to_d6(P)])[0]


def load(n):
    with open("census_n%d.json" % n) as f:
        d = json.load(f)["detail"]
    with open("closure_n%d.json" % n) as f:
        lab = json.load(f)
    idx = {c: i for i, c in enumerate(d["canon"])}
    return d, lab, idx


def poset_of(n, covers):
    return Poset.from_relations(n, covers)


def snf_sym(P):
    C = cartan(P)
    CT = [list(r) for r in zip(*C)]
    return smith_diagonal(matadd(C, CT))


def header(title, claim):
    print("\n=== %s" % title)
    print("    claim: %s" % claim)


# ----------------------------------------------------------------------------
def check_duality(nmax=7):
    header("Lemma 3.5 (duality)",
           "if P = A|_|B is admissible, then (P^-)^op = A|_|B is admissible, "
           "with the same M(a), and its negative poset is P^op")
    cnt = 0
    for n in range(2, nmax + 1):
        for P in all_posets(n):
            for c in admissible_cuts(P):
                Q = c.Pminus.op()
                good, why, M = check_cut(Q, c.A)
                assert good, why
                assert M == c.M
                assert negative_poset(Q, c.A, M) == P.op()
                cnt += 1
    print("    verified on %d admissible cuts (n <= %d)" % (cnt, nmax))


# ----------------------------------------------------------------------------
ALPHA_REP = [(0, 2), (0, 3), (1, 3), (1, 5), (2, 4), (2, 5), (3, 4)]
BETA_REP = [(0, 3), (0, 5), (1, 5), (2, 3), (2, 4), (4, 5)]
CLASS_6_20 = [(0, 2), (0, 5), (1, 2), (1, 3), (1, 4), (3, 5), (4, 5)]
CLASS_6_6 = [(0, 2), (0, 5), (1, 2), (1, 3), (3, 4), (4, 5)]      # orientation of A~_{2,4}


def check_n6_invariants():
    header("Section 5.3 (six elements)",
           "for connected posets with 6 elements, (Coxeter polynomial, Betti numbers, "
           "SNF(C+C^T)) takes 22 values; exactly one of them occurs in two "
           "~_L-classes, namely alpha (3 posets) and beta (10 posets)")
    d, lab, idx = load(6)
    L = lab["label_L"]
    groups = defaultdict(set)
    for i in range(len(L)):
        if not d["connected"][i]:
            continue
        P = poset_of(6, [tuple(c) for c in d["covers"][i]])
        groups[(tuple(d["cox"][i]), tuple(d["betti"][i]), snf_sym(P))].add(L[i])
    split = [v for v in groups.values() if len(v) > 1]
    print("    signatures: %d ; ~_L classes: %d ; signatures with several ~_L classes: %d"
          % (len(groups), len({L[i] for i in range(len(L)) if d['connected'][i]}),
             len(split)))
    assert len(groups) == 22 and len(split) == 1 and len(split[0]) == 2
    a = idx[canon(poset_of(6, ALPHA_REP))]
    b = idx[canon(poset_of(6, BETA_REP))]
    assert split[0] == {L[a], L[b]}
    for name, j in (("alpha", a), ("beta", b)):
        mem = [i for i in range(len(L)) if L[i] == L[j]]
        print("    %s: %d posets, Coxeter %s, Betti %s" %
              (name, len(mem), d["cox"][j], d["betti"][j]))
        for i in mem:
            print("        covers %s" % d["covers"][i])
    assert sum(1 for i in range(len(L)) if L[i] == L[a]) == 3
    assert sum(1 for i in range(len(L)) if L[i] == L[b]) == 10


def check_6_6_versus_6_20():
    header("Appendix A.2: classes 6.6 and 6.20",
           "same Coxeter polynomial (t^4-1)(t^2-1) and Betti numbers, "
           "SNF(C+C^T) = (1,1,1,1,6,0) for 6.6 and (1,1,1,1,4,0) for 6.20")
    d, lab, idx = load(6)
    L = lab["label_L"]
    p = idx[canon(poset_of(6, CLASS_6_20))]
    q = idx[canon(poset_of(6, CLASS_6_6))]
    t = sp.symbols("t")
    for name, j in (("class 6.20", p), ("class 6.6", q)):
        P = poset_of(6, [tuple(c) for c in d["covers"][j]])
        C = sp.Matrix(cartan(P))
        via_sympy = tuple(abs(int(x)) for x in
                          smith_normal_form(C + C.T, domain=sp.ZZ).diagonal())
        cox = sp.factor(sum(c * t ** (len(d["cox"][j]) - 1 - k)
                            for k, c in enumerate(d["cox"][j])))
        print("    %-10s Coxeter %s, Betti %s, SNF (own) %s, SNF (sympy, up to order) %s"
              % (name, cox, d["betti"][j], snf_sym(P), via_sympy))
    assert d["cox"][p] == d["cox"][q] and d["betti"][p] == d["betti"][q]
    assert L[p] != L[q]
    assert snf_sym(poset_of(6, CLASS_6_20)) == (1, 1, 1, 1, 4, 0)
    assert snf_sym(poset_of(6, CLASS_6_6)) == (1, 1, 1, 1, 6, 0)


# ----------------------------------------------------------------------------
def check_D4():
    header("Example 4.7",
           "the orientation 0,1 < 2 < 3 of D4 with A = {0,1,2}, B = {3} is "
           "admissible and P^- is the commutative square I2 x I2")
    P = poset_of(4, [(0, 2), (1, 2), (2, 3)])
    good, why, M = check_cut(P, to_mask([0, 1, 2]))
    assert good
    Pm = negative_poset(P, to_mask([0, 1, 2]), M)
    I2 = poset_of(2, [(0, 1)])
    assert canon(Pm) == canon(product_poset(I2, I2))
    print("    covers of P^-: %s  (isomorphic to I2 x I2)" % Pm.covers())


if __name__ == "__main__":
    check_duality()
    check_n6_invariants()
    check_6_6_versus_6_20()
    check_D4()
    print("\nall extra checks passed")
