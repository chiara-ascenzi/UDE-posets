"""
tests.py -- validation of the implementation against the paper.

  T1  Example 3.7   (Tamari lattice T3 -> orientation of D5)
  T2  a partition satisfying conditions (a), (b) but not (c) of
      Definition 3.1 (the candidate negative relation is not transitive)
  T3  Example 3.9 / Corollary 3.8 (height <= 1: P^- = P^op), all posets
  T4  Proposition 4.1 / Corollary 4.2 (source-clicks), all posets
  T5  Proposition 3.4 (reconstruction), every admissible cut
  T6  Corollary 3.11 and the remark before it (cardinalities of M(a))
  T7  Theorem 3.2 by brute force over ALL partitions and ALL families
      (independent of the proof: only Ladkani's definitions are used)
  T8  canonical forms are invariant under random relabelling

usage: python3 tests.py NMAX NBRUTE
  (T3-T6 and T8 on all posets with at most NMAX elements,
   T7 on all posets with at most NBRUTE elements)
"""

import random
import sys
import time
from itertools import product

from admissible_cuts import (Poset, bit, members, popcount, to_mask, ideals,
                             check_cut, negative_poset, admissible_cuts,
                             reconstruct_from_negative, ladkani_hypotheses,
                             ladkani_positive_up, is_ideal)
from canonical import all_posets, canonical_forms

NMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 6
NBRUTE = int(sys.argv[2]) if len(sys.argv) > 2 else 5


def ok(msg):
    print("  [ok] " + msg)


# ----------------------------------------------------------------------------
def test_tamari():
    # labels 1..5 of the paper -> 0..4 ; T3: 1<2<4<5, 1<3<5
    lab = {1: 0, 2: 1, 3: 2, 4: 3, 5: 4}
    rel = [(1, 2), (2, 4), (4, 5), (1, 3), (3, 5)]
    T3 = Poset.from_relations(5, [(lab[x], lab[y]) for x, y in rel])
    A = to_mask([lab[i] for i in (1, 2, 3, 4)])
    good, why, M = check_cut(T3, A)
    assert good, why
    assert all(M[a] == bit(lab[5]) for a in members(A))
    Tm = negative_poset(T3, A, M)
    inv = {v: k for k, v in lab.items()}
    covers = sorted((inv[x], inv[y]) for x, y in Tm.covers())
    assert covers == [(1, 2), (1, 3), (2, 4), (5, 1)], covers
    assert Tm.hasse_is_tree() and not T3.hasse_is_tree()
    degrees = sorted(sum(1 for c in Tm.covers() if v in c) for v in range(5))
    assert degrees == [1, 1, 1, 2, 3]          # D5: one branch vertex
    ok("Example 3.7: T3 = A|_|B admissible, M(a)={5}, T3^- is an orientation of D5")


def test_remark_c():
    # B = {u,v,w} with v<w ; A = {a<a'} ; a<u, a<v, a'<w
    a, a2, u, v, w = range(5)
    P = Poset.from_relations(5, [(v, w), (a, a2), (a, u), (a, v), (a2, w)])
    A = to_mask([a, a2])
    good, why, M = check_cut(P, A)
    assert not good and why == "(c)", why
    assert M[a] == to_mask([u, v]) and M[a2] == to_mask([w])
    # the candidate negative relation is not transitive
    try:
        negative_poset(P, A, M)
        raise AssertionError("expected a non-transitive relation")
    except ValueError:
        pass
    ok("(a),(b) hold, (c) fails; the candidate P^- is not a partial order")


def test_example_3_9():
    a1, a2, b1, b2, b3 = range(5)
    P = Poset.from_relations(5, [(a1, b1), (a1, b2), (a1, b3), (a2, b1), (a2, b2)])
    A = to_mask([a1, a2])
    good, why, M = check_cut(P, A)
    assert good
    assert M[a1] == to_mask([b1, b2, b3]) and M[a2] == to_mask([b1, b2])
    assert negative_poset(P, A, M) == P.op()
    ok("Example 3.9: M(a1)={b1,b2,b3}, M(a2)={b1,b2}, P^- = P^op")


def test_height_one(posets_by_n):
    count = 0
    for n, Ps in posets_by_n.items():
        for P in Ps:
            if P.height() > 1:
                continue
            A = to_mask(P.minimal())
            good, why, M = check_cut(P, A)
            assert good, (P, why)
            assert negative_poset(P, A, M) == P.op()
            count += 1
    ok("Corollary 3.8 on all %d posets of height <= 1 with n <= %d" % (count, NMAX))


def source_click(P, s):
    """Reverse the covering relations s < m and take the transitive closure."""
    pairs = []
    for x, y in P.covers():
        if x == s:
            pairs.append((y, s))
        else:
            pairs.append((x, y))
    return Poset.from_relations(P.n, pairs)


def test_source_clicks(posets_by_n):
    n_adm = n_tot = 0
    for n, Ps in posets_by_n.items():
        for P in Ps:
            for s in P.minimal():
                if n == 1:
                    continue
                n_tot += 1
                A = bit(s)
                good, why, M = check_cut(P, A)
                cov = to_mask([y for x, y in P.covers() if x == s])
                assert M[s] == cov                         # M(s) = Cov_P(s)
                ms = list(members(cov))
                sep = all(not (P.up[m1] & P.up[m2] & ~A) and
                          not (P.down[m1] & P.down[m2] & ~A)
                          for i, m1 in enumerate(ms) for m2 in ms[i + 1:])
                assert good == sep                          # criterion (ii)
                if good:
                    n_adm += 1
                    assert negative_poset(P, A, M) == source_click(P, s)
                if P.hasse_is_tree():
                    assert good                             # Corollary 4.2
    ok("Proposition 4.1 / Corollary 4.2 on %d (poset, source) pairs, %d admissible"
       % (n_tot, n_adm))


def test_reconstruction_and_cardinalities(posets_by_n):
    ncuts = 0
    for n, Ps in posets_by_n.items():
        for P in Ps:
            has_top = any(P.down[x] == P.full() for x in range(n))
            for c in admissible_cuts(P):
                ncuts += 1
                Prec, Mrec = reconstruct_from_negative(c.Pminus, c.A)
                assert Prec == P and Mrec == c.M                  # Prop. 3.4
                if has_top:
                    assert c.is_singleton_type()                  # Cor. 3.11
                for a in members(c.A):                            # |M(a)| = |M(a')|
                    for a2 in members(P.up[a] & c.A):
                        assert popcount(c.M[a]) == popcount(c.M[a2])
    ok("Proposition 3.4, Corollary 3.11 and |M(a)| = |M(a')| for a <= a' on all %d "
       "nontrivial admissible cuts with n <= %d" % (ncuts, NMAX))


def test_theorem_3_2_bruteforce(posets_by_n):
    """For every partition A|_|B (not only ideals) and every family (Y_a) of
    subsets of B: Ladkani's hypotheses + P = (A|_|B)^+_Y  <=>  admissible,
    and then Y = M."""
    checked_parts = checked_fams = 0
    for n, Ps in posets_by_n.items():
        if n > NBRUTE:
            continue
        for P in Ps:
            full = P.full()
            for A in range(1, full):
                B = full & ~A
                As = list(members(A))
                Bsubsets = [S for S in range(full + 1) if S & ~B == 0]
                valid = []
                for choice in product(Bsubsets, repeat=len(As)):
                    fam = dict(zip(As, choice))
                    checked_fams += 1
                    if not ladkani_hypotheses(P, A, B, fam):
                        continue
                    if ladkani_positive_up(P, A, B, fam) == P.up:
                        valid.append(fam)
                good, why, M = check_cut(P, A)
                assert good == (len(valid) > 0), (P, A, why, valid)
                if good:
                    assert valid == [M], (P, A, valid, M)
                checked_parts += 1
    ok("Theorem 3.2 (both directions and uniqueness B_a = M(a)) by brute force: "
       "%d partitions, %d families, n <= %d" % (checked_parts, checked_fams, NBRUTE))


def test_canonical_invariance(posets_by_n):
    rnd = random.Random(1)
    trials = 0
    for n, Ps in posets_by_n.items():
        sample = Ps if len(Ps) < 300 else rnd.sample(Ps, 300)
        relabelled = []
        for P in sample:
            perm = list(range(n))
            rnd.shuffle(perm)
            pairs = [(perm[x], perm[y]) for x, y in P.covers()]
            relabelled.append(Poset.from_relations(n, pairs))
        assert canonical_forms(sample) == canonical_forms(relabelled)
        trials += len(sample)
    ok("canonical forms invariant under %d random relabellings" % trials)


if __name__ == "__main__":
    t0 = time.time()
    posets_by_n = {n: all_posets(n) for n in range(1, NMAX + 1)}
    print("posets loaded:", {n: len(v) for n, v in posets_by_n.items()})
    test_tamari()
    test_remark_c()
    test_example_3_9()
    test_height_one(posets_by_n)
    test_source_clicks(posets_by_n)
    test_reconstruction_and_cardinalities(posets_by_n)
    test_canonical_invariance(posets_by_n)
    test_theorem_3_2_bruteforce(posets_by_n)
    print("all tests passed in %.1f s" % (time.time() - t0))
