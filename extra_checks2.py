"""
extra_checks2.py -- checks of further statements of the paper.

  A. Remark after Proposition 3.12: for ordinal sums of antichains with at
     most NMAX elements, the posets with the same Coxeter polynomial and the
     same Betti numbers b_i, i > 0, are exactly the cyclic rotations of P
     and of P^op (in particular 2+2+2 and 3+3 are alone with six elements).
  C. Example 5.2: the class alpha of Section 5.3 under the restricted kinds
     of cuts of Table 2 (one-point cuts, cuts of singleton type, the cut of
     Corollary 3.8), and the only admissible cut of P_alpha.
  D. Section 5.5 (a): the pair (Lambda+1)(+)(V+1), (V+1)(+)(Lambda+1), n = 8.
  E. Section 5.1: size of the naive search, sum over ideals A of 2^(|A||B|)
     candidate families, versus the number of ideals.
  F. Section 5.5 (b): a poset with eight elements that is derived equivalent
     over every field to an orientation of a tree (Ladkani's lexicographic
     sums) but is alone in its ~_L-class.
  G. The labelled examples of Example 5.2 and Section 5.5 (b), and the
     matrix identities of Section 5.2.

usage: python3 extra_checks2.py [NMAX]
       (NMAX = 9 by default; needs census_n*.json, closure_n*.json and
        residual_n*.json, written by census.py, closure.py, residual.py)
"""

import json
import math
import sys
import time
from collections import defaultdict

from admissible_cuts import (Poset, ideals, check_cut, negative_poset, popcount,
                             members, to_mask)
from canonical import canonical_strings, poset_to_d6
from census import UnionFind
from fine_invariants import fine_invariants
from invariants import coxeter_polynomial, betti_numbers


def detail(n):
    with open("census_n%d.json" % n) as f:
        return json.load(f)["detail"]


def labels(n):
    with open("closure_n%d.json" % n) as f:
        return json.load(f)


def residual(n):
    with open("residual_n%d.json" % n) as f:
        return json.load(f)


def ordinal_sum_of_antichains(sizes):
    rel, levels, off = [], [], 0
    for s in sizes:
        levels.append(list(range(off, off + s)))
        off += s
    for i in range(len(levels) - 1):
        for x in levels[i]:
            for y in levels[i + 1]:
                rel.append((x, y))
    return Poset.from_relations(off, rel)


def compositions(n, minpart=2):
    if n == 0:
        yield ()
        return
    for k in range(minpart, n + 1):
        for rest in compositions(n - k, minpart):
            yield (k,) + rest


def betti_pos(b):
    t = list(b[1:])
    while t and t[-1] == 0:
        t.pop()
    return tuple(t)


def name(sizes):
    return "+".join(str(s) for s in sizes)


# ---------------------------------------------------------------------------
def part_A(nmax):
    print("=== A. Ordinal sums of antichains (Remark after Proposition 3.12)")
    print("    claim: for P = L1+...+Lr with r >= 2, |Li| >= 2 and |P| <= %d, the posets with |P|" % nmax)
    print("    elements (connected or not) that have the Coxeter polynomial of P and its Betti numbers")
    print("    b_i, i > 0, are exactly the cyclic rotations of P and of P^op")
    bad = 0
    for n in range(4, nmax + 1):
        det = detail(n)
        canon, cox, betti = det["canon"], det["cox"], det["betti"]
        idx = {c: i for i, c in enumerate(canon)}
        seen = set()
        for sizes in compositions(n):
            if len(sizes) < 2:
                continue
            rots = [sizes[j:] + sizes[:j] for j in range(len(sizes))]
            if min(rots) in seen:
                continue
            seen.add(min(rots))
            rev = tuple(reversed(sizes))
            rrots = [rev[j:] + rev[:j] for j in range(len(rev))]
            orbit = sorted(set(rots) | set(rrots))
            cs = canonical_strings([poset_to_d6(ordinal_sum_of_antichains(s))
                                    for s in [sizes] + orbit])
            i = idx[cs[0]]
            R = set(idx[c] for c in cs[1:])
            rot_only = set(idx[c] for c, s in zip(cs[1:], orbit) if s in set(rots))
            G1 = set(j for j in range(len(canon))
                     if cox[j] == cox[i] and betti_pos(betti[j]) == betti_pos(betti[i]))
            G2 = set(j for j in G1 if betti[j] == betti[i])
            ok = (G1 == R) and (G2 == R)
            bad += not ok
            print("    n = %d  %-9s rotations of P: %d, of P and P^op: %d; same (chi, b_i>0): %d; "
                  "same (chi, b): %d  %s" % (n, name(sizes), len(rot_only), len(R), len(G1),
                                            len(G2), "ok" if ok else "DIFFERENT"))
    print("    %s" % ("all as claimed" if bad == 0 else "%d exceptions" % bad))
    return bad == 0


# ---------------------------------------------------------------------------
def basic_kind(P, A, M):
    full = P.full()
    single = all(popcount(v) == 1 for v in M.values())
    click = popcount(A) == 1 or popcount(full & ~A) == 1
    height1 = P.height() <= 1 and A == to_mask(P.minimal())
    return single, click, height1


def part_C():
    print("=== C. Example 5.2: the class alpha (n = 6) under the restricted kinds of cuts")
    n = 6
    det, lab = detail(n), labels(n)
    from canonical import all_posets
    Ps = all_posets(n)
    N = len(Ps)
    canon = det["canon"]
    idx = {c: i for i, c in enumerate(canon)}
    assert canonical_strings([poset_to_d6(P) for P in Ps]) == canon
    rows = []
    for i, P in enumerate(Ps):
        full = P.full()
        for A in ideals(P):
            if A in (0, full):
                continue
            good, _, M = check_cut(P, A)
            if not good or all(v == 0 for v in M.values()):
                continue
            rows.append((i, A, M, basic_kind(P, A, M), poset_to_d6(negative_poset(P, A, M))))
    tg = canonical_strings([r[4] for r in rows])
    ub, ua = UnionFind(N), UnionFind(N)
    for (i, A, M, kind, _), c in zip(rows, tg):
        j = idx[c]
        ua.union(i, j)
        if any(kind):
            ub.union(i, j)
    res = residual(n)
    alpha = [cl["members"] for g in res["undecided"] for cl in g["classes"] if cl["size"] == 3][0]
    beta = [cl["members"] for g in res["undecided"] for cl in g["classes"] if cl["size"] == 10][0]
    print("    alpha = %s, beta = %s (indices as in census_n6.json)" % (alpha, beta))
    for nm, cl in (("alpha", alpha), ("beta", beta)):
        groups = defaultdict(list)
        for i in cl:
            groups[ub.find(i)].append(i)
        print("    %s: %d posets, %d classes under the restricted kinds of cuts: %s"
              % (nm, len(cl), len(groups), sorted(groups.values())))
    print("    effective cuts between members of alpha:")
    for (i, A, M, kind, _), c in zip(rows, tg):
        j = idx[c]
        if i in alpha and j in alpha and j != i:
            print("      #%d -> #%d  A=%s  M=%s  singleton=%s one-point=%s height<=1 cut=%s"
                  % (i, j, sorted(members(A)),
                     {a: sorted(members(m)) for a, m in M.items()}, *kind))
    # the example in the labelling of the paper (Section 5.3, Example 5.2)
    Pa = Poset.from_relations(6, [(0, 2), (0, 3), (1, 3), (1, 5), (2, 4), (2, 5), (3, 4)])
    print("    P_alpha of Section 5.3: covers %s, height %d" % (Pa.covers(), Pa.height()))
    for A in ideals(Pa):
        if A in (0, Pa.full()):
            continue
        good, why, M = check_cut(Pa, A)
        if not good:
            continue
        if all(v == 0 for v in M.values()):
            continue
        Q = negative_poset(Pa, A, M)
        kind = basic_kind(Pa, A, M)
        ci = canonical_strings([poset_to_d6(Pa), poset_to_d6(Q)])
        i, j = idx[ci[0]], idx[ci[1]]
        print("      A=%s B=%s M=%s -> P^- covers %s  (#%d -> #%d, same class under restricted "
              "cuts: %s, restricted kind: %s)" % (sorted(members(A)), sorted(members(Pa.full() & ~A)),
                                                  {a: sorted(members(m)) for a, m in M.items()},
                                                  Q.covers(), i, j, ub.find(i) == ub.find(j),
                                                  any(kind)))
    return True


# ---------------------------------------------------------------------------
def part_D():
    print("=== D. Section 5.5 (a): (Lambda+1)(+)(V+1) versus (V+1)(+)(Lambda+1), n = 8")
    # X = 1 + Lambda on {0,1,2,3}: 1,2 < 3 ; Y = 1 + V on {4,..,7}: 5 < 6,7
    X_rel = [(1, 3), (2, 3)]
    Y_rel = [(5, 6), (5, 7)]

    def osum(first, second, rel1, rel2):
        rel = rel1 + rel2 + [(x, y) for x in first for y in second]
        return Poset.from_relations(8, rel)

    P = osum(range(0, 4), range(4, 8), X_rel, Y_rel)          # X below Y
    # Y below X: relabel so that Y = 1+V sits on {0..3} and X = 1+Lambda on {4..7}
    Q = osum(range(0, 4), range(4, 8), [(1, 2), (1, 3)], [(5, 7), (6, 7)])
    det, lab = detail(8), labels(8)
    idx = {c: i for i, c in enumerate(det["canon"])}
    cs = canonical_strings([poset_to_d6(P), poset_to_d6(Q), poset_to_d6(P.op()), poset_to_d6(Q.op())])
    i, j = idx[cs[0]], idx[cs[1]]
    print("    P = (Lambda+1)(+)(V+1): #%d, covers %s" % (i, P.covers()))
    print("    Q = (V+1)(+)(Lambda+1): #%d, covers %s" % (j, Q.covers()))
    print("    isomorphic: %s; P self-dual: %s; Q self-dual: %s" % (i == j, cs[2] == cs[0], cs[3] == cs[1]))
    L, LP, LPS = lab["label_L"], lab["label_LP"], lab["label_LPS"]
    sizeL = defaultdict(int)
    for k in range(len(L)):
        if det["connected"][k]:
            sizeL[L[k]] += 1
    print("    same ~_L class: %s; same L+products class: %s; same LPS class: %s"
          % (L[i] == L[j], LP[i] == LP[j], LPS[i] == LPS[j]))
    print("    sizes of the ~_L classes of P and Q: %d, %d" % (sizeL[L[i]], sizeL[L[j]]))
    fp = (coxeter_polynomial(P), betti_numbers(P), fine_invariants(P, det["cox"][i]))
    fq = (coxeter_polynomial(Q), betti_numbers(Q), fine_invariants(Q, det["cox"][j]))
    print("    Coxeter polynomial, Betti numbers and fine invariants coincide: %s" % (fp == fq))
    print("    Coxeter polynomial %s, Betti numbers %s" % (fp[0], fp[1]))
    return (i != j) and L[i] != L[j] and LP[i] != LP[j] and LPS[i] == LPS[j] and fp == fq


# ---------------------------------------------------------------------------
def part_F():
    print("=== F. Section 5.5 (b): a poset with the derived category of a tree orientation, alone in its ~_L-class (n = 8)")
    print("    S = {s0,s1,s2,s3} with s0<s2, s0<s3, s1<s2 (height one); X_s0 = Lambda (two minimal")
    print("    elements below a maximum), X_s2 = V (a minimum below two maximal elements), X_s1, X_s3 points")
    print("    claim: the lexicographic sum over S is an orientation of the tree T made of two adjacent")
    print("    vertices of degree 4 (each with three further neighbours); the sum Q over S^op is alone in")
    print("    its ~_L-class; the two have the same computed invariants (they are derived equivalent over")
    print("    every field by Ladkani, math/0610685, Theorem 4.14)")
    lam, V, p1, p3 = [0, 1, 2], [3, 4, 5], 6, 7
    inner = [(0, 2), (1, 2), (3, 4), (3, 5)]
    relS = inner + [(x, y) for x in lam for y in V] + [(x, p3) for x in lam] + [(p1, y) for y in V]
    relSop = inner + [(y, x) for x in lam for y in V] + [(p3, x) for x in lam] + [(y, p1) for y in V]
    PS = Poset.from_relations(8, relS)
    Q = Poset.from_relations(8, relSop)
    det, lab = detail(8), labels(8)
    idx = {c: i for i, c in enumerate(det["canon"])}
    cs = canonical_strings([poset_to_d6(PS), poset_to_d6(Q)])
    i, j = idx[cs[0]], idx[cs[1]]
    L, LPS = lab["label_L"], lab["label_LPS"]
    size, trees = defaultdict(int), defaultdict(int)
    for k in range(len(L)):
        if det["connected"][k]:
            size[L[k]] += 1
            trees[L[k]] += det["is_tree"][k]
    deg = defaultdict(int)
    for x, y in PS.covers():
        deg[x] += 1
        deg[y] += 1
    degseq = sorted(deg.values(), reverse=True)
    print("    sum over S:     #%d, covers %s; Hasse diagram a tree: %s, degrees %s"
          % (i, PS.covers(), PS.hasse_is_tree(), degseq))
    print("    Q (over S^op):  #%d, covers %s" % (j, Q.covers()))
    print("    ~_L-class of the tree orientation: %d posets (%d tree orientations); ~_L-class of Q: %d poset(s)"
          % (size[L[i]], trees[L[i]], size[L[j]]))
    print("    same ~_L-class: %s; same class after adding lexicographic sums: %s" % (L[i] == L[j], LPS[i] == LPS[j]))
    fp = (coxeter_polynomial(PS), betti_numbers(PS), fine_invariants(PS, det["cox"][i]))
    fq = (coxeter_polynomial(Q), betti_numbers(Q), fine_invariants(Q, det["cox"][j]))
    print("    Coxeter polynomial %s, Betti numbers %s; fine invariants coincide: %s" % (fp[0], fp[1], fp == fq))
    return (PS.hasse_is_tree() and degseq[:2] == [4, 4] and degseq[2:] == [1] * 6
            and size[L[j]] == 1 and L[i] != L[j] and LPS[i] == LPS[j] and fp == fq)


# ---------------------------------------------------------------------------
def part_G():
    print("=== G. Labelled examples and matrix identities quoted in the paper")
    ok = True
    det8 = detail(8)
    idx8 = {c: i for i, c in enumerate(det8["canon"])}
    tree = Poset.from_relations(8, [(0, 3), (1, 3), (2, 4), (3, 4), (3, 5), (4, 6), (4, 7)])
    Q = Poset.from_relations(8, [(0, 2), (0, 3), (1, 5), (1, 6), (2, 4), (2, 5), (2, 6), (3, 4),
                                 (3, 5), (3, 6), (5, 7), (6, 7)])
    ct, cq = canonical_strings([poset_to_d6(tree), poset_to_d6(Q)])
    i, j = idx8[ct], idx8[cq]
    print("    Section 5.5 (b): labelled tree orientation = #%d, labelled Q = #%d (expected 11768, 3877)"
          % (i, j))
    ok &= (i, j) == (11768, 3877) and len(Q.covers()) == 12 and len(tree.covers()) == 7
    det6 = detail(6)
    idx6 = {c: k for k, c in enumerate(det6["canon"])}
    Pam = Poset.from_relations(6, [(3, 0), (5, 0), (3, 1), (5, 1), (0, 2), (4, 2), (3, 4)])
    k = idx6[canonical_strings([poset_to_d6(Pam)])[0]]
    print("    Example 5.2: labelled P_alpha^- = #%d (expected 95), covers %s" % (k, Pam.covers()))
    ok &= k == 95
    # matrix identities of Section 5.2 on random posets: if C_Q = S^T C_P S with
    # S in GL_n(Z), then Phi_Q = S^{-1} Phi_P S and C_Q +- C_Q^T = S^T (C_P +- C_P^T) S
    import random
    from sympy import Matrix
    from invariants import cartan
    rnd = random.Random(1)
    good = True
    for trial in range(30):
        n = rnd.randint(3, 7)
        rel = [(x, y) for x in range(n) for y in range(x + 1, n) if rnd.random() < 0.35]
        P = Poset.from_relations(n, rel)
        C = Matrix(cartan(P))
        Phi = -C.T.inv() * C
        while True:
            S = Matrix(n, n, lambda r, c: rnd.randint(-2, 2))
            if abs(S.det()) == 1:
                break
        CQ = S.T * C * S
        PhiQ = -CQ.T.inv() * CQ
        good &= PhiQ == S.inv() * Phi * S
        good &= CQ + CQ.T == S.T * (C + C.T) * S
        good &= CQ - CQ.T == S.T * (C - C.T) * S
    print("    Phi_Q = S^{-1} Phi_P S and C_Q +- C_Q^T = S^T (C_P +- C_P^T) S for C_Q = S^T C_P S "
          "(30 random posets): %s" % good)
    ok &= good
    return ok


# ---------------------------------------------------------------------------
def part_E(nmax):
    print("=== E. Section 5.1: naive search versus Theorem 3.2, candidate families sum_A 2^(|A||B|)")
    from canonical import all_posets
    for n in range(1, nmax + 1):
        t0 = time.time()
        Ps = all_posets(n)
        nid = 0
        fam = 0
        worst = 0
        for P in Ps:
            full = P.full()
            for A in ideals(P):
                if A in (0, full):
                    continue
                a = popcount(A)
                nid += 1
                fam += 1 << (a * (n - a))
                worst = max(worst, a * (n - a))
        print("    n = %d: %d posets, %d nonempty proper ideals, %d candidate families "
              "(about 10^%.1f), largest single search 2^%d  [%.0fs]"
              % (n, len(Ps), nid, fam, math.log10(fam) if fam else 0.0, worst,
                 time.time() - t0))
        sys.stdout.flush()
    return True


def main(nmax=9):
    t0 = time.time()
    ok = True
    ok &= part_A(nmax)
    ok &= part_C()
    ok &= part_D()
    ok &= part_F()
    ok &= part_G()
    part_E(nmax)
    print("all checks %s (%.0fs)" % ("passed" if ok else "DID NOT PASS", time.time() - t0))


if __name__ == "__main__":
    main(int(sys.argv[1]) if len(sys.argv) > 1 else 9)
