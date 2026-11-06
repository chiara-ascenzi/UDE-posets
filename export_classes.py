"""
export_classes.py -- the ~_L-classes of connected posets in machine-readable form.

For each n = 1..NMAX writes data/connected_posets_n<n>.txt with one line per
connected poset with n elements (up to isomorphism):

    <digraph6 string of the Hasse diagram>  <label of its ~_L-class>

The Hasse diagram has an arc x -> y for every covering relation x < y, and the
string is the canonical form computed by nauty's labelg, so that two posets
are isomorphic if and only if their strings coincide.

Classes are labelled n.1, n.2, ... in the order used in Appendix A of the
paper: first the classes containing orientations of trees of type A, D, E,
then Euclidean trees (D~, E~), then orientations of a cycle with no two
distinct directed paths with the same endpoints (A~_{p,q}), then the other
trees ("wild"), then the classes containing none of these; within each group
by decreasing size, then by Coxeter polynomial (list of coefficients, leading
one first), then by the smallest digraph6 string of the class.  For n = 6 the
classes alpha and beta of Section 5.3 are labelled 6.alpha and 6.beta.

Also writes results/class_list_n1-NMAX.txt (one line per class: label, size,
type, Coxeter polynomial) and, for n <= 6, checks that classes and labels
coincide with those of gen_appendix.py, which enumerates the posets and their
admissible cuts independently.

usage: python3 export_classes.py [NMAX]     (default 9; needs census_n*.json)
"""

import json
import os
import sys
from collections import defaultdict

from admissible_cuts import Poset, bit
from canonical import canonical_strings, encode_digraph6, poset_to_d6

ALPHA = [(0, 2), (0, 3), (1, 3), (1, 5), (2, 4), (2, 5), (3, 4)]
BETA = [(0, 3), (0, 5), (1, 5), (2, 3), (2, 4), (4, 5)]


def hasse_d6(P):
    rows = [0] * P.n
    for x, y in P.covers():
        rows[x] |= bit(y)
    return encode_digraph6(P.n, rows)


def hereditary(P):
    """No two distinct directed paths of the Hasse diagram with the same ends."""
    succ = defaultdict(list)
    for x, y in P.covers():
        succ[x].append(y)
    order = P.linear_extension()
    for s in range(P.n):
        cnt = [0] * P.n
        cnt[s] = 1
        for x in order:
            if cnt[x]:
                for y in succ[x]:
                    cnt[y] += cnt[x]
        if any(c > 1 for c in cnt):
            return False
    return True


def graph_type(P):
    """(group, name) for a tree or a cycle Hasse diagram, else None.
    Groups: 0 A, 1 D, 2 E, 3 Euclidean tree, 4 A~_{p,q}, 5 wild tree."""
    n, cov = P.n, P.covers()
    adj = defaultdict(set)
    for x, y in cov:
        adj[x].add(y)
        adj[y].add(x)
    deg = {v: len(adj[v]) for v in range(n)}
    if len(cov) == n - 1 and P.is_connected():
        branch = [v for v in range(n) if deg[v] >= 3]
        if not branch:
            return (0, "A%d" % n)
        if len(branch) == 1:
            c = branch[0]
            arms = []
            for w in adj[c]:
                length, prev, cur = 1, c, w
                while deg[cur] == 2:
                    prev, cur = cur, next(u for u in adj[cur] if u != prev)
                    length += 1
                arms.append(length)
            arms = sorted(arms)
            if len(arms) == 3:
                if arms[:2] == [1, 1]:
                    return (1, "D%d" % n)
                named = {(1, 2, 2): (2, "E6"), (1, 2, 3): (2, "E7"), (1, 2, 4): (2, "E8"),
                         (2, 2, 2): (3, "E~6"), (1, 3, 3): (3, "E~7"), (1, 2, 5): (3, "E~8")}
                if tuple(arms) in named:
                    return named[tuple(arms)]
            if arms == [1, 1, 1, 1]:
                return (3, "D~4")
            return (5, "wild")
        if len(branch) == 2 and all(deg[b] == 3 for b in branch) and \
                all(sum(1 for u in adj[b] if deg[u] == 1) == 2 for b in branch):
            return (3, "D~%d" % (n - 1))
        return (5, "wild")
    if len(cov) == n and all(deg[v] == 2 for v in range(n)) and P.is_connected() \
            and hereditary(P):
        cyc, prev = [0], None
        while len(cyc) < n:
            cur = cyc[-1]
            nxt = next(u for u in sorted(adj[cur]) if u != prev and u not in cyc)
            prev = cur
            cyc.append(nxt)
        fwd = sum(1 for k in range(n) if (cyc[k], cyc[(k + 1) % n]) in set(cov))
        p, q = sorted((fwd, n - fwd))
        return (4, "A~%d,%d" % (p, q))
    return None


def classes(n):
    """Labelled classes of connected posets with n elements:
    list of dicts (label, members as canonical Hasse strings, type, cox)."""
    with open("census_n%d.json" % n) as f:
        det = json.load(f)["detail"]
    conn = [i for i, c in enumerate(det["connected"]) if c]
    Ps = {i: Poset.from_relations(n, [tuple(c) for c in det["covers"][i]]) for i in conn}
    hs = dict(zip(conn, canonical_strings([hasse_d6(Ps[i]) for i in conn])))
    groups = defaultdict(list)
    for i in conn:
        groups[det["comp"][i]].append(i)
    special = {}
    if n == 6:
        idx = {c: i for i, c in enumerate(det["canon"])}
        for name, cov in (("alpha", ALPHA), ("beta", BETA)):
            j = idx[canonical_strings([poset_to_d6(Poset.from_relations(6, cov))])[0]]
            special[det["comp"][j]] = name
    infos = []
    for c, mem in groups.items():
        cox = det["cox"][mem[0]]
        assert all(det["cox"][i] == cox for i in mem)
        types = {graph_type(Ps[i]) for i in mem if hereditary(Ps[i])} - {None}
        assert len(types) <= 1, types
        typ = types.pop() if types else None
        strings = sorted(hs[i] for i in mem)
        spec = {"alpha": 1, "beta": 2}.get(special.get(c), 0)
        infos.append({"key": (spec, typ[0] if typ else 9, -len(mem), cox, strings[0]),
                      "members": strings, "type": typ[1] if typ else "-",
                      "cox": cox, "special": special.get(c)})
    infos.sort(key=lambda d: d["key"])
    for k, d in enumerate(infos, 1):
        d["label"] = "%d.%s" % (n, d["special"] or k)
    return infos


def check_against_gen_appendix(n, infos):
    import gen_appendix as ga
    ga_infos = sorted((ga.class_info(m) for m in ga.classes(n)), key=ga.sort_key)
    for k, gi in enumerate(ga_infos, 1):
        label = "%d.%s" % (n, gi["special"] or k)
        Ps = [Poset.from_down(n, list(Q)) for Q in gi["members"]]
        strings = sorted(canonical_strings([hasse_d6(P) for P in Ps]))
        mine = [d for d in infos if d["label"] == label]
        assert len(mine) == 1 and mine[0]["members"] == strings, (n, label)
        assert list(gi["chi"]) == list(mine[0]["cox"]), (n, label)
    assert len(ga_infos) == len(infos)


def poly_str(c):
    d = len(c) - 1
    terms = []
    for k, a in enumerate(c):
        e = d - k
        if a == 0:
            continue
        mon = "" if e == 0 else ("t" if e == 1 else "t^%d" % e)
        coef = str(abs(a)) if (abs(a) != 1 or e == 0) else ""
        terms.append(("-" if a < 0 else "+") + coef + mon)
    s = "".join(terms)
    return s[1:] if s.startswith("+") else s


def main(nmax):
    os.makedirs("data", exist_ok=True)
    os.makedirs("results", exist_ok=True)
    summary = []
    for n in range(1, nmax + 1):
        infos = classes(n)
        lines = []
        for d in infos:
            for s in d["members"]:
                lines.append("%s %s" % (s, d["label"]))
            summary.append("%-9s %6d  %-7s %s" % (d["label"], len(d["members"]), d["type"],
                                                 poly_str(d["cox"])))
        with open("data/connected_posets_n%d.txt" % n, "w") as f:
            f.write("\n".join(lines) + "\n")
        checked = ""
        if 3 <= n <= 6:
            check_against_gen_appendix(n, infos)
            checked = "; classes and labels agree with gen_appendix.py"
        print("n = %d: %d connected posets, %d classes%s"
              % (n, len(lines), len(infos), checked))
        sys.stdout.flush()
    with open("results/class_list_n1-%d.txt" % nmax, "w") as f:
        f.write("# label     size  type    Coxeter polynomial\n")
        f.write("\n".join(summary) + "\n")


if __name__ == "__main__":
    main(int(sys.argv[1]) if len(sys.argv) > 1 else 9)
