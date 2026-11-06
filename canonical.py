"""
canonical.py -- isomorphism classes of posets through nauty.

A poset is encoded as the digraph of its strict order relation
(arc x -> y iff x < y) in digraph6 format; canonical labelling is done in
batch by nauty's `labelg`.  Two posets are isomorphic iff their canonical
strings coincide.  The list of all posets with n points is produced by
nauty's `genposetg` (Brinkmann-McKay), which outputs Hasse diagrams.
"""

import os
import shutil
import subprocess
import tempfile

from admissible_cuts import Poset, bit, members

LABELG = shutil.which("nauty-labelg") or shutil.which("labelg")
GENPOSETG = shutil.which("nauty-genposetg") or shutil.which("genposetg")


# ----------------------------------------------------------------------------
# digraph6
# ----------------------------------------------------------------------------

def encode_digraph6(n, rows):
    """rows[i] = bitmask of the out-neighbours of i.  Requires n <= 62."""
    assert n <= 62
    bits = []
    for i in range(n):
        r = rows[i]
        for j in range(n):
            bits.append((r >> j) & 1)
    while len(bits) % 6:
        bits.append(0)
    chars = ["&", chr(n + 63)]
    for k in range(0, len(bits), 6):
        v = 0
        for b in bits[k:k + 6]:
            v = (v << 1) | b
        chars.append(chr(v + 63))
    return "".join(chars)


def decode_digraph6(s):
    s = s.strip()
    assert s[0] == "&"
    n = ord(s[1]) - 63
    assert 0 <= n <= 62
    bits = []
    for c in s[2:]:
        v = ord(c) - 63
        for k in range(5, -1, -1):
            bits.append((v >> k) & 1)
    rows = [0] * n
    for i in range(n):
        for j in range(n):
            if bits[i * n + j]:
                rows[i] |= bit(j)
    return n, rows


def poset_to_d6(P):
    """Strict order relation of P as digraph6."""
    return encode_digraph6(P.n, [P.up[x] & ~bit(x) for x in range(P.n)])


def poset_from_hasse_d6(s):
    n, rows = decode_digraph6(s)
    pairs = [(i, j) for i in range(n) for j in members(rows[i])]
    return Poset.from_relations(n, pairs)


# ----------------------------------------------------------------------------
# nauty wrappers
# ----------------------------------------------------------------------------

def canonical_strings(d6_list):
    """Canonical digraph6 strings (same order as the input)."""
    if not d6_list:
        return []
    with tempfile.TemporaryDirectory() as tmp:
        fin = os.path.join(tmp, "in.d6")
        fout = os.path.join(tmp, "out.d6")
        with open(fin, "w") as f:
            f.write("\n".join(d6_list))
            f.write("\n")
        subprocess.run([LABELG, "-q", fin, fout], check=True)
        with open(fout) as f:
            out = f.read().split()
    assert len(out) == len(d6_list), (len(out), len(d6_list))
    return out


def canonical_forms(posets):
    return canonical_strings([poset_to_d6(P) for P in posets])


def all_posets(n):
    """All posets with n points up to isomorphism (genposetg)."""
    if n == 0:
        return [Poset(0, [], [])]
    res = subprocess.run([GENPOSETG, str(n), "t", "q"], check=True,
                         capture_output=True, text=True)
    lines = [l for l in res.stdout.split("\n") if l.startswith("&")]
    return [poset_from_hasse_d6(l) for l in lines]
