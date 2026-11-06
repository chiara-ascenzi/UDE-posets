# UDE-posets

Code and data for the paper

> Chiara Ascenzi, *Derived equivalences between diagram categories of finite posets*, arXiv:2609.10110.

The scripts compute the admissible cuts (Definition 3.1 of the paper) of all
posets with at most nine elements, the associated negative posets
(Corollary 3.3) and the classes of the equivalence relation ∼<sub>L</sub> that they
generate. They compare ∼<sub>L</sub> with derived invariants (Coxeter polynomial, Betti
numbers of the order complex, integral invariants of the incidence matrix)
and with Ladkani's constructions by products and lexicographic sums. They also
produce Tables 1 and 2, Appendix A, and the list of all ∼<sub>L</sub>-classes of
connected posets with at most nine elements.

## Requirements

* Python 3.8 or later (tested with Python 3.13)
* [sympy](https://www.sympy.org) and [networkx](https://networkx.org): `pip install sympy networkx`
* [nauty](https://pallini.di.uniroma1.it) 2.8 or later, for the programs `genposetg`
  (list of all posets with n elements, Brinkmann–McKay) and `labelg` (canonical forms).
  On Debian and Ubuntu, `apt install nauty` installs them as `nauty-genposetg` and
  `nauty-labelg`; both names are recognised.

The results in `results/` and `data/` were computed with nauty 2.8.8, sympy 1.14 and
networkx 3.7.

## Reproducing the results

```
sh run_all.sh
```

recomputes everything (about 10 minutes) and writes the outputs to
`results/` and `data/`. The large intermediate files `census_n*.json`,
`closure_n*.json` and `residual_n*.json` are written to the current directory.

## The ∼<sub>L</sub>-classes (Appendix A.3)

For n = 1, ..., 9, the file `data/connected_posets_n<n>.txt` has one line per
connected poset with n elements, up to isomorphism:

```
<digraph6 string of the Hasse diagram> <label of the class>
```

* The Hasse diagram has an arc x → y for every covering relation x < y. The
  [digraph6](https://users.cecs.anu.edu.au/~bdm/data/formats.txt) string (nauty's
  format, beginning with `&`; SageMath uses a different format with the same name) is
  the canonical form computed by nauty's `labelg`, so two posets are isomorphic if
  and only if their strings coincide.
* Classes are labelled n.1, n.2, ... For n ≤ 6 the labels are those of Appendix A,
  and the classes α and β of Section 5.3 are labelled `6.alpha` and `6.beta`.
  In general the order is: classes containing orientations of trees of type
  A, D, E; Euclidean trees (D̃, Ẽ); orientations of a cycle with no two
  distinct directed paths with the same endpoints (Ã<sub>p,q</sub>); other trees;
  all other classes. Within each group, classes are ordered by decreasing size,
  then by Coxeter polynomial (list of coefficients, leading one first), then by
  the smallest digraph6 string of the class.
* `results/class_list_n1-9.txt` lists every class with its size, its type
  (when it contains a tree orientation or such a cycle orientation; `-`
  otherwise) and its Coxeter polynomial.

To find the class of a given poset:

```python
from admissible_cuts import Poset
from canonical import canonical_strings
from export_classes import hasse_d6

# the Tamari lattice T3 of Example 3.7, with labels 0..4 instead of 1..5
T3 = Poset.from_relations(5, [(0, 1), (1, 3), (3, 4), (0, 2), (2, 4)])
s = canonical_strings([hasse_d6(T3)])[0]
for line in open("data/connected_posets_n5.txt"):
    if line.split()[0] == s:
        print(line.split()[1])          # 5.2
```

Canonical forms may change with the version of nauty; with another version,
recompute the strings with `export_classes.py`.

## Where each statement of the paper is computed

| statement of the paper | script | output |
|---|---|---|
| Section 5.1: Theorem 3.2 checked by brute force for n ≤ 6 (21 864 partitions, 5 914 080 families) | `tests.py` | `results/tests.txt` |
| Section 5.1: 7 704 062 nonempty proper ideals and about 3.4·10¹² families for n = 9 | `extra_checks2.py` (part E) | `results/extra_checks2.txt` |
| Section 5.2: integral homology torsion free for all connected posets with n ≤ 9 | `residual.py` | `results/residual_n1-9.jsonl` (`torsion_posets`) |
| Table 1: connected posets, ∼<sub>L</sub>-classes, computed invariant signatures | `census.py`, `closure.py`, `residual.py`, `make_summary.py` | `results/summary_table_n1-9.md`, `results/closure_n1-9.jsonl` (`classes_L`), `results/residual_n1-9.jsonl` (`refined_invariant_classes`) |
| Theorem 5.1: for n ≤ 5, distinct ∼<sub>L</sub>-classes have distinct Coxeter polynomials | `export_classes.py`, `independent_check.py` | `results/class_list_n1-9.txt`, `results/independent_check_n6.txt` |
| Theorem 5.1: independent implementation | `independent_check.py` | `results/independent_check_n6.txt` |
| Section 5.3: 23 classes, 22 signatures, α (3 posets) and β (10 posets) | `extra_checks.py`, `residual.py` | `results/extra_checks.txt`, `results/residual_n1-9.jsonl` |
| Section 5.3: Coxeter matrices of α and β similar modulo every prime p ≤ 47 | `modp.py` | `results/modp_n6.jsonl` |
| Table 2 | `move_types.py`, `move_types2.py` | `results/move_types_n2-8.jsonl`, `results/move_types2_n2-8.jsonl` |
| Section 5.4: the complete bipartite posets with five elements | `essential_cuts.py` | `results/essential_cuts_n5.txt` |
| Example 5.2 | `extra_checks2.py` (parts C, G) | `results/extra_checks2.txt` |
| Section 5.5: products and lexicographic sums (21 197 → 21 165 classes for n = 9, 1 284 → 1 282 for n = 8) | `closure.py` | `results/closure_n1-9.jsonl` (`classes_LP`, `classes_LPS`) |
| Section 5.5 (a), (b) | `lex_new.py`, `extra_checks2.py` (parts D, F, G) | `results/lex_new_n8.txt`, `results/extra_checks2.txt` |
| Remark after Proposition 3.12 | `extra_checks2.py` (part A) | `results/extra_checks2.txt` |
| Lemma 3.5, Example 4.7 | `extra_checks.py` | `results/extra_checks.txt` |
| Appendix A: drawings and Table 3 | `gen_appendix.py` | `results/appendix_classes.tex` |
| Appendix A.2: classes 6.6 and 6.20 | `extra_checks.py`, `gen_appendix.py` | `results/extra_checks.txt`, `results/appendix_classes.tex` |
| Appendix A.3: the ∼<sub>L</sub>-classes for n ≤ 9 | `export_classes.py` | `data/`, `results/class_list_n1-9.txt` |

`tests.py` also checks Examples 3.7 and 3.9, Proposition 3.4, Corollaries 3.8
and 3.11, Proposition 4.1 and Corollary 4.2 on all posets with at most seven
elements. `gen_appendix.py` enumerates the posets and their admissible cuts
independently of the other scripts; `export_classes.py` checks that for n ≤ 6
the two computations give the same classes and labels.

## Files

| file | content |
|---|---|
| `admissible_cuts.py` | posets as bitmasks; ideals; the sets M(a); the conditions of Definition 3.1; the negative poset (Corollary 3.3); the reconstruction of Proposition 3.4; Ladkani's construction for arbitrary data (for the brute-force checks) |
| `canonical.py` | digraph6 encoding; canonical forms (`labelg`); all posets with n elements (`genposetg`) |
| `invariants.py` | Coxeter polynomial; Betti numbers of the order complex |
| `fine_invariants.py` | Smith normal forms of C ± Cᵀ and of f(Φ); rational Jordan data of Φ; torsion of the integral homology of the order complex |
| `census.py` | all admissible cuts of all posets with n elements; the ∼<sub>L</sub>-classes |
| `closure.py` | the relations generated by ∼<sub>L</sub> together with products and lexicographic sums |
| `residual.py` | computed invariant signatures; torsion check |
| `make_summary.py` | Table 1 |
| `modp.py` | similarity of Coxeter matrices modulo primes p ≤ 47 |
| `move_types.py`, `move_types2.py`, `essential_cuts.py` | restricted kinds of cuts (Section 5.4) |
| `lex_new.py` | lexicographic sums not generated by admissible cuts (Section 5.5) |
| `tests.py`, `independent_check.py`, `extra_checks.py`, `extra_checks2.py` | checks of individual statements |
| `export_classes.py` | the files in `data/` |
| `gen_appendix.py` | the LaTeX source of the drawings and of the table of Appendix A |
| `run_all.sh` | runs everything |

## How to cite

Please cite the paper above. Each release of this repository is archived on
Zenodo; the citation of the software is in `CITATION.cff`.

The code was written with the assistance of the AI program Claude (Anthropic),
from algorithms specified by the author (see the disclosure statement in the paper).

## License

MIT, see `LICENSE`.
