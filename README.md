# weave-complexity

A Lean 4 complexity-theory foundation library. Milestone 1 is a port, not new
mathematics: it brings three existing Lean developments into one Lake project
under the `Complexity` namespace, with every "concept package" axiom of the
sources replaced by the actual proof.

| Source | Lax id | Ported namespace | Content |
| --- | --- | --- | --- |
| [EdouardBonnet/classical-complexity](https://github.com/EdouardBonnet/classical-complexity) @ `0c08403` | lax-434930 | `Complexity.Classical`, `Complexity.ClassicalProofs` | L, NL, P, NP, coNL, coNP, PSPACE, NPSPACE, EXPTIME as sets of languages of finite binary strings; the inclusion chain `L ⊆ NL ⊆ P ⊆ NP ⊆ PSPACE = NPSPACE ⊆ EXPTIME`; single-tape and finite-stack characterizations of P; closure of P under complement. |
| [EdouardBonnet/cook-levin](https://github.com/EdouardBonnet/cook-levin) @ `905f2da` | lax-429075 | `Complexity.CookLevin`, `Complexity.CookLevinProofs` | CNF, its binary encoding, SAT, polynomial many-one reductions, NP-completeness, the Cook–Levin theorem with a compiled reduction machine. |
| [EdouardBonnet/arc-kayles](https://github.com/EdouardBonnet/arc-kayles) @ `dd8b6e6` | lax-689614 | `Complexity.ArcKayles`, `Complexity.ArcKaylesProofs` | Arc Kayles, Sprague–Grundy values, the positive CNF game, Schaefer's PSPACE-hardness, the reduction to Arc Kayles, and PSPACE-completeness of Arc Kayles. |

The sources are Apache-2.0; their licenses are in `LICENSES/`, and every
ported file carries an attribution header naming its origin, commit and
modifications. [BoltonBailey/complexitylib](https://github.com/BoltonBailey/complexitylib)
was not needed: the Cook–Levin dependency of arc-kayles is Bonnet's own
`cook-levin` submission, which is ported here.

## Toolchain

* Lean `leanprover/lean4:v4.33.0`
* Mathlib `db584cd6d46c92f209a44c0f1c829460d327499d`

These are the exact revisions the pinned source commits build against. The
v4.30.0 line mentioned in the task exists only on an older branch of
classical-complexity; the arc-kayles and cook-levin sources depend on the
v4.33 branch (`integrate-p-mathlib-4.33`, commit `0c08403`), which also
inlines the former `p-complement` dependency, so that repository is not a
separate dependency any more.

## Layout

```
Complexity.lean                  root module: imports everything below
Complexity/Classical/            definitions (former "concepts") of classical-complexity
Complexity/ClassicalProofs/      proofs of classical-complexity
Complexity/CookLevin/            definitions of cook-levin
Complexity/CookLevinProofs/      proofs of cook-levin
Complexity/ArcKayles/            definitions of arc-kayles
Complexity/ArcKaylesProofs/      proofs of arc-kayles
Complexity/StatementCheck.lean   generated: re-elaborates every archived statement
scripts/check.sh                 CI acceptance checks
scripts/AxiomCheck.lean          generated: `#print axioms` + hard failure on non-standard axioms
scripts/forbidden_tokens.py      no sorry/admit/axiom/native_decide outside comments
AUDIT.md                         semantic audit of the load-bearing definitions
```

### How the concept axioms were discharged

In the Lax archive, each "concept" package states its theorems as `axiom`s
and a separate "proof" package proves them under different names; the archive
tool checks that the types agree. In this port:

* every `axiom` was deleted from the concept files (a comment in its place
  says where the proof lives);
* immediately after each annotated proof theorem (the ones whose docstring
  carries `conclusion: <concept name>`), an
  `alias _root_.<concept name> := <proof name>` re-exports the proof under the
  concept's original fully qualified name, so all downstream references to
  the concept statement resolve to the proof;
* modules that use a concept statement now import the proof module that
  provides it (the import graph is verified acyclic);
* `Complexity/StatementCheck.lean` restates each original axiom, binders and
  statement copied verbatim from the archived concept file, and checks with
  `example : ∀ <binders>, <statement> := @<name>` that the theorem carrying
  the name has exactly that type.

The one axiom without a proof in the sources, `Lax434930.PVersusNP.P_ne_NP`
("open question"), was dropped. No `sorry`, `admit`, `axiom` or
`native_decide` occurs anywhere in the ported tree.

Top-level theorems (see `AUDIT.md` §4.6, §5, §7 for the statements):

```
Complexity.Classical.BasicProperties.{L_subset_NL, NL_subset_P, P_subset_NP, NP_subset_PSPACE, NPSPACE_subset_EXPTIME}
Complexity.Classical.PolynomialSpaceEquality.PSPACE_eq_NPSPACE
Complexity.Classical.ComplementClosure.closed_under_complement
Complexity.Classical.ModelEquivalence.singleTapeP_eq_P
Complexity.Classical.FiniteStackEquivalence.finiteStackP_eq_P
Complexity.CookLevin.CookLevin.np_complete
Complexity.ArcKayles.Completeness.pspace_complete
```

## Building and checking

```sh
lake exe cache get      # Mathlib oleans
scripts/check.sh        # lake build, token scan, axiom audit
```

`scripts/check.sh` fails unless `lake build` is clean (no errors, no `sorry`
warnings), the token scan is clean, and `#print axioms` on every ported
top-level statement (all 41 former concept axioms) shows nothing beyond
`propext`, `Classical.choice` and `Quot.sound`. The same script runs in CI
(`.github/workflows/ci.yml`).

## Regenerating the port

The tree was produced mechanically by a script from the pinned source
commits; the attribution header of each file records its origin. Nothing in
this milestone defines new problems or games.
