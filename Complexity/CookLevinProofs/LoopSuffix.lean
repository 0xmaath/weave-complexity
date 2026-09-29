/-
Ported from https://github.com/EdouardBonnet/cook-levin (Lax submission lax-429075, commit 905f2da2698d),
file `proofs/Lax429075Proofs/LoopSuffix.lean`.
Original authors: Édouard Bonnet, Codex 5.6 and 6. Licensed under the Apache License, Version 2.0;
see `LICENSES/cook-levin.LICENSE`. Modifications for this port: module and namespace
renamed from `Lax429075Proofs.LoopSuffix` to `Complexity.CookLevinProofs.LoopSuffix`; concept-package `axiom` statements
replaced by `alias`es of their proofs; imports adjusted accordingly.
-/
import Complexity.CookLevinProofs.LiteralExecution

namespace Complexity.CookLevinProofs.VerifierProgram

open Complexity.ClassesProofs.InclusionAux.TimeCompiler.StackProgram

lemma loop_suffix_step {p q : Code} {b : Control → Bool} {s u t : Data} {a c : ℕ}
    (hb : b s.state = true) (hp : Executes p s u a)
    (hrest : Executes (.seq (.loop b p) q) u t c) :
    Executes (.seq (.loop b p) q) s t (a + c + 1) := by
  cases hrest with
  | seq hl hq =>
    convert Executes.seq (.loop_true hb hp hl) hq using 1 <;> omega

end Complexity.CookLevinProofs.VerifierProgram
