/-
Ported from https://github.com/EdouardBonnet/classical-complexity (Lax submission lax-434930, commit 0c0840319318),
file `proofs/Lax434930Proofs/ComplementClosure.lean`.
Original authors: Édouard Bonnet, Codex 5.6 and 6. Licensed under the Apache License, Version 2.0;
see `LICENSES/classical-complexity.LICENSE`. Modifications for this port: module and namespace
renamed from `Lax434930Proofs.ComplementClosure` to `Complexity.ClassicalProofs.ComplementClosure`; concept-package `axiom` statements
replaced by `alias`es of their proofs; imports adjusted accordingly.
-/
import Complexity.Classical.ComplementClosure
import Mathlib.Logic.Equiv.Bool

set_option backward.isDefEq.respectTransparency false

namespace Complexity.ClassicalProofs

open Complexity.Classical.PolynomialTime

/-- Exchange the two output-symbol interpretations, retaining the machine and its time bound. -/
def negateOutput {f : Word → Bool}
    (M : Turing.TM2ComputableInPolyTime id Computability.encodeBool f) :
    Turing.TM2ComputableInPolyTime id Computability.encodeBool (fun w ↦ !(f w)) where
  tm := M.tm
  inputAlphabet := M.inputAlphabet
  outputAlphabet := M.outputAlphabet.trans Equiv.boolNot
  time := M.time
  outputsFun w := by
    change Turing.TM2OutputsInTime M.tm
      (List.map M.inputAlphabet.invFun w)
      (some [M.outputAlphabet.invFun (!(!(f w)))]) (M.time.eval w.length)
    simpa only [Computability.encodeBool, List.map_cons, List.map_nil, Bool.not_not]
      using! M.outputsFun w

/--
---
conclusion: Complexity.Classical.ComplementClosure.closed_under_complement
---
Compose the output-alphabet equivalence with Boolean negation. The same
machine execution then computes the complemented answer with the same time
bound. Negating the correctness equivalence identifies the complement language.
-/
theorem closed_under_complement (L : Language) : L ∈ P → Lᶜ ∈ P := by
  rintro ⟨f, hf, ⟨M⟩⟩
  refine ⟨fun w ↦ !(f w), ?_, ⟨negateOutput M⟩⟩
  intro w
  change (Bool.not (f w) = true) ↔ w ∉ L
  rw [← hf w]
  cases f w <;> decide

/-- The complement of a polynomial-time decidable language is polynomial-time decidable. -/
alias _root_.Complexity.Classical.ComplementClosure.closed_under_complement := closed_under_complement

end Complexity.ClassicalProofs
