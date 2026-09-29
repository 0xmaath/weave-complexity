/-
Ported from https://github.com/EdouardBonnet/classical-complexity (Lax submission lax-434930, commit 0c0840319318),
file `proofs/Lax434930Proofs/InclusionAux/TimeHelpers/Emitted.lean`.
Original authors: Édouard Bonnet, Codex 5.6 and 6. Licensed under the Apache License, Version 2.0;
see `LICENSES/classical-complexity.LICENSE`. Modifications for this port: module and namespace
renamed from `Lax434930Proofs.InclusionAux.TimeHelpers.Emitted` to `Complexity.ClassicalProofs.InclusionAux.TimeHelpers.Emitted`; concept-package `axiom` statements
replaced by `alias`es of their proofs; imports adjusted accordingly.
-/
import Complexity.ClassicalProofs.InclusionAux.TimeCompiler.StackCopy
import Complexity.ClassicalProofs.PolynomialComposition
import Complexity.Classical.PolynomialTime

set_option backward.isDefEq.respectTransparency false

namespace Complexity.ClassicalProofs.InclusionAux.TimeHelpers.CNFOutput

open Complexity.ClassicalProofs.InclusionAux.TimeCompiler.StackProgram Complexity.ClassicalProofs.InclusionAux.TimeCompiler.StackTransfer
open Complexity.Classical.PolynomialTime

variable {K Aux : Type} [DecidableEq K]

def emitted (out : K) (w : Word) (s : BitStore K Aux) : BitStore K Aux :=
  ⟨(s.state.1, none), Function.update s.stk out (w.reverse ++ s.stk out)⟩

@[simp] lemma emitted_aux (out : K) (w : Word) (s : BitStore K Aux) :
    (emitted out w s).state.1 = s.state.1 := rfl

@[simp] lemma emitted_scratch (out : K) (w : Word) (s : BitStore K Aux) :
    (emitted out w s).state.2 = none := rfl

lemma emitted_empty (out : K) (s : BitStore K Aux) :
    emitted out [] s = ⟨(s.state.1, none), s.stk⟩ := by
  simp [emitted, Function.update_eq_self]

lemma emitted_append (out : K) (u v : Word) (s : BitStore K Aux) :
    emitted out v (emitted out u s) = emitted out (u ++ v) s := by
  simp [emitted, List.reverse_append, List.append_assoc, Function.update_idem]

lemma emitted_source (out src : K) (h : src ≠ out) (w : Word) (s : BitStore K Aux) :
    (emitted out w s).stk src = s.stk src := by
  simp [emitted, h]

end Complexity.ClassicalProofs.InclusionAux.TimeHelpers.CNFOutput
