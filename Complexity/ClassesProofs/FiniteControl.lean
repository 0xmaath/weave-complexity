/-
Ported from https://github.com/EdouardBonnet/classical-complexity (Lax submission lax-434930, commit 0c0840319318),
file `proofs/Lax434930Proofs/FiniteControl.lean`.
Original authors: Édouard Bonnet, Codex 5.6 and 6. Licensed under the Apache License, Version 2.0;
see `LICENSES/classical-complexity.LICENSE`. Modifications for this port: module and namespace
renamed from `Lax434930Proofs.FiniteControl` to `Complexity.ClassesProofs.FiniteControl`; concept-package `axiom` statements
replaced by `alias`es of their proofs; imports adjusted accordingly.
-/
import Complexity.ClassesProofs.Time
import Complexity.Classes.MachineModels

/-! Restrict a finitely supported elementary machine to an actual finite state type. -/

namespace Complexity.ClassesProofs.FiniteControl

open Turing Time

variable {Γ Q : Type} [Inhabited Γ] [Inhabited Q]
variable (M : TM0.Machine Γ Q) (S : Finset Q) (hS : TM0.Supports M (S : Set Q))

@[reducible] def initial : Inhabited {q // q ∈ S} := ⟨⟨default, hS.1⟩⟩

def restrict : @TM0.Machine Γ {q // q ∈ S} (initial M S hS) :=
  fun q a ↦ match h : M q.val a with
    | none => none
    | some p => some (⟨p.1, hS.2 h q.property⟩, p.2)

def decode (c : TM0.Cfg Γ {q // q ∈ S}) : TM0.Cfg Γ Q :=
  ⟨c.q.val, c.Tape⟩

theorem step (c : TM0.Cfg Γ {q // q ∈ S}) :
    (@TM0.step Γ _ (initial M S hS) _ (restrict M S hS) c).map (decode S) =
      TM0.step M (decode S c) := by
  rcases c with ⟨q, T⟩
  simp only [TM0.step, restrict, decode]
  split <;> simp_all [decode]

/-- Every finite run lifts without any time overhead. -/
theorem run {n : ℕ} {a b : TM0.Cfg Γ Q} (h : Run (TM0.step M) n a b)
    (ha : a.q ∈ S) :
    ∃ b' : TM0.Cfg Γ {q // q ∈ S},
      decode S b' = b ∧
      Run (@TM0.step Γ _ (initial M S hS) _ (restrict M S hS)) n
        ⟨⟨a.q, ha⟩, a.Tape⟩ b' :=
  h.lift (decode S) (step M S hS) rfl

theorem halted (c : TM0.Cfg Γ {q // q ∈ S})
    (h : TM0.step M (decode S c) = none) :
    @TM0.step Γ _ (initial M S hS) _ (restrict M S hS) c = none := by
  have he := step M S hS c
  rw [h] at he
  exact Option.map_eq_none_iff.mp he

end Complexity.ClassesProofs.FiniteControl
