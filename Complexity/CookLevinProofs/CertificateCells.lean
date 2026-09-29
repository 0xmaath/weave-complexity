/-
Ported from https://github.com/EdouardBonnet/cook-levin (Lax submission lax-429075, commit 905f2da2698d),
file `proofs/Lax429075Proofs/CertificateCells.lean`.
Original authors: Édouard Bonnet, Codex 5.6 and 6. Licensed under the Apache License, Version 2.0;
see `LICENSES/cook-levin.LICENSE`. Modifications for this port: module and namespace
renamed from `Lax429075Proofs.CertificateCells` to `Complexity.CookLevinProofs.CertificateCells`; concept-package `axiom` statements
replaced by `alias`es of their proofs; imports adjusted accordingly.
-/
import Complexity.CookLevinProofs.CertificateAssignments
import Complexity.CookLevinProofs.MachineBits
import Complexity.CookLevinProofs.CircuitPadding

namespace Complexity.CookLevinProofs.CertificateCircuit

open Complexity.Classical.PolynomialTime Complexity.Classical.Certificates Complexity.CookLevin.CNF
open Complexity.Classical.MachineModels CircuitBuilder
open scoped Classical

def pairedPrefix (x : Word) : Word := pair x []

lemma pair_prefix (x y : Word) : pair x y = pairedPrefix x ++ y := by
  induction x with
  | nil => rfl
  | cons b x ih => simpa only [pair, pairedPrefix, List.cons_append] using congrArg (fun w => false :: b :: w) ih

noncomputable def certificateCell (M : SingleTape) (bound i : ℕ) (a : M.Γ) : Expr :=
  let data := Expr.wire (dataPort i)
  let present := Expr.wire (livePort bound i)
  .disj
    (.conj present (.disj (.conj data (.constant (decide (M.input true = a))))
      (.conj (.neg data) (.constant (decide (M.input false = a))))))
    (.conj (.neg present) (.constant (decide (default = a))))

lemma certificateCell_cost (M : SingleTape) (bound i : ℕ) (a : M.Γ) :
    (certificateCell M bound i a).cost = 11 := rfl

lemma certificateCell_bounded (M : SingleTape) (bound i : ℕ) (a : M.Γ) (hi : i < bound) :
    (certificateCell M bound i a).Bounded (inputCount bound) := by
  simp only [certificateCell, Expr.Bounded, dataPort, livePort, inputCount, and_true]
  omega

lemma certificateCell_eval (M : SingleTape) (bound i : ℕ) (a : M.Γ) (ρ : Assignment) :
    (certificateCell M bound i a).eval ρ =
      decide ((if ρ (livePort bound i) then M.input (ρ (dataPort i)) else default) = a) := by
  cases hd : ρ (dataPort i) <;> cases hl : ρ (livePort bound i) <;>
    simp [certificateCell, Expr.eval, hd, hl]

lemma certificateCell_word (M : SingleTape) (bound i : ℕ) (a : M.Γ) (ρ : Assignment)
    (y : Word) (hi : i < bound)
    (hlive : ∀ j, live bound ρ j = true ↔ j < y.length)
    (hdata : ∀ j, j < y.length → y[j]? = some (ρ (dataPort j))) :
    (certificateCell M bound i a).eval ρ = decide (((y[i]?).map M.input).getD default = a) := by
  rw [certificateCell_eval]
  by_cases hy : i < y.length
  · have hv : ρ (livePort bound i) = true := by simpa [live, hi] using (hlive i).mpr hy
    simp [hv, hdata i hy]
  · have hv : ρ (livePort bound i) = false := by
      have hn : ¬ live bound ρ i = true := fun h => hy ((hlive i).mp h)
      simpa [live, hi] using hn
    have he : y[i]? = none := List.getElem?_eq_none (by omega)
    simp [hv, he]

end Complexity.CookLevinProofs.CertificateCircuit
