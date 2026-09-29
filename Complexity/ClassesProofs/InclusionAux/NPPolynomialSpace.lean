/-
Ported from https://github.com/EdouardBonnet/classical-complexity (Lax submission lax-434930, commit 0c0840319318),
file `proofs/Lax434930Proofs/InclusionAux/NPPolynomialSpace.lean`.
Original authors: Édouard Bonnet, Codex 5.6 and 6. Licensed under the Apache License, Version 2.0;
see `LICENSES/classical-complexity.LICENSE`. Modifications for this port: module and namespace
renamed from `Lax434930Proofs.InclusionAux.NPPolynomialSpace` to `Complexity.ClassesProofs.InclusionAux.NPPolynomialSpace`; concept-package `axiom` statements
replaced by `alias`es of their proofs; imports adjusted accordingly.
-/
import Complexity.ClassesProofs.InclusionAux.CertificateVerification
import Complexity.ClassesProofs.FiniteAlphabet
import Complexity.Classes.NondeterministicPolynomialTime
import Complexity.Classes.NondeterministicPolynomialSpace

set_option backward.isDefEq.respectTransparency false

namespace Complexity.ClassesProofs.InclusionAux.CertificateMachine

open Turing Complexity.Classes.PolynomialTime
open Complexity.ClassesProofs Complexity.ClassesProofs.SavitchProofs
open scoped Classical

noncomputable section

attribute [local instance] FinTM2.kFin FinTM2.ΛFin FinTM2.σFin

variable {f : Word → Bool} (M : TM2ComputableInPolyTime id Computability.encodeBool f)

def fullCode (p : Polynomial ℕ) : ChoiceProofs.ChoiceLanguage.Command (Key M p) (Alphabet M) (State M) :=
  .seq (.det (constructorCode M p))
    (.seq (ChoiceProofs.GuessWord.code (supply M p) (guess M p) (VerifierRoutine.inputSymbol M))
      (.det (finishCode M p)))

lemma guess_budget (p : Polynomial ℕ) (w : Word) :
    ((constructed M p w).store (supply M p)).length +
      ((constructed M p w).store (guess M p)).length < (spaceBound M p).eval w.length := by
  simpa [guess] using width_lt_bound M p w.length

lemma total (p : Polynomial ℕ) (w : Word) :
    ChoiceProofs.ChoiceLanguage.Total w ((spaceBound M p).eval w.length)
      (fullCode M p) (initial M p) := by
  have hc := constructor_execution M p w _ (input_lt_bound M p w.length) (width_lt_bound M p w.length)
  apply ChoiceProofs.ChoiceLanguage.total_det_seq hc
  refine .seq (ChoiceProofs.GuessWord.total w _ (supply M p) (guess M p)
    (by simp [supply, guess]) (VerifierRoutine.inputSymbol M) (constructed M p w) hc.good.2
    (guess_budget M p w)) ?_
  intro e he
  obtain ⟨xs, hx, rfl⟩ := ChoiceProofs.GuessWord.execution_sound w _ (supply M p) (guess M p)
    (by simp [supply, guess]) (VerifierRoutine.inputSymbol M) (constructed M p w) e hc.good.2
    (guess_budget M p w) he
  have hxs : xs.length = (width p).eval w.length := by simpa using hx
  obtain ⟨r, hr, _⟩ := finish_execution M p w xs _ he.good.2
    (by rw [hxs]; exact preparation_lt_bound M p w.length) (verifier_lt_bound M p w xs hxs)
  exact .det hr

lemma acceptance (p : Polynomial ℕ) (w : Word) :
    (∃ e, ChoiceProofs.ChoiceLanguage.Exec w ((spaceBound M p).eval w.length)
      (fullCode M p) (initial M p) e ∧ e.state.flag = true) ↔
    ∃ y : Word, y.length ≤ p.eval w.length ∧ f (Complexity.Classes.Certificates.pair w y) = true := by
  have hc := constructor_execution M p w _ (input_lt_bound M p w.length) (width_lt_bound M p w.length)
  constructor
  · rintro ⟨e, he, ha⟩
    cases he with
    | seq hconst hrest =>
      obtain rfl := (ChoiceProofs.ChoiceLanguage.det_exec_iff hc).mp hconst
      cases hrest with
      | seq hguess hfinish =>
        obtain ⟨xs, hx, rfl⟩ := ChoiceProofs.GuessWord.execution_sound w _ (supply M p) (guess M p)
          (by simp [supply, guess]) (VerifierRoutine.inputSymbol M) (constructed M p w) _ hc.good.2
          (guess_budget M p w) hguess
        have hxs : xs.length = (width p).eval w.length := by simpa using hx
        obtain ⟨r, hr, hb⟩ := finish_execution M p w xs _ hguess.good.2
          (by rw [hxs]; exact preparation_lt_bound M p w.length) (verifier_lt_bound M p w xs hxs)
        obtain rfl := (ChoiceProofs.ChoiceLanguage.det_exec_iff hr).mp hfinish
        refine ⟨CertificateProjection.first xs.reverse, ?_, hb.symm.trans ha⟩
        exact CertificateBudget.first_bounded (p.eval w.length) xs.reverse (by simp [hxs])
  · rintro ⟨y, hy, ha⟩
    let xs := (CertificateBudget.padded (p.eval w.length) y).reverse
    have hxs : xs.length = (width p).eval w.length := by
      simp [xs, CertificateBudget.padded_length _ _ hy]
    have hg := ChoiceProofs.GuessWord.execution w _ (supply M p) (guess M p)
      (by simp [supply, guess]) (VerifierRoutine.inputSymbol M) (constructed M p w) hc.good.2
      (guess_budget M p w) xs (by simpa using hxs)
    obtain ⟨e, he, hb⟩ := finish_execution M p w xs _ hg.good.2
      (by rw [hxs]; exact preparation_lt_bound M p w.length) (verifier_lt_bound M p w xs hxs)
    refine ⟨e, .seq (.det hc) (.seq hg (.det he)), ?_⟩
    rw [hb]
    simpa [verifierInput, xs, CertificateBudget.first_padded] using ha

end

end Complexity.ClassesProofs.InclusionAux.CertificateMachine

namespace Complexity.ClassesProofs.InclusionAux

open Turing Complexity.Classes.PolynomialTime Complexity.Classes.NondeterministicPolynomialTime
open Complexity.Classes.NondeterministicPolynomialSpace
open Complexity.ClassesProofs CertificateMachine

lemma NP_subset_NPSPACE : NP ⊆ NPSPACE := by
  rintro A ⟨V, ⟨f, hf, ⟨M⟩⟩, p, hp⟩
  obtain ⟨N, _, hN⟩ := FiniteAlphabet.computer M
  letI := N.tm.kFin
  letI := N.tm.ΛFin
  letI := N.tm.σFin
  letI : ∀ k, Fintype (N.tm.Γ k) := fun k => @Fintype.ofFinite _ (hN k)
  refine ⟨spaceBound N p, ChoiceProofs.ChoiceLanguage.nspace_of_execution
    (fullCode N p) (initial N p).state (fun s => s.flag) (spaceBound N p).eval
    (spaceBound_pos N p) A (total N p) ?_⟩
  intro w
  change (∃ e, ChoiceProofs.ChoiceLanguage.Exec w ((spaceBound N p).eval w.length)
    (fullCode N p) (initial N p) e ∧ e.state.flag = true) ↔ w ∈ A
  rw [acceptance, hp]
  exact exists_congr (fun y => and_congr_right (fun _ => hf _))

end Complexity.ClassesProofs.InclusionAux
