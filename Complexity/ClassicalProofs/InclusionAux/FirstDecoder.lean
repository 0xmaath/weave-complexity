/-
Ported from https://github.com/EdouardBonnet/classical-complexity (Lax submission lax-434930, commit 0c0840319318),
file `proofs/Lax434930Proofs/InclusionAux/FirstDecoder.lean`.
Original authors: Édouard Bonnet, Codex 5.6 and 6. Licensed under the Apache License, Version 2.0;
see `LICENSES/classical-complexity.LICENSE`. Modifications for this port: module and namespace
renamed from `Lax434930Proofs.InclusionAux.FirstDecoder` to `Complexity.ClassicalProofs.InclusionAux.FirstDecoder`; concept-package `axiom` statements
replaced by `alias`es of their proofs; imports adjusted accordingly.
-/
import Complexity.ClassicalProofs.InclusionAux.CertificateBudget
import Complexity.ClassicalProofs.SavitchProofs.StackTransducer

set_option backward.isDefEq.respectTransparency false

namespace Complexity.ClassicalProofs.InclusionAux.FirstDecoder

open Complexity.Classical.PolynomialTime
open Complexity.ClassicalProofs Complexity.ClassicalProofs.SavitchProofs

inductive State | tag | bit | done deriving Fintype, DecidableEq

def transition : State → Bool → State × Option Bool
  | .tag, false => (.bit, none)
  | .tag, true => (.done, none)
  | .bit, b => (.tag, some b)
  | .done, _ => (.done, none)

lemma run_done (xs : Word) : StackTransducer.run transition .done xs = (.done, []) := by
  induction xs with
  | nil => rfl
  | cons b xs ih => simp [StackTransducer.run, transition, ih]

lemma run_output (xs : Word) :
    (StackTransducer.run transition .tag xs).2 = CertificateProjection.first xs := by
  fun_induction CertificateProjection.first xs <;>
    simp_all [StackTransducer.run, transition, CertificateProjection.first, run_done]

variable {K Γ σ : Type}

def lifted (state : State → σ) (readState : σ → State) (bit : Bool → Γ) (readBit : Γ → Bool)
    (s : σ) (g : Γ) : σ × Option Γ :=
  let (t, output) := transition (readState s) (readBit g)
  (state t, output.map bit)

lemma lifted_run (state : State → σ) (readState : σ → State) (bit : Bool → Γ) (readBit : Γ → Bool)
    (hs : ∀ s, readState (state s) = s) (hb : ∀ b, readBit (bit b) = b) (xs : Word) :
    (StackTransducer.run (lifted state readState bit readBit) (state .tag) (xs.map bit)).2 =
      (CertificateProjection.first xs).map bit := by
  have h := StackTransducer.run_map transition (lifted state readState bit readBit) state bit bit
    (fun s g => by simp [lifted, hs, hb]) .tag xs
  simpa only [run_output] using congrArg Prod.snd h

lemma result_output (state : State → σ) (readState : σ → State) (bit : Bool → Γ) (readBit : Γ → Bool)
    (hs : ∀ s, readState (state s) = s) (hb : ∀ b, readBit (bit b) = b)
    (src dst : K) (xs : Word) (d : StackRoutines.Data (K := K) (Γ := Γ) (σ := σ))
    (hstate : d.state.user = state .tag) (hstore : d.store src = xs.map bit) :
    (StackTransducer.result d src dst (lifted state readState bit readBit)).store dst =
      (CertificateProjection.first xs).reverse.map bit ++ d.store dst := by
  classical
  simp only [StackTransducer.result, Function.update_self, hstate, hstore,
    lifted_run state readState bit readBit hs hb xs, List.map_reverse]

end Complexity.ClassicalProofs.InclusionAux.FirstDecoder
