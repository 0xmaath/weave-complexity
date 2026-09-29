/-
Ported from https://github.com/EdouardBonnet/classical-complexity (Lax submission lax-434930, commit 0c0840319318),
file `proofs/Lax434930Proofs/InclusionAux/CertificateBudget.lean`.
Original authors: Édouard Bonnet, Codex 5.6 and 6. Licensed under the Apache License, Version 2.0;
see `LICENSES/classical-complexity.LICENSE`. Modifications for this port: module and namespace
renamed from `Lax434930Proofs.InclusionAux.CertificateBudget` to `Complexity.ClassicalProofs.InclusionAux.CertificateBudget`; concept-package `axiom` statements
replaced by `alias`es of their proofs; imports adjusted accordingly.
-/
import Complexity.ClassicalProofs.CertificateProjection
import Complexity.ClassicalProofs.Certificates
import Complexity.ClassicalProofs.SavitchProofs.PolynomialConstructor

namespace Complexity.ClassicalProofs.InclusionAux.CertificateBudget

open Complexity.Classical.PolynomialTime Complexity.Classical.Certificates
open Complexity.ClassicalProofs Complexity.ClassicalProofs.SavitchProofs

lemma first_length (xs : Word) : 2 * (CertificateProjection.first xs).length ≤ xs.length := by
  fun_induction CertificateProjection.first xs <;> simp_all [CertificateProjection.first] <;> omega

lemma first_bounded (p : ℕ) (xs : Word) (h : xs.length = 2 * p + 1) :
    (CertificateProjection.first xs).length ≤ p := by
  have := first_length xs
  omega

def padded (p : ℕ) (ys : Word) : Word := pair ys (List.replicate (2 * (p - ys.length)) false)

lemma padded_length (p : ℕ) (ys : Word) (hy : ys.length ≤ p) :
    (padded p ys).length = 2 * p + 1 := by
  rw [padded, Certificates.pair_length]
  simp only [List.length_replicate]
  omega

lemma first_padded (p : ℕ) (ys : Word) : CertificateProjection.first (padded p ys) = ys :=
  CertificateProjection.first_pair _ _

open StackLanguage UnaryPolynomial

noncomputable def code (p : Polynomial ℕ) : UnaryPolynomial.Code p.natDegree :=
  .seq (countCode p.natDegree) (polynomialCode p)

noncomputable def result (p : Polynomial ℕ) (w : Word) : UnaryPolynomial.Data p.natDegree :=
  grown (countResult p.natDegree w) (p.eval w.length)

lemma execution (p : Polynomial ℕ) (w : Word) (bound : ℕ)
    (hn : w.length < bound) (hp : p.eval w.length < bound) :
    Exec w bound (code p) ⟨initial p.natDegree, 0, fun _ => []⟩ (result p w) := by
  have hc := count_exec p.natDegree w bound hn
  have he := polynomial_exec p w.length w bound (countResult p.natDegree w) hc.good.2
    (by simp [countResult]) (by simp [countResult]) (by intro k; simp [countResult])
    (by simpa [countResult] using hp)
  exact Exec.seq hc he

lemma result_output (p : Polynomial ℕ) (w : Word) :
    (result p w).store .output = List.replicate (p.eval w.length) () := by
  simp [result, grown, countResult]

end Complexity.ClassicalProofs.InclusionAux.CertificateBudget
