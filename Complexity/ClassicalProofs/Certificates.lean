/-
Ported from https://github.com/EdouardBonnet/classical-complexity (Lax submission lax-434930, commit 0c0840319318),
file `proofs/Lax434930Proofs/Certificates.lean`.
Original authors: Édouard Bonnet, Codex 5.6 and 6. Licensed under the Apache License, Version 2.0;
see `LICENSES/classical-complexity.LICENSE`. Modifications for this port: module and namespace
renamed from `Lax434930Proofs.Certificates` to `Complexity.ClassicalProofs.Certificates`; concept-package `axiom` statements
replaced by `alias`es of their proofs; imports adjusted accordingly.
-/
import Complexity.Classical.Certificates
import Mathlib.Tactic
import Batteries.Tactic.Alias

namespace Complexity.ClassicalProofs.Certificates

open Complexity.Classical.PolynomialTime Complexity.Classical.Certificates

/--
---
conclusion: Complexity.Classical.Certificates.unpair_pair
assumptions:
---
Induct on the first word, decoding one two-bit block at a time.
-/
theorem unpair_pair (x y : Word) : unpair (pair x y) = some (x, y) := by
  induction x with
  | nil => rfl
  | cons b x ih => simp [pair, unpair, ih]

/-- Encoding followed by decoding recovers both strings. -/
alias _root_.Complexity.Classical.Certificates.unpair_pair := unpair_pair

/--
---
conclusion: Complexity.Classical.Certificates.pair_injective
assumptions:
---
Apply the decoder to an equality of encodings.
-/
theorem pair_injective : Function.Injective (fun p : Word × Word => pair p.1 p.2) := by
  intro a b h
  have hd := congrArg unpair h
  simpa only [unpair_pair, Prod.mk.eta, Option.some.injEq] using hd

/-- Distinct pairs of strings have distinct encodings. -/
alias _root_.Complexity.Classical.Certificates.pair_injective := pair_injective

/--
---
conclusion: Complexity.Classical.Certificates.pair_length
assumptions:
---
Each bit of the first word contributes two bits, and the delimiter contributes one.
-/
theorem pair_length (x y : Word) : (pair x y).length = 2 * x.length + y.length + 1 := by
  induction x with
  | nil => simp [pair]
  | cons b x ih =>
    simp only [pair, List.length_cons, ih]
    omega

/-- The encoding has linear length in its two arguments. -/
alias _root_.Complexity.Classical.Certificates.pair_length := pair_length

end Complexity.ClassicalProofs.Certificates
