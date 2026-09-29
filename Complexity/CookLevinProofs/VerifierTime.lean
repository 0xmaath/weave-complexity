/-
Ported from https://github.com/EdouardBonnet/cook-levin (Lax submission lax-429075, commit 905f2da2698d),
file `proofs/Lax429075Proofs/VerifierTime.lean`.
Original authors: Édouard Bonnet, Codex 5.6 and 6. Licensed under the Apache License, Version 2.0;
see `LICENSES/cook-levin.LICENSE`. Modifications for this port: module and namespace
renamed from `Lax429075Proofs.VerifierTime` to `Complexity.CookLevinProofs.VerifierTime`; concept-package `axiom` statements
replaced by `alias`es of their proofs; imports adjusted accordingly.
-/
import Complexity.CookLevinProofs.VerifierExecution
import Complexity.CookLevin.VerifierTime

namespace Complexity.CookLevinProofs

open Complexity.Classical.PolynomialTime Complexity.CookLevin.Satisfiability
open Complexity.ClassicalProofs.InclusionAux.TimeCompiler.StackProgram VerifierProgram

/--
---
conclusion: Complexity.CookLevin.VerifierTime.polynomial
assumptions:
---
Decode the pair, evaluate the formula against the certificate, and clear the
work stacks. The finite stack program takes at most $100(n+1)^4$ steps on
every input, including malformed encodings.
-/
lemma verifier_polynomial : Verifier ∈ P := by
  refine ⟨decideVerifier, decideVerifier_correct, ?_⟩
  apply program_polytime program .input .output initial id Computability.encodeBool decideVerifier
    (100 * (Polynomial.X + 1) ^ 4)
  intro w
  simpa [Computability.encodeBool] using program_executes w

alias _root_.Complexity.CookLevin.VerifierTime.polynomial := verifier_polynomial

end Complexity.CookLevinProofs
