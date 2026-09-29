/-
Ported from https://github.com/EdouardBonnet/cook-levin (Lax submission lax-429075, commit 905f2da2698d),
file `concepts/Lax429075/Satisfiability.lean`.
Original authors: Édouard Bonnet, Codex 5.6 and 6. Licensed under the Apache License, Version 2.0;
see `LICENSES/cook-levin.LICENSE`. Modifications for this port: module and namespace
renamed from `Lax429075.Satisfiability` to `Complexity.CookLevin.Satisfiability`; concept-package `axiom` statements
replaced by `alias`es of their proofs; imports adjusted accordingly.
-/
import Complexity.CookLevin.Encoding
import Complexity.Classes.Certificates

/-!
---
title: The satisfiability language and verifier
type: definition
---
SAT contains precisely the encodings of satisfiable CNF formulas.
A certificate is a finite list of truth values, extended by false outside
its length. The verifier accepts a paired formula encoding and certificate
when every clause is satisfied. Malformed encodings are outside the language.
-/

namespace Complexity.CookLevin.Satisfiability

open CNF Encoding Complexity.Classes.PolynomialTime Complexity.Classes.Certificates

def assignment (y : Word) : Assignment := fun i => (y[i]?).getD false

def SAT : Language := {w | ∃ F, encodeCNF F = w ∧ Satisfiable F}

def Verifier : Language :=
  {z | ∃ (F : Formula) (y : Word), z = pair (encodeCNF F) y ∧ eval F (assignment y) = true}

end Complexity.CookLevin.Satisfiability
