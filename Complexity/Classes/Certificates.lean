/-
Ported from https://github.com/EdouardBonnet/classical-complexity (Lax submission lax-434930, commit 0c0840319318),
file `concepts/Lax434930/Certificates.lean`.
Original authors: Édouard Bonnet, Codex 5.6 and 6. Licensed under the Apache License, Version 2.0;
see `LICENSES/classical-complexity.LICENSE`. Modifications for this port: module and namespace
renamed from `Lax434930.Certificates` to `Complexity.Classes.Certificates`; concept-package `axiom` statements
replaced by `alias`es of their proofs; imports adjusted accordingly.
-/
import Complexity.Classes.PolynomialTime

/-!
---
title: Binary encoding of an input and a certificate
type: definition
---
To encode a pair $(x,y)$ of binary strings, replace each bit $b$ of $x$ by
$0b$, then append a single $1$ followed by $y$. This encoding has length
$2|x|+|y|+1$ and has a unique decoding. In particular, a polynomial bound in
the encoded length is a polynomial bound in the combined input and
certificate lengths.
-/

namespace Complexity.Classes.Certificates

open PolynomialTime

/-- A self-delimiting encoding of the first string, followed by the second. -/
def pair : Word → Word → Word
  | [], y => true :: y
  | b :: x, y => false :: b :: pair x y

/-- Decode a pair, rejecting a missing delimiter or an incomplete bit block. -/
def unpair : Word → Option (Word × Word)
  | [] => none
  | true :: y => some ([], y)
  | false :: [] => none
  | false :: b :: rest => (unpair rest).map (fun p => (b :: p.1, p.2))

/- The archived concept stated `unpair_pair` here as an `axiom`. In this port it is a
theorem: it is proved as `Complexity.ClassesProofs.Certificates.unpair_pair` in `Complexity.ClassesProofs.Certificates`, which
re-exports it under the name `Complexity.Classes.Certificates.unpair_pair` via `alias`. -/

/- The archived concept stated `pair_injective` here as an `axiom`. In this port it is a
theorem: it is proved as `Complexity.ClassesProofs.Certificates.pair_injective` in `Complexity.ClassesProofs.Certificates`, which
re-exports it under the name `Complexity.Classes.Certificates.pair_injective` via `alias`. -/

/- The archived concept stated `pair_length` here as an `axiom`. In this port it is a
theorem: it is proved as `Complexity.ClassesProofs.Certificates.pair_length` in `Complexity.ClassesProofs.Certificates`, which
re-exports it under the name `Complexity.Classes.Certificates.pair_length` via `alias`. -/

end Complexity.Classes.Certificates
