/-
Ported from https://github.com/EdouardBonnet/cook-levin (Lax submission lax-429075, commit 905f2da2698d),
file `concepts/Lax429075/EncodingCorrect.lean`.
Original authors: Édouard Bonnet, Codex 5.6 and 6. Licensed under the Apache License, Version 2.0;
see `LICENSES/cook-levin.LICENSE`. Modifications for this port: module and namespace
renamed from `Lax429075.EncodingCorrect` to `Complexity.CookLevin.EncodingCorrect`; concept-package `axiom` statements
replaced by `alias`es of their proofs; imports adjusted accordingly.
-/
import Complexity.CookLevin.Encoding

/-!
---
title: Decoding an encoded formula
type: lemma
---
The binary decoder recovers every encoded CNF formula.
-/

namespace Complexity.CookLevin.EncodingCorrect

open CNF Encoding

/- The archived concept stated `roundtrip` here as an `axiom`. In this port it is a
theorem: it is proved as `Complexity.CookLevinProofs.encoding_roundtrip` in `Complexity.CookLevinProofs.Encoding`, which
re-exports it under the name `Complexity.CookLevin.EncodingCorrect.roundtrip` via `alias`. -/

end Complexity.CookLevin.EncodingCorrect
