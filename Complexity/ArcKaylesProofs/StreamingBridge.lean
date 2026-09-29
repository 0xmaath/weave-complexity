/-
Ported from https://github.com/EdouardBonnet/arc-kayles (Lax submission lax-689614, commit dd8b6e67317f),
file `proofs/Lax689614Proofs/StreamingBridge.lean`.
Original authors: Édouard Bonnet, gpt-6-astra. Licensed under the Apache License, Version 2.0;
see `LICENSES/arc-kayles.LICENSE`. Modifications for this port: module and namespace
renamed from `Lax689614Proofs.StreamingBridge` to `Complexity.ArcKaylesProofs.StreamingBridge`; concept-package `axiom` statements
replaced by `alias`es of their proofs; imports adjusted accordingly.
-/
import Complexity.ArcKaylesProofs.UniformPatterns
import Complexity.ArcKaylesProofs.CodeComputer

set_option backward.isDefEq.respectTransparency false

namespace Complexity.ArcKaylesProofs.CircuitStreaming

open Complexity.Classes.PolynomialTime

namespace CS
export Complexity.ClassesProofs.InclusionAux.TimeHelpers.Streaming (Code Number Test extend)
namespace Code
export Complexity.ClassesProofs.InclusionAux.TimeHelpers.Streaming.Code (eval)
end Code
end CS

namespace CL
export Complexity.CookLevinProofs.Streaming (Code Number Test extend Expression)
namespace Code
export Complexity.CookLevinProofs.Streaming.Code (eval)
end Code
end CL

/-- Embed the Cook–Levin output language in the extended archive language.
    The latter additionally supports bounded state iteration. -/
def liftCode : {I : Type} → CL.Code I → CS.Code I
  | _, .literal w => .literal w
  | _, .source i => .source i
  | _, .length i => .length i
  | _, .drop s i => .drop s i
  | _, .inspect i f => .inspect i f
  | _, .append p q => .append (liftCode p) (liftCode q)
  | _, .bind p q => .bind (liftCode p) (liftCode q)
  | _, .branch i p q => .branch i (liftCode p) (liftCode q)
  | _, .forRange n p => .forRange n (liftCode p)

theorem liftCode_eval {I : Type} (c : CL.Code I) (a : I → Word) : (liftCode c).eval a = c.eval a := by
  induction c with
  | literal w | source i | length i | drop s i | inspect i f => rfl
  | append p q ihp ihq => simp only [liftCode, CS.Code.eval, CL.Code.eval, ihp, ihq]
  | bind p q ihp ihq =>
    simp only [liftCode, CS.Code.eval, CL.Code.eval, ihp, ihq]
    rfl
  | branch i p q ihp ihq => simp only [liftCode, CS.Code.eval, CL.Code.eval, ihp, ihq]
  | forRange n p ih =>
    simp only [liftCode, CS.Code.eval, CL.Code.eval, ih]
    rfl

def liftNumber {I : Type} (n : CL.Number I) : CS.Number I :=
  ⟨n.value, liftCode n.code, fun a => (liftCode_eval n.code a).trans (n.correct a)⟩

def liftTest {I : Type} (t : CL.Test I) : CS.Test I :=
  ⟨t.value, liftCode t.code, fun a => (liftCode_eval t.code a).trans (t.correct a)⟩

theorem cookCode_polynomial (c : CL.Code Unit) :
    Nonempty (Turing.TM2ComputableInPolyTime id id (fun w => c.eval (fun _ => w))) := by
  have h := MachineCode.code_polynomial_time (liftCode c)
  simpa only [liftCode_eval] using h

end Complexity.ArcKaylesProofs.CircuitStreaming
