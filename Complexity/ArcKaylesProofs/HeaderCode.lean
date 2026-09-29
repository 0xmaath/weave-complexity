/-
Ported from https://github.com/EdouardBonnet/arc-kayles (Lax submission lax-689614, commit dd8b6e67317f),
file `proofs/Lax689614Proofs/HeaderCode.lean`.
Original authors: Édouard Bonnet, gpt-6-astra. Licensed under the Apache License, Version 2.0;
see `LICENSES/arc-kayles.LICENSE`. Modifications for this port: module and namespace
renamed from `Lax689614Proofs.HeaderCode` to `Complexity.ArcKaylesProofs.HeaderCode`; concept-package `axiom` statements
replaced by `alias`es of their proofs; imports adjusted accordingly.
-/
import Complexity.ArcKaylesProofs.FormulaHeader
import Complexity.ArcKaylesProofs.NormalizeCode

set_option backward.isDefEq.respectTransparency false

namespace Complexity.ArcKaylesProofs.MachineCode

open Complexity.ClassesProofs.InclusionAux.TimeHelpers.Streaming
open Complexity.Classes.PolynomialTime

theorem eval_bind {I : Type} (p : Code I) (q : Code (Option I)) (a : I → Word) :
    (Code.bind p q).eval a = q.eval (extend a (p.eval a)) := rfl

def dropCode {I : Type} (i : I) (n : Number I) : Code I :=
  .bind n.code (.drop (some i) none)

theorem dropCode_eval {I : Type} (i : I) (n : Number I) (a : I → Word) :
    (dropCode i n).eval a = (a i).drop (n.value a) := by
  unfold dropCode
  rw [eval_bind, Number.correct]
  simp [Code.eval, extend]

abbrev HeaderContext := Option (Option (Option (Option Unit)))
def nIndex : HeaderContext := some (some (some none))
def mIndex : HeaderContext := some none
def tailIndex : HeaderContext := some (some none)
def wordIndex : HeaderContext := some (some (some (some ())))

def headerEnv (w : Word) : HeaderContext → Word :=
  extend (extend (extend (extend (fun _ : Unit => w)
    (List.replicate (inputVars w) true)) (afterVars w))
    (List.replicate (inputClauses w) true)) (inputMatrix w)

def withHeader (body : Code HeaderContext) : Code Unit :=
  .bind (leadingOnes ()).code
    (.bind (dropCode (some ()) ((Number.length none).add (.constant 1)))
      (.bind (leadingOnes none).code
        (.bind (dropCode (some none) ((Number.length none).add (.constant 1))) body)))

theorem withHeader_eval (body : Code HeaderContext) (w : Word) :
    (withHeader body).eval (fun _ => w) = body.eval (headerEnv w) := by
  simp only [withHeader, eval_bind, Number.correct, dropCode_eval, leadingOnes_value,
    Number.add, Number.length, Number.constant, extend, Option.elim_none, Option.elim_some,
    List.length_replicate]
  rfl

def validTest {I : Type} (n m : Number I) (source tail bits : I) : Test I :=
  (Test.lt n (.length source)).and ((Test.lt m (.length tail)).and
    (Test.eq (.length bits) (m.mul n)))

theorem validTest_header (w : Word) :
    (validTest (.length nIndex) (.length mIndex) wordIndex tailIndex none).value (headerEnv w) = true ↔
      ValidHeader w := by
  simp only [validTest, Test.and, Bool.and_eq_true, Test.lt, Test.eq_value,
    decide_eq_true_eq, Number.length, Number.mul, headerEnv, nIndex, mIndex,
    wordIndex, tailIndex, extend, Option.elim_none, Option.elim_some, List.length_replicate, ValidHeader]

end Complexity.ArcKaylesProofs.MachineCode
