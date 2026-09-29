/-
Milestone 2: the TQBF game moves as word programs.

`succCode` transcribes `Complexity.QBF.Game.succ` and `startCode` transcribes
`Complexity.QBF.Game.start` (including the validity check of the input word) into the tree's
`Code` language. Every test and number below is built from the ported combinators and
carries, as its value, literally the expression used by the Lean-level definitions, so the
evaluation lemmas are proved by unfolding.
-/
import Complexity.QBF.Game
import Complexity.ArcKaylesProofs.HeaderCode

namespace Complexity.QBF.GameCode

open Complexity.Classes.PolynomialTime
open Complexity.ClassesProofs.InclusionAux.TimeHelpers.Streaming
open Complexity.ArcKaylesProofs.MachineCode (dropCode dropCode_eval leadingOnes leadingOnes_value
  takeCode takeCode_eval eval_bind)
open Complexity.QBF.Game Complexity.Games

variable {I : Type}

/-! ### Semantic tests and numbers -/

/-- Re-label the value of a test by a provably equal function. -/
def Test.withValue (c : Test I) (v : (I → Word) → Bool) (h : ∀ a, c.value a = v a) : Test I :=
  ⟨v, c.code, fun a => by rw [c.correct, h]⟩

@[simp] theorem Test.withValue_value (c : Test I) (v : (I → Word) → Bool) (h : ∀ a, c.value a = v a)
    (a : I → Word) : (Test.withValue c v h).value a = v a := rfl

def Number.withValue (c : Number I) (v : (I → Word) → ℕ) (h : ∀ a, c.value a = v a) : Number I :=
  ⟨v, c.code, fun a => by rw [c.correct, h]⟩

@[simp] theorem Number.withValue_value (c : Number I) (v : (I → Word) → ℕ) (h : ∀ a, c.value a = v a)
    (a : I → Word) : (Number.withValue c v h).value a = v a := rfl

/-- `decide (t = u)` for two Boolean tests. -/
def Test.same (t u : Test I) : Test I :=
  Test.withValue ((t.and u).or (t.not.and u.not)) (fun a => decide (t.value a = u.value a)) (by
    intro a
    simp only [Test.or, Test.and, Test.not]
    cases t.value a <;> cases u.value a <;> rfl)

/-- `t != u`. -/
def Test.xorB (t u : Test I) : Test I :=
  Test.withValue ((t.and u.not).or (t.not.and u)) (fun a => t.value a != u.value a) (by
    intro a
    simp only [Test.or, Test.and, Test.not]
    cases t.value a <;> cases u.value a <;> rfl)

/-- `decide (n ≤ m)`. -/
def Test.le (n m : Number I) : Test I :=
  Test.withValue (Test.lt m n).not (fun a => decide (n.value a ≤ m.value a)) (by
    intro a
    simp only [Test.not, Test.lt, ← decide_not, Nat.not_lt])

/-- `decide (n = m)`. -/
def Test.eqP (n m : Number I) : Test I :=
  Test.withValue (Test.eq n m) (fun a => decide (n.value a = m.value a)) (Test.eq_value n m)

/-- `decide (¬ P)` from a test deciding `P`. -/
def Test.notP (t : Test I) (P : (I → Word) → Prop) [DecidablePred P] (h : ∀ a, t.value a = decide (P a)) :
    Test I :=
  Test.withValue t.not (fun a => decide (¬ P a)) (by intro a; simp only [Test.not, h, decide_not])

/-- `decide (P ∧ Q)`. -/
def Test.andP (t u : Test I) (P Q : (I → Word) → Prop) [DecidablePred P] [DecidablePred Q]
    (ht : ∀ a, t.value a = decide (P a)) (hu : ∀ a, u.value a = decide (Q a)) : Test I :=
  Test.withValue (t.and u) (fun a => decide (P a ∧ Q a)) (by
    intro a; simp only [Test.and, ht, hu, Bool.decide_and])

/-- A Boolean conditional of tests. -/
def Test.ite (c t u : Test I) : Test I :=
  ⟨fun a => if c.value a then t.value a else u.value a, Code.when c t.code u.code, by
    intro a
    rw [Code.eval_when]
    split <;> simp [Test.correct]⟩

@[simp] theorem Test.ite_value (c t u : Test I) (a : I → Word) :
    (Test.ite c t u).value a = if c.value a then t.value a else u.value a := rfl

/-! ### Node lookups -/

def offset (W j : Number I) : Number I := j.mul (W.add (.constant 2))

theorem offset_value (W j : Number I) (a : I → Word) :
    (offset W j).value a = j.value a * recordLength (W.value a) := rfl

def tag0Test (rs : I) (W j : Number I) : Test I := Test.input rs (offset W j)
def tag1Test (rs : I) (W j : Number I) : Test I := Test.input rs ((offset W j).add (.constant 1))

def isVarTest (rs : I) (W j : Number I) : Test I :=
  Test.withValue ((tag0Test rs W j).not.and (tag1Test rs W j).not)
    (fun a => isVar (a rs) (W.value a) (j.value a)) (fun _ => rfl)

def isNotTest (rs : I) (W j : Number I) : Test I :=
  Test.withValue ((tag0Test rs W j).and (tag1Test rs W j).not)
    (fun a => isNot (a rs) (W.value a) (j.value a)) (fun _ => rfl)

def isAndTest (rs : I) (W j : Number I) : Test I :=
  Test.withValue ((tag0Test rs W j).not.and (tag1Test rs W j))
    (fun a => isAnd (a rs) (W.value a) (j.value a)) (fun _ => rfl)

/-- The numeric field of node `j`. -/
def fieldNumber (rs : I) (W j : Number I) : Number I where
  value a := field (a rs) (W.value a) (j.value a)
  code := .bind ((offset W j).add (.constant 2)).code (.bind (.drop (some rs) none) (leadingOnes none).code)
  correct a := by
    simp only [Code.eval, Number.correct, extend, Option.elim_none, Option.elim_some,
      List.length_replicate]
    rfl

@[simp] theorem fieldNumber_value (rs : I) (W j : Number I) (a : I → Word) :
    (fieldNumber rs W j).value a = field (a rs) (W.value a) (j.value a) := rfl

def sizeAtNumber (rs : I) (W j : Number I) : Number I :=
  Number.withValue (Number.choose (isVarTest rs W j) (.constant 1) (fieldNumber rs W j))
    (fun a => sizeAt (a rs) (W.value a) (j.value a)) (fun _ => rfl)

@[simp] theorem sizeAtNumber_value (rs : I) (W j : Number I) (a : I → Word) :
    (sizeAtNumber rs W j).value a = sizeAt (a rs) (W.value a) (j.value a) := rfl

def leftChildNumber (rs : I) (W j : Number I) : Number I :=
  Number.withValue ((j.sub (.constant 1)).sub (sizeAtNumber rs W (j.sub (.constant 1))))
    (fun a => leftChild (a rs) (W.value a) (j.value a)) (fun _ => rfl)

def rightChildNumber (j : Number I) : Number I :=
  Number.withValue (j.sub (.constant 1)) (fun a => rightChild (j.value a)) (fun _ => rfl)

/-! ### Building positions -/

def someCode (c : Code I) : Code I := .append (.literal [true]) c

theorem someCode_eval (c : Code I) (a : I → Word) : (someCode c).eval a = true :: c.eval a := rfl

def mkPosCode (t s : Test I) (len : Number I) (ρ : Code I) (j : Number I) : Code I :=
  .append t.code (.append s.code (.append len.code (.append (.literal [false])
    (.append ρ (.append j.code (.literal [false]))))))

theorem mkPosCode_eval (t s : Test I) (len : Number I) (ρ : Code I) (j : Number I) (a : I → Word) :
    (mkPosCode t s len ρ j).eval a = t.value a :: s.value a ::
      (List.replicate (len.value a) true ++ false :: (ρ.eval a ++ (List.replicate (j.value a) true ++ [false]))) := by
  simp only [mkPosCode, Code.eval, Test.correct, Number.correct, List.singleton_append,
    List.cons_append, List.nil_append, List.append_assoc]

/-! ### The move body -/

/-- The successor program on parsed inputs: `position`, `index` (unary move index), `bodyw`
(prefix and records), `rs` (records) and `ρ` are input indices; `n N W k j` are numbers. -/
def succBody (position index bodyw rs ρ : I) (n N W k j : Number I) : Code I :=
  let t := Test.input position (.constant 0)
  let s := Test.input position (.constant 1)
  let κ := Number.length index
  let idx0 := Test.eqP κ (.constant 0)
  Code.when (Test.eqP (.length position) (.constant 0)) (.literal [])
   (Code.when ((Test.le k n).and (Test.lt j N)).not (.literal [])
    (Code.when (Test.lt k n)
      (Code.when (Test.same t (Test.input bodyw k))
        (Code.when (Test.lt κ (.constant 2))
          (someCode (mkPosCode t.not s (k.add (.constant 1))
            (.append (.source ρ) (Test.eqP κ (.constant 1)).code) j))
          (.literal []))
        (Code.when idx0 (someCode (mkPosCode t.not s k (.source ρ) j)) (.literal [])))
      (Code.when (isVarTest rs W j)
        (Code.when (idx0.and (Test.same t (Test.xorB (Test.input ρ (fieldNumber rs W j)) s)).not)
          (.literal [true]) (.literal []))
        (Code.when (Test.le (.constant 1) j).not (.literal [])
          (Code.when (isNotTest rs W j)
            (Code.when idx0 (someCode (mkPosCode t.not s.not k (.source ρ) (j.sub (.constant 1)))) (.literal []))
            (Code.when (Test.lt (sizeAtNumber rs W (j.sub (.constant 1))) j).not
              (.literal [])
              (Code.when (Test.same t (Test.xorB (isAndTest rs W j) s))
                (Code.when idx0 (someCode (mkPosCode t.not s k (.source ρ) (leftChildNumber rs W j)))
                  (Code.when (Test.eqP κ (.constant 1))
                    (someCode (mkPosCode t.not s k (.source ρ) (rightChildNumber j))) (.literal [])))
                (Code.when idx0 (someCode (mkPosCode t.not s k (.source ρ) j)) (.literal [])))))))))

theorem optionWord_ite (c : Prop) [Decidable c] (x y : Option Word) :
    optionWord (if c then x else y) = if c then optionWord x else optionWord y := by
  split <;> rfl

theorem succBody_eval (position index bodyw rs ρ : I) (n N W k j : Number I) (a : I → Word)
    (hk : (a ρ).length = k.value a) :
    (succBody position index bodyw rs ρ n N W k j).eval a =
      optionWord (succCore (n.value a) (N.value a) (W.value a) (a bodyw) (a rs) (a position).length
        (bit (a position) 0) (bit (a position) 1) (k.value a) (a ρ) (j.value a) (a index).length) := by
  simp only [succBody, Code.eval_when, Test.withValue_value, Test.same, Test.xorB, Test.le,
    Test.eqP, Test.lt, Test.input, Test.not, Test.and, isVarTest, isNotTest, isAndTest,
    fieldNumber_value, sizeAtNumber_value, leftChildNumber, rightChildNumber, Number.withValue_value,
    Number.length, Number.constant, Number.add, Number.sub, someCode_eval, mkPosCode_eval, Code.eval,
    Test.correct, List.length_replicate]
  unfold succCore
  simp only [optionWord_ite]
  simp only [optionWord, mkPos, bit, List.length_replicate, List.length_append, List.length_singleton,
    hk, Bool.not_eq_true']
  rfl

/-! ### The full successor program -/

/-- Parse the instance header and the position, then run `succBody`. -/
noncomputable def succCode : Code MoveInput :=
  .bind (leadingOnes MoveInput.instance).code
  (.bind (dropCode (some .instance) ((Number.length none).add (.constant 1)))
  (.bind (leadingOnes none).code
  (.bind (dropCode (some none) ((Number.length none).add (.constant 1)))
  (.bind (leadingOnes none).code
  (.bind (dropCode (some none) ((Number.length none).add (.constant 1)))
  (.bind (dropCode none (.length (some (some (some (some (some none)))))))
  (.bind (dropCode (some (some (some (some (some (some (some MoveInput.position))))))) (.constant 2))
  (.bind (leadingOnes none).code
  (.bind (dropCode (some (some (some (some (some (some (some (some (some MoveInput.position))))))))) ((Number.length none).add (.constant 3)))
  (.bind (takeCode (.length (some none)) none)
  (.bind (.bind (dropCode (some none) (.length (some (some none)))) (leadingOnes none).code)
  (succBody (some (some (some (some (some (some (some (some (some (some (some (some MoveInput.position)))))))))))) (some (some (some (some (some (some (some (some (some (some (some (some MoveInput.index)))))))))))) (some (some (some (some (some (some none)))))) (some (some (some (some (some none))))) (some none)
    (.length (some (some (some (some (some (some (some (some (some (some (some none)))))))))))) (.length (some (some (some (some (some (some (some (some (some none)))))))))) (.length (some (some (some (some (some (some (some none)))))))) (.length (some (some (some none)))) (.length none)))))))))))))

theorem succCode_eval (w p : Word) (κ : ℕ) :
    succCode.eval (moveEnv w p (List.replicate κ true)) = optionWord (succ w p κ) := by
  simp only [succCode, eval_bind, Number.correct, dropCode_eval, leadingOnes_value, takeCode_eval,
    extend, Option.elim_none, Option.elim_some, List.length_replicate, Number.length, Number.add,
    Number.constant, moveEnv]
  rw [succBody_eval]
  · simp only [Number.length, extend, Option.elim_none, Option.elim_some, List.length_replicate, moveEnv]
    rfl
  · simp only [Number.length, extend, Option.elim_none, Option.elim_some, List.length_replicate,
      List.length_map, List.length_range]

/-! ### Validity of the input word, and the start program -/

/-- The field window of node `j` is canonical: all bits are `1` up to the field value. -/
def canonicalAllTest (rs : I) (W j : Number I) : Test I :=
  Test.withValue
    (Test.forall W (Test.same
      (Test.input (some rs) ((((offset W j).rename some).add (.constant 2)).add (.length none)))
      (Test.lt (.length none) ((fieldNumber rs W j).rename some))))
    (fun a => (List.range (W.value a)).all fun i =>
      bit (a rs) (j.value a * recordLength (W.value a) + 2 + i) ==
        decide (i < field (a rs) (W.value a) (j.value a)))
    (by
      intro a
      apply Bool.eq_iff_iff.mpr
      rw [Test.forall_true, List.all_eq_true]
      simp only [List.mem_range, Test.same, Test.withValue_value, Test.input, Test.lt, Number.add,
        Number.rename, Number.length, Number.constant, offset_value, fieldNumber_value, extend,
        Option.elim_none, Option.elim_some, List.length_replicate, extend_some, Function.comp_apply]
      rfl)

def fieldCanonicalTest (rs : I) (W j : Number I) : Test I :=
  Test.withValue ((Test.lt (fieldNumber rs W j) W).and (canonicalAllTest rs W j))
    (fun a => fieldCanonical (a rs) (W.value a) (j.value a)) (fun _ => rfl)

def nodeValidTest (rs : I) (n W j : Number I) : Test I :=
  let field := fieldNumber rs W j
  let sz1 := sizeAtNumber rs W (j.sub (.constant 1))
  Test.withValue
    ((fieldCanonicalTest rs W j).and
      (Test.ite (isVarTest rs W j) (Test.lt field n)
        (Test.ite (isNotTest rs W j)
          ((Test.le (.constant 1) j).and (Test.eqP field (sz1.add (.constant 1))))
          (((Test.le (.constant 1) j).and (Test.lt sz1 j)).and
            (Test.eqP field (((sizeAtNumber rs W ((j.sub (.constant 1)).sub sz1)).add sz1).add (.constant 1)))))))
    (fun a => nodeValid (a rs) (n.value a) (W.value a) (j.value a)) (fun _ => rfl)

def allNodesTest (rs : I) (n N W : Number I) : Test I :=
  Test.withValue (Test.forall N (nodeValidTest (some rs) (n.rename some) (W.rename some) (.length none)))
    (fun a => (List.range (N.value a)).all fun j => nodeValid (a rs) (n.value a) (W.value a) j)
    (by
      intro a
      apply Bool.eq_iff_iff.mpr
      rw [Test.forall_true, List.all_eq_true]
      simp only [List.mem_range, nodeValidTest, Test.withValue_value, Number.rename, Number.length,
        extend, Option.elim_none, Option.elim_some, List.length_replicate, extend_some])

/-- The validity test, in a context holding the parsed header. -/
def validTest (w a1 a2 bodyw rs : I) (n N W : Number I) : Test I :=
  ((((((Test.lt n (.length w)).and (Test.lt N (.length a1))).and (Test.lt W (.length a2))).and
    (Test.eqP (.length bodyw) (n.add (N.mul (W.add (.constant 2)))))).and
    (Test.le (.constant 1) N)).and (Test.eqP (sizeAtNumber rs W (N.sub (.constant 1))) N)).and
    (allNodesTest rs n N W)

/-- Parse the header, validate, and emit the initial position. -/
noncomputable def startCode : Code Unit :=
  .bind (leadingOnes ()).code
  (.bind (dropCode (some ()) ((Number.length none).add (.constant 1)))
  (.bind (leadingOnes none).code
  (.bind (dropCode (some none) ((Number.length none).add (.constant 1)))
  (.bind (leadingOnes none).code
  (.bind (dropCode (some none) ((Number.length none).add (.constant 1)))
  (.bind (dropCode none (.length (some (some (some (some (some none)))))))
    (Code.when (validTest (some (some (some (some (some (some (some ()))))))) (some (some (some (some (some none))))) (some (some (some none))) (some none) none
        (.length (some (some (some (some (some (some none))))))) (.length (some (some (some (some none))))) (.length (some (some none))))
      (someCode (mkPosCode (Test.constant false) (Test.constant false) (.constant 0) (.literal [])
        ((Number.length (some (some (some (some none))))).sub (.constant 1))))
      (.literal []))))))))

theorem startCode_eval (w : Word) : startCode.eval (fun _ => w) = optionWord (start w) := by
  simp only [startCode, eval_bind, Number.correct, dropCode_eval, leadingOnes_value, extend,
    Option.elim_none, Option.elim_some, List.length_replicate, Number.length, Number.add,
    Number.constant, Code.eval_when, validTest, allNodesTest, Test.and, Test.lt, Test.le, Test.eqP,
    Test.withValue_value, sizeAtNumber_value, Number.mul, Number.sub, someCode_eval, mkPosCode_eval,
    Test.constant, Code.eval]
  unfold start
  simp only [optionWord_ite]
  simp only [optionWord, mkPos, List.length_nil, List.replicate_zero, List.nil_append]
  rfl

end Complexity.QBF.GameCode
