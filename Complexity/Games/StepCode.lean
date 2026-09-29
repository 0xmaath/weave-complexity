/-
Milestone 2: the depth-first transition as a word program.

`nextCode G` transcribes `Complexity.Games.DepthFirst.nextWord` into the tree's `Code`
language, calling the game's own successor program once per step. `initialCode G` builds the
initial search state from the game's start program, and `driverCode G` dispatches between
the two. Every `Code` runs in polynomial time and space by construction, so these
transcriptions are all the machine-level content needed for PSPACE membership.
-/
import Complexity.Games.StateWords
import Complexity.ArcKaylesProofs.HeaderCode

namespace Complexity.Games.StepCode

open Complexity.Classes.PolynomialTime
open Complexity.ClassesProofs.InclusionAux.TimeHelpers.Streaming
open Complexity.ArcKaylesProofs.MachineCode (dropCode dropCode_eval leadingOnes leadingOnes_value
  takeCode takeCode_eval eval_bind)
open Complexity.Games.DepthFirst

theorem eval_append {I : Type} (p q : Code I) (a : I → Word) :
    (Code.append p q).eval a = p.eval a ++ q.eval a := rfl

/-- `1^fuel 0 1^count 0 1^len 0 pos`. -/
def frameCode {I : Type} (fuel count len : Number I) (pos : Code I) : Code I :=
  .append fuel.code (.append (.literal [false]) (.append count.code (.append (.literal [false])
    (.append len.code (.append (.literal [false]) pos)))))

theorem frameCode_eval {I : Type} (fuel count len : Number I) (pos : Code I) (a : I → Word) :
    (frameCode fuel count len pos).eval a =
      List.replicate (fuel.value a) true ++ false :: (List.replicate (count.value a) true ++ false ::
        (List.replicate (len.value a) true ++ false :: pos.eval a)) := by
  simp only [frameCode, eval_append, Number.correct, Code.eval, List.append_assoc, List.cons_append,
    List.nil_append]

def nextBodyCode {I : Type} (A fuel count : Number I) (state frames pos rest child : I) : Code I :=
  Code.when (Test.input state (.constant 0))
    (Code.when (Test.input state (.constant 1))
      (.append (.literal [false, false]) (.source frames))
      (.append (.literal [true, true]) (.source rest)))
    (Code.when ((Test.eq fuel (.constant 0)).or (Test.eq count (.constant 0)))
      (.append (.literal [true, false]) (.source rest))
      (Code.when (Test.eq (.length child) (.constant 0))
        (.append (.literal [false, false])
          (.append (frameCode fuel (count.sub (.constant 1)) (.length pos) (.source pos)) (.source rest)))
        (.append (.literal [false, false])
          (.append (frameCode (fuel.sub (.constant 1)) A ((Number.length child).sub (.constant 1))
              (dropCode child (.constant 1)))
            (.append (frameCode fuel (count.sub (.constant 1)) (.length pos) (.source pos))
              (.source rest))))))

theorem nextBodyCode_eval {I : Type} (A fuel count : Number I) (state frames pos rest child : I)
    (a : I → Word) :
    (nextBodyCode A fuel count state frames pos rest child).eval a =
      nextBody (A.value a) (fuel.value a) (count.value a) (a state) (a frames) (a pos) (a rest) (a child) := by
  simp only [nextBodyCode, Code.eval_when, eval_append, frameCode_eval, dropCode_eval,
    Test.input, Test.or, Test.eq_value, Number.constant, Number.sub, Number.length, Code.eval,
    nextBody, rawFrame, bit, List.length_drop, Bool.or_eq_true, decide_eq_true_eq,
    List.append_assoc, List.cons_append, List.nil_append]
  rfl

variable (G : Game)

noncomputable section

/-- Parse the top frame of the state word, query the game, and rebuild the stack. -/
def nextCode : Code Bool :=
  .bind (dropCode true (.constant 2))
  (.bind (leadingOnes none).code
  (.bind (dropCode (some none) ((Number.length none).add (.constant 1)))
  (.bind (leadingOnes none).code
  (.bind (dropCode (some none) ((Number.length none).add (.constant 1)))
  (.bind (leadingOnes none).code
  (.bind (dropCode (some none) ((Number.length none).add (.constant 1)))
  (.bind (takeCode (.length (some none)) none)
  (.bind (dropCode (some none) (.length (some (some none))))
  (.bind ((Number.polynomial G.arity (.length (some (some (some (some (some (some (some (some (some false))))))))))).sub (.length (some (some (some (some (some none))))))).code
  (.bind (G.succCode.rename (fun i => match i with
      | .instance => (some (some (some (some (some (some (some (some (some (some false))))))))))
      | .position => some (some none)
      | .index => none))
  (nextBodyCode (Number.polynomial G.arity (.length (some (some (some (some (some (some (some (some (some (some (some false))))))))))))) (.length (some (some (some (some (some (some (some (some (some none))))))))))
    (.length (some (some (some (some (some (some (some none)))))))) (some (some (some (some (some (some (some (some (some (some (some true))))))))))) (some (some (some (some (some (some (some (some (some (some none)))))))))) (some (some (some none))) (some (some none)) none)))))))))))

theorem nextCode_eval (w s : Word) :
    (nextCode G).eval (fun b => if b then s else w) = nextWord G w s := by
  simp only [nextCode, eval_bind, Number.correct, dropCode_eval, leadingOnes_value, takeCode_eval,
    Game.succCode_rename_eval, nextBodyCode_eval, extend, Option.elim_none, Option.elim_some,
    List.length_replicate, Bool.false_eq_true, ↓reduceIte]
  simp only [Number.polynomial_value, Number.sub, Number.length, Number.add, Number.constant,
    List.length_replicate, extend, Option.elim_none, Option.elim_some, Bool.false_eq_true,
    ↓reduceIte, G.succ_eval]
  rfl

/-- The initial search state, or the rejecting final state when `w` is not an instance. -/
def initialWord (w : Word) : Word :=
  match G.start w with
  | none => [true, false]
  | some p => [false, false] ++ rawFrame (G.length.eval w.length + 1) (G.arity.eval w.length) p

def initialCode : Code Bool :=
  .bind (G.startCode.rename (fun _ => false))
    (Code.when (Test.eq (.length none) (.constant 0)) (.literal [true, false])
      (.append (.literal [false, false])
        (frameCode ((Number.polynomial G.length (.length (some false))).add (.constant 1))
          (Number.polynomial G.arity (.length (some false)))
          ((Number.length none).sub (.constant 1)) (dropCode none (.constant 1)))))

theorem initialCode_eval (w s : Word) :
    (initialCode G).eval (fun b => if b then s else w) = initialWord G w := by
  simp only [initialCode, eval_bind, Game.startCode_rename_eval, Code.eval_when, eval_append,
    frameCode_eval, dropCode_eval, Test.eq_value, Number.length, Number.constant, Number.add,
    Number.sub, Number.polynomial_value, Code.eval, extend, Option.elim_none, Option.elim_some,
    Bool.false_eq_true, ↓reduceIte, List.length_replicate]
  rcases hs : G.start w with _ | p <;> simp [initialWord, hs, optionWord, rawFrame]

/-- One transition of the search machine: build the initial state from the empty state word,
otherwise perform a depth-first step. -/
def driverCode : Code Bool :=
  Code.when (Test.eq (.length true) (.constant 0)) (initialCode G) (nextCode G)

theorem driverCode_initial (w : Word) :
    (driverCode G).eval (fun b => if b then [] else w) = initialWord G w := by
  rw [driverCode, Code.eval_when]
  simp [Test.eq_value, Number.length, Number.constant, initialCode_eval]

theorem driverCode_next (w s : Word) (hs : s ≠ []) :
    (driverCode G).eval (fun b => if b then s else w) = nextWord G w s := by
  rw [driverCode, Code.eval_when]
  simp [Test.eq_value, Number.length, Number.constant, hs, nextCode_eval]

end

end Complexity.Games.StepCode
