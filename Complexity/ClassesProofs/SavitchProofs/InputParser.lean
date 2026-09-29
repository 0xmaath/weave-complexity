/-
Ported from https://github.com/EdouardBonnet/classical-complexity (Lax submission lax-434930, commit 0c0840319318),
file `proofs/Lax434930Proofs/SavitchProofs/InputParser.lean`.
Original authors: Édouard Bonnet, Codex 5.6 and 6. Licensed under the Apache License, Version 2.0;
see `LICENSES/classical-complexity.LICENSE`. Modifications for this port: module and namespace
renamed from `Lax434930Proofs.SavitchProofs.InputParser` to `Complexity.ClassesProofs.SavitchProofs.InputParser`; concept-package `axiom` statements
replaced by `alias`es of their proofs; imports adjusted accordingly.
-/
import Complexity.ClassesProofs.SavitchProofs.ConfigurationWords
import Complexity.ClassesProofs.SavitchProofs.StackTransducer

set_option backward.isDefEq.respectTransparency false

namespace Complexity.ClassesProofs.SavitchProofs.InputParser

open Complexity.Classes.SpaceMachines ConfigurationWords
open StackTransducer (run)
open scoped Classical

noncomputable section

inductive Mode where
  | header | field | rest
  deriving DecidableEq, Fintype

structure State where
  mode : Mode
  desired : InputSymbol
  deriving Fintype

def start : State := ⟨.header, .leftEnd⟩

def readBit (M : Machine) : Letter M → Bool
  | .inr (.bit b) => b
  | _ => false

def step (M : Machine) (s : State) (x : Letter M) : State × Option Bool :=
  match s.mode with
  | .header => match x with
      | .inr (.header _ i) => (⟨.field, i⟩, none)
      | _ => (⟨.rest, .leftEnd⟩, none)
  | .field => if x = split M then (⟨.rest, s.desired⟩, none) else (s, some (readBit M x))
  | .rest => (s, none)

lemma run_rest (M : Machine) (i : InputSymbol) (xs : List (Letter M)) :
    run (step M) ⟨.rest, i⟩ xs = (⟨.rest, i⟩, []) := by
  induction xs <;> simp [run, step, *]

lemma run_field (M : Machine) (i : InputSymbol) (xs : List (Letter M)) :
    (run (step M) ⟨.field, i⟩ xs).1.desired = i ∧
      (run (step M) ⟨.field, i⟩ xs).2 =
        (xs.takeWhile (fun x => decide (x ≠ split M))).map (readBit M) := by
  induction xs with
  | nil => simp [run]
  | cons x xs ih =>
    by_cases hx : x = split M
    · simp [run, step, hx, run_rest]
    · simp [run, step, hx, ih.1, ih.2]

lemma run_correct (M : Machine) (xs : List (Letter M)) :
    (run (step M) start xs).1.desired = desiredInput M xs ∧
      (run (step M) start xs).2 = inputBits M xs := by
  cases xs with
  | nil => simp [run, start, desiredInput, inputBits]
  | cons x xs =>
    cases x with
    | inl b => simp [run, step, start, run_rest, desiredInput, inputBits]
    | inr a =>
      cases a with
      | header q i =>
        simpa only [run, step, start, Option.toList_none, List.nil_append, desiredInput, inputBits,
          List.head?_cons, List.tail_cons, readBit] using! run_field M i xs
      | bit b => simp [run, step, start, run_rest, desiredInput, inputBits]
      | split => simp [run, step, start, run_rest, desiredInput, inputBits]
      | cell g h => simp [run, step, start, run_rest, desiredInput, inputBits]
      | invalid => simp [run, step, start, run_rest, desiredInput, inputBits]

end

end Complexity.ClassesProofs.SavitchProofs.InputParser
