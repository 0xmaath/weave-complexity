/-
Ported from https://github.com/EdouardBonnet/classical-complexity (Lax submission lax-434930, commit 0c0840319318),
file `proofs/Lax434930Proofs/SavitchProofs/QueryRegisters.lean`.
Original authors: Édouard Bonnet, Codex 5.6 and 6. Licensed under the Apache License, Version 2.0;
see `LICENSES/classical-complexity.LICENSE`. Modifications for this port: module and namespace
renamed from `Lax434930Proofs.SavitchProofs.QueryRegisters` to `Complexity.ClassicalProofs.SavitchProofs.QueryRegisters`; concept-package `axiom` statements
replaced by `alias`es of their proofs; imports adjusted accordingly.
-/
import Complexity.ClassicalProofs.SavitchProofs.EncodedGraph
import Complexity.ClassicalProofs.SavitchProofs.BitDecoder
import Complexity.ClassicalProofs.SavitchProofs.InputParser
import Complexity.ClassicalProofs.SavitchProofs.SearchRegisters

set_option backward.isDefEq.respectTransparency false

namespace Complexity.ClassicalProofs.SavitchProofs.GraphQuery

open Complexity.Classical.PolynomialTime Complexity.Classical.SpaceMachines
open ConfigurationWords
open scoped Classical

noncomputable section

inductive Scratch where
  | left | right | temporary | reverse | counter | aux
  | constructorLeft | constructorRight | bound
  deriving DecidableEq, Fintype

structure State (M : Machine) where
  buffer : BitDecoder.Buffer (Payload M)
  parser : InputParser.State
  automaton : Set (PatternAutomata.Suffix (graphPatterns M))
  deriving Fintype

def initial (M : Machine) : State M :=
  ⟨BitDecoder.empty _, InputParser.start, (PatternAutomata.machine (graphPatterns M)).start⟩

abbrev Beta (M : Machine) (BΓ : Type) := Sum BΓ (Letter M)
abbrev Alphabet (M : Machine) (BΓ : Type) := SearchProgram.Alphabet (Beta M BΓ)
abbrev Key := SearchProgram.Key Scratch
abbrev User (M : Machine) := SearchProgram.Control (State M)
abbrev Context (M : Machine) (BΓ : Type) := SearchProgram.Context (Beta M BΓ) (State M)
abbrev Data (M : Machine) (BΓ : Type) := SearchProgram.Data (Beta M BΓ) (State M) Scratch
abbrev Macro (M : Machine) (BΓ : Type) := StackMacros.Macro Key (Alphabet M BΓ) (User M)

def key (r : Scratch) : Key := .inr r

def letter {M : Machine} {BΓ : Type} (x : Letter M) : Alphabet M BΓ := .inl (.inr x)
def readLetter {M : Machine} {BΓ : Type} : Alphabet M BΓ → Letter M
  | .inl (.inr x) => x
  | _ => .inr .invalid

@[simp] lemma readLetter_letter {M : Machine} {BΓ : Type} (x : Letter M) :
    readLetter (letter (BΓ := BΓ) x) = x := rfl

def setBuffer {M : Machine} (s : User M) (buf : BitDecoder.Buffer (Payload M)) : User M :=
  {s with query := {s.query with buffer := buf}}

def setParser {M : Machine} (s : User M) (p : InputParser.State) : User M :=
  {s with query := {s.query with parser := p}}

def setAutomaton {M : Machine} (s : User M) (q : Set (PatternAutomata.Suffix (graphPatterns M))) : User M :=
  {s with query := {s.query with automaton := q}}

end

end Complexity.ClassicalProofs.SavitchProofs.GraphQuery
