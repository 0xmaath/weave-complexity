/-
Ported from https://github.com/EdouardBonnet/cook-levin (Lax submission lax-429075, commit 905f2da2698d),
file `proofs/Lax429075Proofs/WindowPositions.lean`.
Original authors: Édouard Bonnet, Codex 5.6 and 6. Licensed under the Apache License, Version 2.0;
see `LICENSES/cook-levin.LICENSE`. Modifications for this port: module and namespace
renamed from `Lax429075Proofs.WindowPositions` to `Complexity.CookLevinProofs.WindowPositions`; concept-package `axiom` statements
replaced by `alias`es of their proofs; imports adjusted accordingly.
-/
import Complexity.CookLevinProofs.TapeWindow

namespace Complexity.CookLevinProofs.WindowMachine

open AbsoluteTape

abbrev Position (radius : ℕ) := Fin (2 * radius + 1)

def coordinate (radius : ℕ) (i : Position radius) : ℤ := (i.val : ℤ) - radius

def position (radius : ℕ) (j : ℤ) : Position radius :=
  ⟨(j + radius).toNat % (2 * radius + 1), Nat.mod_lt _ (by omega)⟩

lemma coordinate_inside (radius : ℕ) (i : Position radius) : Inside radius (coordinate radius i) := by
  have h := i.isLt
  dsimp [Inside, coordinate]
  omega

lemma coordinate_position (radius : ℕ) (j : ℤ) (h : Inside radius j) :
    coordinate radius (position radius j) = j := by
  have hz : 0 ≤ j + radius := by dsimp [Inside] at h; omega
  have ht : (j + radius).toNat < 2 * radius + 1 := by dsimp [Inside] at h; omega
  simp only [coordinate, position, Nat.mod_eq_of_lt ht]
  omega

lemma position_coordinate (radius : ℕ) (i : Position radius) :
    position radius (coordinate radius i) = i := by
  apply Fin.ext
  simp [position, coordinate, Nat.mod_eq_of_lt i.isLt]

lemma coordinate_injective (radius : ℕ) : Function.Injective (coordinate radius) := by
  intro i j h
  have he := congrArg (position radius) h
  simpa only [position_coordinate] using he

end Complexity.CookLevinProofs.WindowMachine
