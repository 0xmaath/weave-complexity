/-
Ported from https://github.com/EdouardBonnet/classical-complexity (Lax submission lax-434930, commit 0c0840319318),
file `proofs/Lax434930Proofs/InclusionAux/RadixTape.lean`.
Original authors: Édouard Bonnet, Codex 5.6 and 6. Licensed under the Apache License, Version 2.0;
see `LICENSES/classical-complexity.LICENSE`. Modifications for this port: module and namespace
renamed from `Lax434930Proofs.InclusionAux.RadixTape` to `Complexity.ClassicalProofs.InclusionAux.RadixTape`; concept-package `axiom` statements
replaced by `alias`es of their proofs; imports adjusted accordingly.
-/
import Complexity.ClassicalProofs.ConfigurationTime

namespace Complexity.ClassicalProofs.InclusionAux.RadixTape

open Complexity.Classical.PolynomialTime Complexity.Classical.SpaceMachines

def encode (base : ℕ) : List ℕ → ℕ
  | [] => 0
  | d :: ds => d + base * encode base ds

lemma encode_lt (base : ℕ) (hb : 0 < base) (ds : List ℕ) (hd : ∀ d ∈ ds, d < base) :
    encode base ds < base ^ ds.length := by
  induction ds with
  | nil => simp [encode]
  | cons d ds ih =>
    have hhead := hd d (by simp)
    have htail := ih (fun e he => hd e (by simp [he]))
    simp only [encode, List.length_cons, pow_succ]
    nlinarith

lemma digit_cons (base d : ℕ) (ds : List ℕ) (hb : 0 < base) (hd : d < base) :
    encode base (d :: ds) / base = encode base ds := by
  simp [encode, Nat.add_mul_div_left _ _ hb, Nat.div_eq_of_lt hd]

lemma digit_encode (base : ℕ) (hb : 0 < base) (ds : List ℕ) (hd : ∀ d ∈ ds, d < base) (i : ℕ) :
    encode base ds / base ^ i % base = ds[i]?.getD 0 := by
  induction ds generalizing i with
  | nil => simp [encode]
  | cons d ds ih =>
    cases i with
    | zero => simp [encode, Nat.mod_eq_of_lt (hd d (by simp))]
    | succ i =>
      rw [pow_succ', ← Nat.div_div_eq_div_mul, digit_cons base d ds hb (hd d (by simp))]
      exact ih (fun e he => hd e (by simp [he])) i

lemma digit_zero (base value i : ℕ) (hb : 1 < base) (hv : value ≤ i) :
    value / base ^ i % base = 0 := by
  have hpow : i < base ^ i := Nat.lt_pow_self hb
  simp [Nat.div_eq_of_lt (hv.trans_lt hpow)]

lemma log_power_bound (base c n : ℕ) :
    base ^ (c * Nat.log 2 (n + 2)) ≤ (n + 2) ^ (base * c) := by
  calc
    _ ≤ (2 ^ base) ^ (c * Nat.log 2 (n + 2)) :=
      Nat.pow_le_pow_left (Nat.lt_pow_self (by decide : 1 < (2 : ℕ))).le _
    _ = (2 ^ Nat.log 2 (n + 2)) ^ (base * c) := by
      simp only [← pow_mul]
      congr 1
      ring
    _ ≤ _ := Nat.pow_le_pow_left (Nat.pow_log_le_self 2 (by omega)) _

end Complexity.ClassicalProofs.InclusionAux.RadixTape
