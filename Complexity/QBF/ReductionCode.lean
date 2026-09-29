/-
Milestone 2: the reduction from the signed-CNF language to TQBF as a word program.

`reductionCode` reads a signed-CNF word (the positive-CNF formula-word format of the ported
tree: unary variable count `4r`, unary clause count `m`, then the `m × 4r` incidence matrix)
and emits `encode (translate r F)`, the canonical word of the translated QBF, record by
record: the header, the alternating prefix, and the postorder record table of the uniform
gadget matrix. Words that are not signed-CNF words, and the degenerate case `r = 0`, are sent
to fixed true or false instances. `reduction_polynomial` is the resulting Karp reduction,
with the polynomial-time machine supplied by the ported `code_polynomial_time`.
-/
import Complexity.QBF.Reduction
import Complexity.QBF.GameCode
import Complexity.ArcKaylesProofs.ByskovPolynomial

namespace Complexity.QBF.ReductionCode

open Complexity.Classes.PolynomialTime
open Complexity.ClassesProofs.InclusionAux.TimeHelpers.Streaming
open Complexity.ArcKaylesProofs (inputVars inputClauses inputMatrix afterVars header_of_parse
  parseFormula_word clausesBits_get clauseBits)
open Complexity.ArcKaylesProofs.MachineCode (withHeader withHeader_eval headerEnv nIndex mIndex
  tailIndex wordIndex eval_bind HeaderContext)
open Complexity.ArcKaylesProofs.Byskov
open Complexity.QBF.Reduction
open Complexity.QBF.GameCode

theorem flatMap_congr {l : List ℕ} {f g : ℕ → Word} (h : ∀ x ∈ l, f x = g x) :
    l.flatMap f = l.flatMap g := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    simp only [List.flatMap_cons, h x List.mem_cons_self,
      ih (fun y hy => h y (List.mem_cons_of_mem _ hy))]

variable {I : Type}

/-! ### Emitting records -/

def zerosCode (n : Number I) : Code I := Code.loop n (.literal [false])

theorem zerosCode_eval (n : Number I) (a : I → Word) :
    (zerosCode n).eval a = List.replicate (n.value a) false := by
  rw [zerosCode, Code.eval_loop]
  generalize n.value a = k
  induction k with
  | zero => simp
  | succ k ih => rw [List.range_succ, List.flatMap_append, ih, List.replicate_succ']; rfl

theorem eval_append (p q : Code I) (a : I → Word) : (Code.append p q).eval a = p.eval a ++ q.eval a := rfl

def recordCode (t0 t1 : Test I) (W f : Number I) : Code I :=
  .append t0.code (.append t1.code (.append f.code (zerosCode (W.sub f))))

theorem recordCode_eval (t0 t1 : Test I) (W f : Number I) (a : I → Word) :
    (recordCode t0 t1 W f).eval a = record (t0.value a) (t1.value a) (W.value a) (f.value a) := by
  simp only [recordCode, eval_append, Test.correct, Number.correct, zerosCode_eval, Number.sub,
    record, fieldWord, List.singleton_append]

/-- The 14 records of a literal gadget. -/
def slotCode (p q : Test I) (u W : Number I) : Code I :=
  let v := recordCode (.constant false) (.constant false) W u
  let nt := recordCode (.constant true) (.constant false) W (.constant 2)
  let a4 := recordCode (.constant false) (.constant true) W (.constant 4)
  .append v (.append v (.append nt (.append a4 (.append v
    (.append (recordCode p (.constant true) W (.constant 6))
    (.append v (.append v (.append nt (.append a4 (.append v (.append nt
    (.append (recordCode q (.constant true) W (.constant 7))
      (recordCode (.constant true) (.constant true) W (.constant 14))))))))))))))

theorem slotCode_eval (p q : Test I) (u W : Number I) (a : I → Word) :
    (slotCode p q u W).eval a = (slot (p.value a) (q.value a) (u.value a)).records (W.value a) := by
  cases hp : p.value a <;> cases hq : q.value a <;>
    simp only [slotCode, eval_append, recordCode_eval, Test.constant, Number.constant, hp, hq, slot,
      branchB, branchC, falseA, Expr.records, Expr.size, Bool.false_eq_true, ↓reduceIte,
      List.append_assoc]

/-! ### Chains -/

/-- Records of the clause chain read from an incidence row. -/
def clauseRecords (n' j n W : ℕ) (bits : Word) : Word :=
  (slot false false 0).records W ++ (List.range n).flatMap fun u =>
    (slot (bit bits (n' * j + 2 * u + 1)) (bit bits (n' * j + 2 * u)) u).records W ++
      record true true W (14 + 15 * (u + 1))

def clauseCode (bits : I) (nPrime j n W : Number I) : Code I :=
  .append (slotCode (.constant false) (.constant false) (.constant 0) W)
    (Code.loop n (.append
      (slotCode
        (Test.input (some bits) ((((nPrime.rename some).mul (j.rename some)).add
          ((Number.constant 2).mul (.length none))).add (.constant 1)))
        (Test.input (some bits) (((nPrime.rename some).mul (j.rename some)).add
          ((Number.constant 2).mul (.length none))))
        (.length none) (W.rename some))
      (recordCode (.constant true) (.constant true) (W.rename some)
        ((Number.constant 14).add ((Number.constant 15).mul ((Number.length none).add (.constant 1)))))))

theorem clauseCode_eval (bits : I) (nPrime j n W : Number I) (a : I → Word) :
    (clauseCode bits nPrime j n W).eval a =
      clauseRecords (nPrime.value a) (j.value a) (n.value a) (W.value a) (a bits) := by
  simp only [clauseCode, eval_append, slotCode_eval, Code.eval_loop, recordCode_eval, Test.input,
    Test.constant, Number.rename, Number.mul, Number.add, Number.constant, Number.length, extend,
    Option.elim_none, Option.elim_some, List.length_replicate, extend_some, Function.comp_apply,
    clauseRecords, bit]

/-- Records of the matrix chain. -/
def matrixRecords (n' m n W Cb : ℕ) (bits : Word) : Word :=
  (slot true true 0).records W ++ (List.range m).flatMap fun j =>
    clauseRecords n' j n W bits ++ record false true W (14 + (j + 1) * (Cb + 1))

def matrixCode (bits : I) (nPrime m n W Cb : Number I) : Code I :=
  .append (slotCode (.constant true) (.constant true) (.constant 0) W)
    (Code.loop m (.append
      (clauseCode (some bits) (nPrime.rename some) (.length none) (n.rename some) (W.rename some))
      (recordCode (.constant false) (.constant true) (W.rename some)
        ((Number.constant 14).add (((Number.length none).add (.constant 1)).mul
          ((Cb.rename some).add (.constant 1)))))))

theorem matrixCode_eval (bits : I) (nPrime m n W Cb : Number I) (a : I → Word) :
    (matrixCode bits nPrime m n W Cb).eval a =
      matrixRecords (nPrime.value a) (m.value a) (n.value a) (W.value a) (Cb.value a) (a bits) := by
  simp only [matrixCode, eval_append, slotCode_eval, Code.eval_loop, clauseCode_eval, recordCode_eval,
    Test.constant, Number.rename, Number.mul, Number.add, Number.constant, Number.length, extend,
    Option.elim_none, Option.elim_some, List.length_replicate, extend_some, Function.comp_apply,
    matrixRecords]

def prefixCode (n : Number I) : Code I :=
  Code.loop n (Test.withValue (Test.eq ((Number.length none).mod (.constant 2)) (.constant 0))
    (fun a => decide ((a none).length % 2 = 0)) (by
      intro a; simp [Test.eq_value, Number.mod, Number.length, Number.constant])).code

theorem prefixCode_eval (n : Number I) (a : I → Word) :
    (prefixCode n).eval a = (List.range (n.value a)).map fun u => decide (u % 2 = 0) := by
  simp only [prefixCode, Code.eval_loop, Test.correct, Test.withValue_value, extend,
    Option.elim_none, List.length_replicate, List.map_eq_flatMap]

/-- The whole output word: header, prefix, matrix. -/
def outCode (bits : I) (nPrime m : Number I) : Code I :=
  let r := nPrime.div (.constant 4)
  let n := (Number.constant 2).mul r
  let Cb := (Number.constant 14).add ((Number.constant 30).mul r)
  let N := (Number.constant 14).add (m.mul (Cb.add (.constant 1)))
  let W := (n.add N).add (.constant 1)
  .append n.code (.append (.literal [false]) (.append N.code (.append (.literal [false])
    (.append W.code (.append (.literal [false])
      (.append (prefixCode n) (matrixCode bits nPrime m n W Cb)))))))

def outWord (n' m : ℕ) (bits : Word) : Word :=
  let r := n' / 4
  let n := 2 * r
  let Cb := 14 + 30 * r
  let N := 14 + m * (Cb + 1)
  let W := n + N + 1
  List.replicate n true ++ false :: (List.replicate N true ++ false :: (List.replicate W true ++ false ::
    (((List.range n).map fun u => decide (u % 2 = 0)) ++ matrixRecords n' m n W Cb bits)))

theorem outCode_eval (bits : I) (nPrime m : Number I) (a : I → Word) :
    (outCode bits nPrime m).eval a = outWord (nPrime.value a) (m.value a) (a bits) := by
  simp only [outCode, eval_append, Number.correct, prefixCode_eval, matrixCode_eval, Code.eval,
    List.singleton_append, List.cons_append, List.nil_append, List.append_assoc]
  simp only [Number.mul, Number.add, Number.div, Number.constant, outWord]

/-! ### The chains as record tables -/

theorem slot_size (p q : Bool) (u : ℕ) : (slot p q u).size = 14 := by
  cases p <;> cases q <;> simp [slot, branchB, branchC, falseA, Expr.size]

theorem or_chain (W : ℕ) (f : ℕ → Expr) (hf : ∀ u, (f u).size = 14) (init : Expr) :
    ∀ k : ℕ,
      ((List.range k).foldl (fun acc u => Expr.or acc (f u)) init).size = init.size + 15 * k ∧
      ((List.range k).foldl (fun acc u => Expr.or acc (f u)) init).records W =
        init.records W ++ (List.range k).flatMap
          (fun u => (f u).records W ++ record true true W (init.size + 15 * (u + 1))) := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    obtain ⟨hs, hr⟩ := ih
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    refine ⟨?_, ?_⟩
    · simp only [Expr.size, hs, hf]
      all_goals ring
    · simp only [Expr.records, hr, hs, hf, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
        List.append_nil, List.append_assoc]
      congr 3

theorem and_chain {α : Type} (W c : ℕ) (f : α → Expr) (init : Expr) :
    ∀ (F : List α) (g : ℕ → Expr), (∀ K ∈ F, (f K).size = c) →
      (∀ j, (h : j < F.length) → g j = f F[j]) →
      (F.foldl (fun acc K => Expr.and acc (f K)) init).size = init.size + F.length * (c + 1) ∧
      (F.foldl (fun acc K => Expr.and acc (f K)) init).records W =
        init.records W ++ (List.range F.length).flatMap
          (fun j => (g j).records W ++ record false true W (init.size + (j + 1) * (c + 1))) := by
  intro F
  induction F using List.reverseRecOn with
  | nil => intro g _ _; simp
  | append_singleton F K ih =>
    intro g hc hg
    have hK : (f K).size = c := hc K (by simp)
    have hgK : g F.length = f K := by
      rw [hg F.length (by simp)]
      simp
    obtain ⟨hs, hr⟩ := ih g (fun K' hK' => hc K' (by simp [hK']))
      (fun j hj => by rw [hg j (by simp; omega)]; simp [List.getElem_append_left hj])
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    refine ⟨?_, ?_⟩
    · simp only [Expr.size, hs, hK, List.length_append, List.length_singleton]
      all_goals ring
    · simp only [Expr.records, hr, hs, hK, List.length_append, List.length_singleton,
        List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil,
        List.append_assoc, hgK]
      rw [show init.size + F.length * (c + 1) + c + 1 = init.size + (F.length + 1) * (c + 1) by ring]

theorem clauseExpr_size (r : ℕ) {r' : ℕ} (K : Finset (SignedLiteral r')) :
    (clauseExpr r K).size = 14 + 30 * r := by
  have := (or_chain 0 (fun u => slot (posIn K u) (negIn K u) u) (fun u => slot_size _ _ _)
    (slot false false 0) (2 * r)).1
  rw [clauseExpr, this, slot_size]; ring

theorem matrixExpr_size (r : ℕ) (F : SignedCNF r) :
    (matrixExpr r F).size = 14 + F.length * (14 + 30 * r + 1) := by
  have := (and_chain 0 (14 + 30 * r) (clauseExpr r) (slot true true 0) F
    (fun j => clauseExpr r (F.getD j ∅)) (fun K _ => clauseExpr_size r K)
    (fun j h => by rw [List.getD_eq_getElem F ∅ h])).1
  rw [matrixExpr, this, slot_size]

theorem clauseExpr_records (r : ℕ) {r' : ℕ} (K : Finset (SignedLiteral r')) (W : ℕ) :
    (clauseExpr r K).records W = (slot false false 0).records W ++ (List.range (2 * r)).flatMap
      (fun u => (slot (posIn K u) (negIn K u) u).records W ++ record true true W (14 + 15 * (u + 1))) := by
  have := (or_chain W (fun u => slot (posIn K u) (negIn K u) u) (fun u => slot_size _ _ _)
    (slot false false 0) (2 * r)).2
  rw [clauseExpr, this, slot_size]

theorem matrixExpr_records (r : ℕ) (F : SignedCNF r) (W : ℕ) (g : ℕ → Expr)
    (hg : ∀ j, (h : j < F.length) → g j = clauseExpr r F[j]) :
    (matrixExpr r F).records W = (slot true true 0).records W ++ (List.range F.length).flatMap
      (fun j => (g j).records W ++ record false true W (14 + (j + 1) * (14 + 30 * r + 1))) := by
  have := (and_chain W (14 + 30 * r) (clauseExpr r) (slot true true 0) F g
    (fun K _ => clauseExpr_size r K) hg).2
  rw [matrixExpr, this, slot_size]

/-! ### Reading incidence bits -/

theorem bits_index {r : ℕ} (F : SignedCNF r) (j v : ℕ) (hj : j < F.length) (hv : v < 4 * r) :
    bit ((matrixFormula F).clauses.flatMap clauseBits) (4 * r * j + v) =
      decide (∃ l ∈ F[j], l.index.val = v) := by
  have hj' : j < (matrixFormula F).clauses.length := by simpa [matrixFormula] using hj
  have h0 := clausesBits_get (matrixFormula F).clauses ⟨j, hj'⟩ ⟨v, hv⟩
  have hidx : (⟨j, hj'⟩ : Fin (matrixFormula F).clauses.length).val * (matrixFormula F).nvars +
      (⟨v, hv⟩ : Fin (4 * r)).val = 4 * r * j + v := by
    change j * (4 * r) + v = 4 * r * j + v
    ring
  rw [hidx] at h0
  have hcl : (matrixFormula F).clauses[(⟨j, hj'⟩ : Fin _)] = Finset.image SignedLiteral.index F[j] :=
    List.getElem_map (f := Finset.image SignedLiteral.index) (l := F)
  have hmem : (⟨v, hv⟩ : Fin (4 * r)) ∈ (matrixFormula F).clauses[(⟨j, hj'⟩ : Fin _)] ↔
      ∃ l ∈ F[j], l.index.val = v := by
    rw [hcl]
    refine Finset.mem_image.trans ?_
    constructor
    · rintro ⟨l, hl, he⟩; exact ⟨l, hl, by rw [he]⟩
    · rintro ⟨l, hl, he⟩; exact ⟨l, hl, Fin.ext he⟩
  unfold bit
  rw [h0, Option.getD_some, decide_eq_decide]
  exact hmem

theorem posIn_bits {r : ℕ} (F : SignedCNF r) (j u : ℕ) (hj : j < F.length) (hu : u < 2 * r) :
    bit ((matrixFormula F).clauses.flatMap clauseBits) (4 * r * j + 2 * u + 1) = posIn F[j] u := by
  rw [show 4 * r * j + 2 * u + 1 = 4 * r * j + (2 * u + 1) by ring, bits_index F j _ hj (by omega)]
  rfl

theorem negIn_bits {r : ℕ} (F : SignedCNF r) (j u : ℕ) (hj : j < F.length) (hu : u < 2 * r) :
    bit ((matrixFormula F).clauses.flatMap clauseBits) (4 * r * j + 2 * u) = negIn F[j] u := by
  rw [bits_index F j _ hj (by omega)]
  rfl

theorem clauseRecords_eq {r : ℕ} (F : SignedCNF r) (j W : ℕ) (hj : j < F.length) :
    clauseRecords (4 * r) j (2 * r) W ((matrixFormula F).clauses.flatMap clauseBits) =
      (clauseExpr r F[j]).records W := by
  rw [clauseRecords, clauseExpr_records]
  congr 1
  apply flatMap_congr
  intro u hu
  rw [posIn_bits F j u hj (List.mem_range.mp hu), negIn_bits F j u hj (List.mem_range.mp hu)]

theorem matrixRecords_eq {r : ℕ} (F : SignedCNF r) (W : ℕ) :
    matrixRecords (4 * r) F.length (2 * r) W (14 + 30 * r) ((matrixFormula F).clauses.flatMap clauseBits) =
      (matrixExpr r F).records W := by
  rw [matrixRecords, matrixExpr_records r F W
    (fun j => clauseExpr r (F.getD j ∅)) (fun j h => by rw [List.getD_eq_getElem F ∅ h])]
  congr 1
  apply flatMap_congr
  intro j hj
  have hj' := List.mem_range.mp hj
  rw [clauseRecords_eq F j W hj', List.getD_eq_getElem F ∅ hj']

theorem outWord_eq {r : ℕ} (F : SignedCNF r) :
    outWord (4 * r) F.length ((matrixFormula F).clauses.flatMap clauseBits) = encode (translate r F) := by
  have hr : 4 * r / 4 = r := by omega
  simp only [outWord, hr, encode, translate, prefixOf_length, matrixExpr_size]
  rw [matrixRecords_eq]
  rfl

/-! ### The reduction -/

def trueInstance : Formula := ⟨[false], .or (.var 0) (.not (.var 0))⟩
def falseInstance : Formula := ⟨[true], .and (.var 0) (.not (.var 0))⟩

theorem trueInstance_mem : encode trueInstance ∈ TQBF := by
  refine ⟨trueInstance, decode_encode _ (by simp [Formula.Closed, trueInstance, Expr.Bounded]), ?_⟩
  simp only [Formula.IsTrue, trueInstance, Holds, Bool.false_eq_true, ↓reduceIte]
  exact ⟨true, by simp [Holds, Expr.eval]⟩

theorem falseInstance_not_mem : encode falseInstance ∉ TQBF := by
  rintro ⟨φ, hd, ht⟩
  rw [decode_encode _ (by simp [Formula.Closed, falseInstance, Expr.Bounded])] at hd
  simp only [Option.some.injEq] at hd
  subst hd
  simp only [Formula.IsTrue, falseInstance, Holds, ↓reduceIte] at ht
  have := ht true
  simp [Holds, Expr.eval] at this

/-- With no rounds, a signed CNF is true exactly when it has no clauses. -/
theorem true_zero (F : SignedCNF 0) : F.True ↔ F = [] := by
  simp only [SignedCNF.True, List.finRange_zero, SignedCNF.TruthFrom, SignedCNF.Satisfied]
  constructor
  · intro h
    cases F with
    | nil => rfl
    | cons K F =>
      obtain ⟨l, _, _⟩ := h K List.mem_cons_self
      exact Fin.elim0 l.round
  · rintro rfl; simp

noncomputable def reductionBody : Code HeaderContext :=
  Code.when signedHeaderTest
    (Code.when (Test.eqP ((Number.length nIndex).div (.constant 4)) (.constant 0))
      (Code.when (Test.eqP (.length mIndex) (.constant 0))
        (.literal (encode trueInstance)) (.literal (encode falseInstance)))
      (outCode none (.length nIndex) (.length mIndex)))
    (.literal (encode falseInstance))

noncomputable def reductionCode : Code Unit := withHeader reductionBody

noncomputable def reduction (w : Word) : Word := reductionCode.eval (fun _ => w)

theorem reduction_word {r : ℕ} (F : SignedCNF r) :
    reduction (signedWord F) =
      if r = 0 then (if F.length = 0 then encode trueInstance else encode falseInstance)
      else encode (translate r F) := by
  have hp := parseFormula_word (matrixFormula F)
  obtain ⟨hn, hm, hb, hv⟩ := header_of_parse hp
  change inputVars (signedWord F) = 4 * r at hn
  change inputClauses (signedWord F) = (matrixFormula F).clauses.length at hm
  change inputMatrix (signedWord F) = (matrixFormula F).clauses.flatMap clauseBits at hb
  have hm' : (matrixFormula F).clauses.length = F.length := by simp [matrixFormula]
  have hs : signedHeader (signedWord F) := ⟨hv, by rw [hn]; omega⟩
  rw [reduction, reductionCode, withHeader_eval]
  unfold reductionBody
  rw [Code.eval_when, (signedHeaderTest_value _).mpr hs]
  simp only [↓reduceIte, Code.eval_when, Test.eqP, Test.withValue_value, Number.div, Number.length,
    Number.constant, decide_eq_true_eq, outCode_eval, Code.eval]
  simp only [headerEnv, nIndex, mIndex, extend, Option.elim_some, Option.elim_none,
    List.length_replicate, hn, hm, hm', hb, outWord_eq]
  have h4 : 4 * r / 4 = r := by omega
  rw [h4]
  simp only [decide_eq_true_eq]

theorem reduction_correct (w : Word) : w ∈ signedLanguage ↔ reduction w ∈ TQBF := by
  by_cases hv : signedHeader w
  · obtain ⟨r, F, rfl⟩ := (signedHeader_iff w).mp hv
    rw [signedWord_mem, reduction_word]
    by_cases hr : r = 0
    · subst hr
      rw [if_pos rfl, true_zero]
      by_cases hF : F.length = 0
      · rw [if_pos hF]; simp [List.length_eq_zero_iff.mp hF, trueInstance_mem]
      · rw [if_neg hF]
        constructor
        · intro h; exact absurd (by simp [h]) hF
        · intro h; exact absurd h falseInstance_not_mem
    · rw [if_neg hr, translate_true, mem_TQBF_iff]
      constructor
      · intro h; exact ⟨_, decode_encode _ (translate_closed r (by omega) F), h⟩
      · rintro ⟨φ, hd, ht⟩
        rw [decode_encode _ (translate_closed r (by omega) F)] at hd
        simp only [Option.some.injEq] at hd
        subst hd; exact ht
  · have hs : signedHeaderTest.value (headerEnv w) = false := by
      apply Bool.eq_false_iff.mpr
      intro ht; exact hv ((signedHeaderTest_value w).mp ht)
    have hn : w ∉ signedLanguage := by
      rintro ⟨r, F, he, _⟩
      exact hv ((signedHeader_iff w).mpr ⟨r, F, he⟩)
    rw [reduction, reductionCode, withHeader_eval]
    unfold reductionBody
    rw [Code.eval_when, hs]
    simp only [Bool.false_eq_true, ↓reduceIte, Code.eval]
    exact ⟨fun h => absurd h hn, fun h => absurd h falseInstance_not_mem⟩

/-- The Karp reduction from the ported PSPACE-hard signed-CNF language to TQBF. -/
theorem reduction_polynomial :
    Complexity.CookLevin.Reductions.ManyOne signedLanguage TQBF :=
  ⟨reduction, Complexity.ArcKaylesProofs.MachineCode.code_polynomial_time reductionCode, reduction_correct⟩

end Complexity.QBF.ReductionCode
