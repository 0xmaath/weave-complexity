/-
Milestone 2: binary encoding of QBFs and the language TQBF.

A formula with `n` quantifiers and a matrix of `N` nodes is written as
`1^n 0 · 1^N 0 · 1^W 0 · prefix · rec_0 ⋯ rec_{N-1}`, where `W = n + N + 1` is the width of the
numeric fields and the matrix is listed in postorder: each record `rec_j` is two tag bits
(`00` variable, `10` negation, `01` conjunction, `11` disjunction) followed by one numeric
field `1^f 0^{W-f}` holding the variable index for a leaf and the size of the subtree rooted
at `j` otherwise. In postorder the right operand of node `j` is node `j-1` and the left operand
is node `j - 1 - size(j-1)`, so the tree is determined by the sizes alone; `valid` checks
exactly these local consistency conditions, and `decode` reads the tree back.

`TQBF` is the set of words that decode to a true formula. Every closed formula has a word
(`decode_encode`), and every valid word decodes to a closed formula (`decode_closed`).
-/
import Complexity.QBF.Syntax

namespace Complexity.QBF

open Complexity.Classes.PolynomialTime

/-- The number of leading `true`s. -/
def readUnary (w : Word) : ℕ := (w.takeWhile id).length

def bit (w : Word) (i : ℕ) : Bool := (w[i]?).getD false

/-! ### Header and records -/

def vars (w : Word) : ℕ := readUnary w
def afterVars (w : Word) : Word := w.drop (vars w + 1)
def nodes (w : Word) : ℕ := readUnary (afterVars w)
def afterNodes (w : Word) : Word := (afterVars w).drop (nodes w + 1)
def width (w : Word) : ℕ := readUnary (afterNodes w)
def body (w : Word) : Word := (afterNodes w).drop (width w + 1)
def prefixWord (w : Word) : Word := (body w).take (vars w)
def records (w : Word) : Word := (body w).drop (vars w)

/-- Length of one record. -/
def recordLength (W : ℕ) : ℕ := W + 2

/-- Tag bits of node `j` (`tag0`, `tag1`). -/
def tag0 (rs : Word) (W j : ℕ) : Bool := bit rs (j * recordLength W)
def tag1 (rs : Word) (W j : ℕ) : Bool := bit rs (j * recordLength W + 1)
/-- The numeric field of node `j`: leading ones after the tag bits. -/
def field (rs : Word) (W j : ℕ) : ℕ := readUnary (rs.drop (j * recordLength W + 2))

/-- Node kinds: `(tag0, tag1) = (false, false)` variable, `(true, false)` negation,
`(false, true)` conjunction, `(true, true)` disjunction. -/
def isVar (rs : Word) (W j : ℕ) : Bool := !tag0 rs W j && !tag1 rs W j
def isNot (rs : Word) (W j : ℕ) : Bool := tag0 rs W j && !tag1 rs W j
def isAnd (rs : Word) (W j : ℕ) : Bool := !tag0 rs W j && tag1 rs W j
def isOr (rs : Word) (W j : ℕ) : Bool := tag0 rs W j && tag1 rs W j

/-- The subtree size recorded at node `j` (a leaf has size one). -/
def sizeAt (rs : Word) (W j : ℕ) : ℕ := if isVar rs W j then 1 else field rs W j

/-- Right operand `j - 1` and left operand `j - 1 - size(j-1)` of a binary node. -/
def rightChild (j : ℕ) : ℕ := j - 1
def leftChild (rs : Word) (W j : ℕ) : ℕ := j - 1 - sizeAt rs W (j - 1)

/-! ### Validity -/

/-- The field window of node `j` is exactly `1^f 0^{W-f}` with `f < W`. -/
def fieldCanonical (rs : Word) (W j : ℕ) : Bool :=
  decide (field rs W j < W) &&
    (List.range W).all fun i => bit rs (j * recordLength W + 2 + i) == decide (i < field rs W j)

/-- Local consistency of node `j` in a table with `n` variables. -/
def nodeValid (rs : Word) (n W j : ℕ) : Bool :=
  fieldCanonical rs W j &&
    if isVar rs W j then decide (field rs W j < n)
    else if isNot rs W j then decide (1 ≤ j) && decide (field rs W j = sizeAt rs W (j - 1) + 1)
    else decide (1 ≤ j) && decide (sizeAt rs W (j - 1) < j) &&
      decide (field rs W j = sizeAt rs W (j - 1 - sizeAt rs W (j - 1)) + sizeAt rs W (j - 1) + 1)

/-- A word is a valid formula encoding. -/
def valid (w : Word) : Bool :=
  decide (vars w < w.length) && decide (nodes w < (afterVars w).length) &&
    decide (width w < (afterNodes w).length) &&
    decide ((body w).length = vars w + nodes w * recordLength (width w)) &&
    decide (1 ≤ nodes w) && decide (sizeAt (records w) (width w) (nodes w - 1) = nodes w) &&
    (List.range (nodes w)).all fun j => nodeValid (records w) (vars w) (width w) j

/-! ### Decoding -/

/-- Read the tree rooted at node `j`; guards keep the recursion well founded, and their
failure (impossible on valid words) yields a default leaf. -/
def decodeNode (rs : Word) (W : ℕ) : ℕ → Expr
  | j =>
    if isVar rs W j then .var (field rs W j)
    else if h1 : 1 ≤ j then
      if isNot rs W j then .not (decodeNode rs W (j - 1))
      else if h2 : sizeAt rs W (j - 1) < j then
        if isAnd rs W j then
          .and (decodeNode rs W (j - 1 - sizeAt rs W (j - 1))) (decodeNode rs W (j - 1))
        else .or (decodeNode rs W (j - 1 - sizeAt rs W (j - 1))) (decodeNode rs W (j - 1))
      else .var 0
    else .var 0
termination_by j => j
decreasing_by all_goals omega

def decode (w : Word) : Option Formula :=
  if valid w then some ⟨prefixWord w, decodeNode (records w) (width w) (nodes w - 1)⟩ else none

/-- **TQBF**: the words that decode to a true quantified Boolean formula. -/
def TQBF : Language := {w | ∃ φ : Formula, decode w = some φ ∧ φ.IsTrue}

theorem mem_TQBF_iff (w : Word) : w ∈ TQBF ↔ ∃ φ : Formula, decode w = some φ ∧ φ.IsTrue := Iff.rfl

/-! ### Encoding -/

/-- `1^f 0^{W-f}`. -/
def fieldWord (W f : ℕ) : Word := List.replicate f true ++ List.replicate (W - f) false

def record (t0 t1 : Bool) (W f : ℕ) : Word := t0 :: t1 :: fieldWord W f

/-- The postorder record table of a matrix. -/
def Expr.records (W : ℕ) : Expr → Word
  | .var i => record false false W i
  | .not p => p.records W ++ record true false W (p.size + 1)
  | .and p q => p.records W ++ q.records W ++ record false true W (p.size + q.size + 1)
  | .or p q => p.records W ++ q.records W ++ record true true W (p.size + q.size + 1)

/-- The canonical word of a formula, with field width `n + N + 1`. -/
def encode (φ : Formula) : Word :=
  let n := φ.quantifiers.length
  let N := φ.matrix.size
  let W := n + N + 1
  List.replicate n true ++ false :: (List.replicate N true ++ false ::
    (List.replicate W true ++ false :: (φ.quantifiers ++ φ.matrix.records W)))

/-! ### Reading lemmas -/

theorem readUnary_replicate (n : ℕ) (rest : Word) :
    readUnary (List.replicate n true ++ false :: rest) = n := by
  induction n with
  | zero => simp [readUnary]
  | succ n ih =>
    unfold readUnary at ih ⊢
    simp [List.replicate_succ, ih]

theorem drop_replicate (n : ℕ) (rest : Word) :
    (List.replicate n true ++ false :: rest).drop (n + 1) = rest := by
  simp [List.drop_append]

theorem bit_append_right (pre rest : Word) (i : ℕ) : bit (pre ++ rest) (pre.length + i) = bit rest i := by
  simp [bit, List.getElem?_append_right]

theorem drop_append_right (pre rest : Word) (i : ℕ) : (pre ++ rest).drop (pre.length + i) = rest.drop i := by
  simp [List.drop_append]

theorem fieldWord_length (W f : ℕ) (h : f ≤ W) : (fieldWord W f).length = W := by
  simp only [fieldWord, List.length_append, List.length_replicate]; omega

theorem record_length (t0 t1 : Bool) (W f : ℕ) (h : f ≤ W) :
    (record t0 t1 W f).length = recordLength W := by
  simp only [record, List.length_cons, fieldWord_length W f h, recordLength]

theorem readUnary_fieldWord (W f : ℕ) (h : f < W) (post : Word) :
    readUnary (fieldWord W f ++ post) = f := by
  obtain ⟨d, hd⟩ : ∃ d, W - f = d + 1 := ⟨W - f - 1, by omega⟩
  rw [fieldWord, hd, List.replicate_succ, List.append_assoc, List.cons_append]
  exact readUnary_replicate f _

theorem bit_fieldWord (W f : ℕ) (h : f < W) (post : Word) (i : ℕ) (hi : i < W) :
    bit (fieldWord W f ++ post) i = decide (i < f) := by
  unfold bit fieldWord
  by_cases hif : i < f
  · rw [List.append_assoc, List.getElem?_append_left (by simpa using hif)]
    simp [hif]
  · rw [List.append_assoc, List.getElem?_append_right (by simpa using hif),
      List.getElem?_append_left (by simp; omega)]
    simp [hif]

/-- Reading the record of node `j` when it sits at offset `j * recordLength W`. -/
theorem read_record (pre post : Word) (t0 t1 : Bool) (W f j : ℕ) (hf : f < W)
    (hpre : pre.length = j * recordLength W) :
    tag0 (pre ++ (record t0 t1 W f ++ post)) W j = t0 ∧
    tag1 (pre ++ (record t0 t1 W f ++ post)) W j = t1 ∧
    field (pre ++ (record t0 t1 W f ++ post)) W j = f ∧
    fieldCanonical (pre ++ (record t0 t1 W f ++ post)) W j = true := by
  have h0 : tag0 (pre ++ (record t0 t1 W f ++ post)) W j = t0 := by
    unfold tag0
    rw [← hpre, ← Nat.add_zero pre.length, bit_append_right]
    rfl
  have h1 : tag1 (pre ++ (record t0 t1 W f ++ post)) W j = t1 := by
    unfold tag1
    rw [← hpre, bit_append_right]
    rfl
  have hfield : field (pre ++ (record t0 t1 W f ++ post)) W j = f := by
    unfold field
    rw [← hpre, drop_append_right]
    exact readUnary_fieldWord W f hf post
  refine ⟨h0, h1, hfield, ?_⟩
  unfold fieldCanonical
  rw [hfield]
  simp only [hf, decide_true, Bool.true_and, List.all_eq_true, List.mem_range]
  intro i hi
  have hrec : bit (pre ++ (record t0 t1 W f ++ post)) (j * recordLength W + 2 + i) =
      bit (fieldWord W f ++ post) i := by
    rw [← hpre, Nat.add_assoc, bit_append_right, record]
    simp only [bit, show 2 + i = i + 1 + 1 by omega, List.cons_append, List.getElem?_cons_succ]
  rw [hrec, bit_fieldWord W f hf post i hi]
  simp

theorem records_length (n W : ℕ) (hnW : n ≤ W) (M : Expr) (hW : M.size < W) (hb : M.Bounded n) :
    (M.records W).length = M.size * recordLength W := by
  induction M with
  | var i =>
    simp only [Expr.Bounded] at hb
    rw [Expr.records, record_length _ _ _ _ (by omega)]
    simp [Expr.size]
  | not p ih =>
    simp only [Expr.size] at hW
    rw [Expr.records, List.length_append, ih (by omega) hb, record_length _ _ _ _ (by omega)]
    simp only [Expr.size]; ring
  | and p q ihp ihq =>
    simp only [Expr.size] at hW
    rw [Expr.records, List.length_append, List.length_append, ihp (by omega) hb.1, ihq (by omega) hb.2,
      record_length _ _ _ _ (by omega)]
    simp only [Expr.size]; ring
  | or p q ihp ihq =>
    simp only [Expr.size] at hW
    rw [Expr.records, List.length_append, List.length_append, ihp (by omega) hb.1, ihq (by omega) hb.2,
      record_length _ _ _ _ (by omega)]
    simp only [Expr.size]; ring

/-- Unfolding `decodeNode`. -/
theorem decodeNode_eq (rs : Word) (W j : ℕ) : decodeNode rs W j =
    if isVar rs W j then .var (field rs W j)
    else if 1 ≤ j then
      if isNot rs W j then .not (decodeNode rs W (j - 1))
      else if sizeAt rs W (j - 1) < j then
        if isAnd rs W j then
          .and (decodeNode rs W (j - 1 - sizeAt rs W (j - 1))) (decodeNode rs W (j - 1))
        else .or (decodeNode rs W (j - 1 - sizeAt rs W (j - 1))) (decodeNode rs W (j - 1))
      else .var 0
    else .var 0 := by
  rw [decodeNode]
  simp only [dite_eq_ite]

/-- The layout invariant: a matrix laid out from node `s` decodes at its root `s + size - 1`,
records its size there, and satisfies the local validity conditions at every node. -/
theorem layout (n W : ℕ) (hnW : n ≤ W) (M : Expr) (hW : M.size < W) (hb : M.Bounded n) :
    ∀ (pre post : Word) (s : ℕ), pre.length = s * recordLength W →
      decodeNode (pre ++ (M.records W ++ post)) W (s + M.size - 1) = M ∧
      sizeAt (pre ++ (M.records W ++ post)) W (s + M.size - 1) = M.size ∧
      ∀ j, s ≤ j → j < s + M.size → nodeValid (pre ++ (M.records W ++ post)) n W j = true := by
  induction M with
  | var i =>
    intro pre post s hpre
    simp only [Expr.records, Expr.size, Nat.add_sub_cancel]
    simp only [Expr.Bounded] at hb
    obtain ⟨h0, h1, hf, hc⟩ := read_record pre post false false W i s (by omega) hpre
    have hv : isVar (pre ++ (record false false W i ++ post)) W s = true := by simp [isVar, h0, h1]
    refine ⟨?_, ?_, ?_⟩
    · rw [decodeNode_eq, if_pos hv, hf]
    · simp [sizeAt, hv]
    · intro j hj1 hj2
      have hj : j = s := by omega
      subst hj
      simp [nodeValid, hc, hv, hf, hb]
  | not p ih =>
    intro pre post s hpre
    simp only [Expr.size] at hW
    have hpW : p.size < W := by omega
    have hpb : p.Bounded n := hb
    have hpos := Expr.size_pos p
    set rec := record true false W (p.size + 1) with hrec
    simp only [Expr.records, Expr.size, List.append_assoc]
    obtain ⟨hdec, hsize, hval⟩ := ih hpW hpb pre (rec ++ post) s hpre
    have hlen : (pre ++ p.records W).length = (s + p.size) * recordLength W := by
      rw [List.length_append, hpre, records_length n W hnW p hpW hpb]; ring
    obtain ⟨h0, h1, hf, hc⟩ := read_record (pre ++ p.records W) post true false W (p.size + 1)
      (s + p.size) (by omega) hlen
    simp only [List.append_assoc] at h0 h1 hf hc
    set rs := pre ++ (p.records W ++ (rec ++ post)) with hrs
    have hroot : s + (p.size + 1) - 1 = s + p.size := by omega
    have hnv : isVar rs W (s + p.size) = false := by simp [isVar, h0, h1]
    have hnn : isNot rs W (s + p.size) = true := by simp [isNot, h0, h1]
    refine ⟨?_, ?_, ?_⟩
    · rw [hroot, decodeNode_eq, if_neg (by simp [hnv]), if_pos (by omega), if_pos hnn, hdec]
    · rw [hroot]; simp [sizeAt, hnv, hf]
    · intro j hj1 hj2
      by_cases hjr : j = s + p.size
      · subst hjr
        simp only [nodeValid, hc, hnv, hnn, Bool.true_and, Bool.false_eq_true, ↓reduceIte,
          Bool.and_eq_true, decide_eq_true_eq]
        exact ⟨by omega, by rw [hf, hsize]⟩
      · exact hval j hj1 (by omega)
  | and p q ihp ihq =>
    intro pre post s hpre
    simp only [Expr.size] at hW
    have hpW : p.size < W := by omega
    have hqW : q.size < W := by omega
    have hpb : p.Bounded n := hb.1
    have hqb : q.Bounded n := hb.2
    have hpos := Expr.size_pos p
    have hqos := Expr.size_pos q
    set rec := record false true W (p.size + q.size + 1) with hrec
    simp only [Expr.records, Expr.size, List.append_assoc]
    obtain ⟨hdecp, hsizep, hvalp⟩ := ihp hpW hpb pre (q.records W ++ (rec ++ post)) s hpre
    have hlenp : (pre ++ p.records W).length = (s + p.size) * recordLength W := by
      rw [List.length_append, hpre, records_length n W hnW p hpW hpb]; ring
    obtain ⟨hdecq, hsizeq, hvalq⟩ := ihq hqW hqb (pre ++ p.records W) (rec ++ post) (s + p.size) hlenp
    simp only [List.append_assoc] at hdecq hsizeq hvalq
    have hlenpq : (pre ++ p.records W ++ q.records W).length = (s + p.size + q.size) * recordLength W := by
      rw [List.length_append, hlenp, records_length n W hnW q hqW hqb]; ring
    obtain ⟨h0, h1, hf, hc⟩ := read_record (pre ++ p.records W ++ q.records W) post false true W
      (p.size + q.size + 1) (s + p.size + q.size) (by omega) hlenpq
    simp only [List.append_assoc] at h0 h1 hf hc
    set rs := pre ++ (p.records W ++ (q.records W ++ (rec ++ post))) with hrs
    have hroot : s + (p.size + q.size + 1) - 1 = s + p.size + q.size := by omega
    have hnv : isVar rs W (s + p.size + q.size) = false := by simp [isVar, h0, h1]
    have hnn : isNot rs W (s + p.size + q.size) = false := by simp [isNot, h0, h1]
    have hna : isAnd rs W (s + p.size + q.size) = true := by simp [isAnd, h0, h1]
    have hsq : sizeAt rs W (s + p.size + q.size - 1) = q.size := by
      rw [show s + p.size + q.size - 1 = s + p.size + q.size - 1 from rfl]
      have := hsizeq
      rwa [show s + p.size + q.size - 1 = s + p.size + q.size - 1 from rfl]
    have hleft : s + p.size + q.size - 1 - q.size = s + p.size - 1 := by omega
    refine ⟨?_, ?_, ?_⟩
    · rw [hroot, decodeNode_eq, if_neg (by simp [hnv]), if_pos (by omega), if_neg (by simp [hnn]),
        if_pos (by rw [hsq]; omega), if_pos hna, hsq, hleft, hdecq, hdecp]
    · rw [hroot]; simp [sizeAt, hnv, hf]
    · intro j hj1 hj2
      by_cases hjr : j = s + p.size + q.size
      · subst hjr
        simp only [nodeValid, hc, hnv, hnn, hna, Bool.true_and, Bool.false_eq_true, ↓reduceIte,
          Bool.and_eq_true, decide_eq_true_eq]
        refine ⟨⟨by omega, by rw [hsq]; omega⟩, ?_⟩
        rw [hf, hsq, hleft, hsizep]
      · by_cases hjp : j < s + p.size
        · exact hvalp j hj1 hjp
        · exact hvalq j (by omega) (by omega)
  | or p q ihp ihq =>
    intro pre post s hpre
    simp only [Expr.size] at hW
    have hpW : p.size < W := by omega
    have hqW : q.size < W := by omega
    have hpb : p.Bounded n := hb.1
    have hqb : q.Bounded n := hb.2
    have hpos := Expr.size_pos p
    have hqos := Expr.size_pos q
    set rec := record true true W (p.size + q.size + 1) with hrec
    simp only [Expr.records, Expr.size, List.append_assoc]
    obtain ⟨hdecp, hsizep, hvalp⟩ := ihp hpW hpb pre (q.records W ++ (rec ++ post)) s hpre
    have hlenp : (pre ++ p.records W).length = (s + p.size) * recordLength W := by
      rw [List.length_append, hpre, records_length n W hnW p hpW hpb]; ring
    obtain ⟨hdecq, hsizeq, hvalq⟩ := ihq hqW hqb (pre ++ p.records W) (rec ++ post) (s + p.size) hlenp
    simp only [List.append_assoc] at hdecq hsizeq hvalq
    have hlenpq : (pre ++ p.records W ++ q.records W).length = (s + p.size + q.size) * recordLength W := by
      rw [List.length_append, hlenp, records_length n W hnW q hqW hqb]; ring
    obtain ⟨h0, h1, hf, hc⟩ := read_record (pre ++ p.records W ++ q.records W) post true true W
      (p.size + q.size + 1) (s + p.size + q.size) (by omega) hlenpq
    simp only [List.append_assoc] at h0 h1 hf hc
    set rs := pre ++ (p.records W ++ (q.records W ++ (rec ++ post))) with hrs
    have hroot : s + (p.size + q.size + 1) - 1 = s + p.size + q.size := by omega
    have hnv : isVar rs W (s + p.size + q.size) = false := by simp [isVar, h0, h1]
    have hnn : isNot rs W (s + p.size + q.size) = false := by simp [isNot, h0, h1]
    have hna : isAnd rs W (s + p.size + q.size) = false := by simp [isAnd, h0, h1]
    have hsq : sizeAt rs W (s + p.size + q.size - 1) = q.size := hsizeq
    have hleft : s + p.size + q.size - 1 - q.size = s + p.size - 1 := by omega
    refine ⟨?_, ?_, ?_⟩
    · rw [hroot, decodeNode_eq, if_neg (by simp [hnv]), if_pos (by omega), if_neg (by simp [hnn]),
        if_pos (by rw [hsq]; omega), if_neg (by simp [hna]), hsq, hleft, hdecq, hdecp]
    · rw [hroot]; simp [sizeAt, hnv, hf]
    · intro j hj1 hj2
      by_cases hjr : j = s + p.size + q.size
      · subst hjr
        simp only [nodeValid, hc, hnv, hnn, Bool.true_and, Bool.false_eq_true, ↓reduceIte,
          Bool.and_eq_true, decide_eq_true_eq]
        refine ⟨⟨by omega, by rw [hsq]; omega⟩, ?_⟩
        rw [hf, hsq, hleft, hsizep]
      · by_cases hjp : j < s + p.size
        · exact hvalp j hj1 hjp
        · exact hvalq j (by omega) (by omega)

/-! ### Header of an encoded formula -/

theorem encode_header (φ : Formula) :
    vars (encode φ) = φ.quantifiers.length ∧
    nodes (encode φ) = φ.matrix.size ∧
    width (encode φ) = φ.quantifiers.length + φ.matrix.size + 1 ∧
    body (encode φ) = φ.quantifiers ++ φ.matrix.records (φ.quantifiers.length + φ.matrix.size + 1) := by
  simp only [encode, vars, afterVars, nodes, afterNodes, width, body, readUnary_replicate,
    drop_replicate, and_self]

theorem encode_prefix_records (φ : Formula) :
    prefixWord (encode φ) = φ.quantifiers ∧
    records (encode φ) = φ.matrix.records (φ.quantifiers.length + φ.matrix.size + 1) := by
  obtain ⟨hn, _, _, hb⟩ := encode_header φ
  simp [prefixWord, records, hb, hn]

theorem encode_valid (φ : Formula) (hc : φ.Closed) : valid (encode φ) = true := by
  obtain ⟨hn, hN, hW, hb⟩ := encode_header φ
  obtain ⟨hpref, hrec⟩ := encode_prefix_records φ
  have hpos := Expr.size_pos φ.matrix
  have hrl := records_length φ.quantifiers.length (φ.quantifiers.length + φ.matrix.size + 1)
    (by omega) φ.matrix (by omega) hc
  obtain ⟨hdec, hsize, hval⟩ := layout φ.quantifiers.length (φ.quantifiers.length + φ.matrix.size + 1)
    (by omega) φ.matrix (by omega) hc [] [] 0 (by simp)
  simp only [List.nil_append, List.append_nil, Nat.zero_add] at hdec hsize hval
  have h1 : vars (encode φ) < (encode φ).length := by
    rw [hn]; simp only [encode, List.length_append, List.length_cons, List.length_replicate]; omega
  have h2 : nodes (encode φ) < (afterVars (encode φ)).length := by
    rw [hN, afterVars, hn]
    simp only [encode, drop_replicate, List.length_append, List.length_cons, List.length_replicate]
    omega
  have h3 : width (encode φ) < (afterNodes (encode φ)).length := by
    rw [hW, afterNodes, afterVars, hn, hN]
    simp only [encode, drop_replicate, List.length_append, List.length_cons, List.length_replicate]
    omega
  have h4 : (body (encode φ)).length =
      vars (encode φ) + nodes (encode φ) * recordLength (width (encode φ)) := by
    rw [hb, hn, hN, hW, List.length_append, hrl]
  have h5 : 1 ≤ nodes (encode φ) := by rw [hN]; exact hpos
  have h6 : sizeAt (records (encode φ)) (width (encode φ)) (nodes (encode φ) - 1) = nodes (encode φ) := by
    rw [hrec, hW, hN]; exact hsize
  have h7 : ∀ j ∈ List.range (nodes (encode φ)),
      nodeValid (records (encode φ)) (vars (encode φ)) (width (encode φ)) j = true := by
    intro j hj
    rw [hrec, hn, hW]
    rw [hN, List.mem_range] at hj
    exact hval j (Nat.zero_le _) hj
  simp only [valid, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
  exact ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩

/-- Every closed formula is encoded by its canonical word. -/
theorem decode_encode (φ : Formula) (hc : φ.Closed) : decode (encode φ) = some φ := by
  obtain ⟨hn, hN, hW, hb⟩ := encode_header φ
  obtain ⟨hpref, hrec⟩ := encode_prefix_records φ
  obtain ⟨hdec, _, _⟩ := layout φ.quantifiers.length (φ.quantifiers.length + φ.matrix.size + 1)
    (by omega) φ.matrix (by omega) hc [] [] 0 (by simp)
  simp only [List.nil_append, List.append_nil, Nat.zero_add] at hdec
  simp only [decode, encode_valid φ hc, ↓reduceIte, hpref, hrec, hW, hN, hdec]

/-! ### Decoded formulas are closed -/

theorem decodeNode_bounded (rs : Word) (n W N : ℕ)
    (hval : ∀ j, j < N → nodeValid rs n W j = true) :
    ∀ j, j < N → (decodeNode rs W j).Bounded n := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hj
    have hv := hval j hj
    rw [decodeNode_eq]
    by_cases hvar : isVar rs W j = true
    · rw [if_pos hvar]
      simp only [nodeValid, hvar, ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq] at hv
      exact hv.2
    · rw [if_neg hvar]
      split
      · rename_i h1
        by_cases hnot : isNot rs W j = true
        · rw [if_pos hnot]
          exact ih (j - 1) (by omega) (by omega)
        · rw [if_neg hnot]
          split
          · rename_i h2
            split
            · exact ⟨ih _ (by omega) (by omega), ih _ (by omega) (by omega)⟩
            · exact ⟨ih _ (by omega) (by omega), ih _ (by omega) (by omega)⟩
          · simp only [nodeValid, hvar, hnot, Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true,
              decide_eq_true_eq] at hv
            omega
      · simp only [nodeValid, hvar, Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true,
          decide_eq_true_eq] at hv
        split at hv <;> simp only [Bool.and_eq_true, decide_eq_true_eq] at hv <;> omega

theorem decode_closed {w : Word} {φ : Formula} (h : decode w = some φ) : φ.Closed := by
  unfold decode at h
  split at h
  · rename_i hv
    simp only [Option.some.injEq] at h
    subst h
    simp only [valid, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at hv
    obtain ⟨⟨⟨⟨⟨⟨_, _⟩, _⟩, hlen⟩, hpos⟩, _⟩, hval⟩ := hv
    have hpl : (prefixWord w).length = vars w := by
      simp only [prefixWord, List.length_take]
      rw [hlen]
      exact Nat.min_eq_left (Nat.le_add_right _ _)
    show (decodeNode (records w) (width w) (nodes w - 1)).Bounded (prefixWord w).length
    rw [hpl]
    exact decodeNode_bounded (records w) (vars w) (width w) (nodes w) hval (nodes w - 1) (by omega)
  · exact absurd h (by simp)

end Complexity.QBF
