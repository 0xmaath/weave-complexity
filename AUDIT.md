# Semantic audit of the ported definitions

This document walks through every load-bearing definition of the library and
argues, in prose, that it captures the standard textbook meaning
(Arora–Barak, *Computational Complexity: A Modern Approach*; Sipser,
*Introduction to the Theory of Computation*). Wherever the formalization
deviates from, or is weaker than, the textbook notion, the deviation is
flagged explicitly in a **Deviation** or **Weakness** paragraph.

Every Lean snippet below is quoted verbatim from the ported sources
(`Complexity/…`). The three source packages are
[classical-complexity](https://github.com/EdouardBonnet/classical-complexity)
(namespace `Complexity.Classes`),
[cook-levin](https://github.com/EdouardBonnet/cook-levin)
(namespace `Complexity.CookLevin`) and
[arc-kayles](https://github.com/EdouardBonnet/arc-kayles)
(namespace `Complexity.ArcKayles`). Each package has a companion `…Proofs`
namespace holding the proofs.

Scope note. The port is a port: no definition was changed. The only edits are
the namespace renames, the replacement of every concept-package `axiom` by an
`alias` of its proof, the removal of the single "open question" axiom
`P ≠ NP`, and the added attribution headers. `Complexity/StatementCheck.lean`
re-elaborates every original axiom statement against the theorem that now
carries its name, so statement fidelity to the archived sources is
machine-checked, not just asserted here.

---

## 0. Words, languages and classes

```lean
/-- A finite binary string. -/
abbrev Word := List Bool

/-- A language of finite binary strings. -/
abbrev Language := Set Word
```
(`Complexity/Classes/PolynomialTime.lean`)

Every complexity class in the library is a `Set Language`. This is exactly
the textbook setting: languages are sets of finite strings over the binary
alphabet {0,1}, and classes are sets of languages. Complements of languages
(used for coNP, coNL and the complement-closure theorems) are complements
inside `Set Word`, i.e. relative to the set of all finite binary strings, as in
the textbooks. There is no separate input alphabet parameter: everything is
binary, which is Arora–Barak's convention (Sipser allows arbitrary finite
alphabets, but every textbook proof that the choice does not matter is
standard and unneeded here because nothing in the library uses another
alphabet).

---

## 1. The machine model(s)

The library uses two machine models, one for time and one for space. This is
itself a mild deviation from the textbooks, which use one model for both, and
is discussed at the end of this section.

### 1.1 Time: Mathlib's finite stack machines (`FinTM2`)

```lean
/-- Languages whose Boolean characteristic functions are computable in polynomial time. -/
def P : Set Language :=
  {L | ∃ f : Word → Bool,
    (∀ w, f w = true ↔ w ∈ L) ∧
    Nonempty (Turing.TM2ComputableInPolyTime id Computability.encodeBool f)}
```
(`Complexity/Classes/PolynomialTime.lean`)

`Turing.TM2ComputableInPolyTime ea eb f` is Mathlib's bundle of

* a `FinTM2`: a deterministic machine with finitely many stacks (`Fintype K`),
  finitely many function labels (`Fintype Λ`), finitely many internal states
  (`Fintype σ`), a finite input-stack alphabet (`Fintype (Γ k₀)`), and a
  program `m : Λ → TM2.Stmt Γ Λ σ` built from `push`, `peek`, `pop`, `load`,
  `branch`, `goto`, `halt`;
* input/output alphabet equivalences (`inputAlphabet`, `outputAlphabet`);
* a polynomial `time : Polynomial ℕ`;
* a proof `outputsFun` that for every input `a` the machine, started from
  `initList tm (ea a)` (input on stack `k₀`, all other stacks empty, initial
  state, program counter at `main`), reaches `haltList tm (eb (f a))` (program
  counter `none`, output on stack `k₁`, all other stacks empty) in at most
  `time.eval (ea a).length` steps.

With the identity input encoding `ea = id`, the input is the binary word
itself and the time bound is a polynomial in `w.length`. With
`eb = Computability.encodeBool`, the output is one bit. So a language is in P
iff a single deterministic finite machine and a single polynomial exist such
that on every input the machine halts within `p(|w|)` steps with the correct
bit. That is Arora–Barak Definition 1.13 / Sipser Definition 7.12, with the
usual "one machine, one polynomial, for all inputs" quantifier order (the
machine and polynomial are chosen before `∀ w`).

**Why a stack machine is a Turing machine.** A `TM2` with `k` stacks is the
standard "k-pushdown-store machine"; a tape can be simulated by two stacks with
constant overhead and conversely, so polynomial time is the same class on
either. The port does not rely on this folklore: it *proves* the equivalence
with an elementary single-tape Turing machine (section 1.2), which is the
model Sipser uses to define P.

**Weakness: Mathlib's `FinTM2` does not require the non-input stack alphabets
to be finite.** `FinTM2` only has `[Γk₀Fin : Fintype (Γ k₀)]`. A machine whose
work stacks have alphabet `ℕ` is still a `FinTM2`. Because `push k (f : σ → Γ k)`
can only push a symbol determined by the finite internal state, and there are
finitely many statements, only finitely many symbols are ever pushed, so no
computational power is gained; but this is an argument, not a definition. The
port closes the gap by theorem: `FiniteStackP` requires every stack alphabet
to be finite,

```lean
/-- Polynomial-time stack deciders with finite alphabets at every stack. -/
def FiniteStackP : Set Language :=
  {L | ∃ (f : Word → Bool)
    (M : TM2ComputableInPolyTime id Computability.encodeBool f),
    (∀ w, f w = true ↔ w ∈ L) ∧ ∀ k, Finite (M.tm.Γ k)}
```
(`Complexity/Classes/MachineModels.lean`)

and `Complexity.Classes.FiniteStackEquivalence.finiteStackP_eq_P :
FiniteStackP = P` is proved. So P is exactly the class obtained with fully
finite machines.

### 1.2 Time, second presentation: elementary single-tape machines

```lean
/-- A finite elementary single-tape machine, with ordinary binary input. -/
structure SingleTape where
  Γ : Type
  Q : Type
  [alphabet : Fintype Γ]
  [control : Fintype Q]
  [blank : Inhabited Γ]
  [initial : Inhabited Q]
  input : Bool ↪ Γ
  input_ne_blank : ∀ b, input b ≠ default
  transition : TM0.Machine Γ Q
  accept : Q → Bool

/-- The standard single-tape formulation: one machine and one polynomial,
halting on every input, with acceptance exactly matching membership. -/
def SingleTapeP : Set Language :=
  {L | ∃ (M : SingleTape) (p : Polynomial ℕ), ∀ w : Word,
    ∃ c : TM0.Cfg M.Γ M.Q,
      Nonempty (StateTransition.EvalsToInTime (TM0.step M.transition)
        (TM0.init (w.map M.input)) (some c) (p.eval w.length)) ∧
      TM0.step M.transition c = none ∧ (M.accept c.q = true ↔ w ∈ L)}
```
(`Complexity/Classes/MachineModels.lean`)

`TM0.Machine Γ Q` is Mathlib's most elementary Turing machine: a partial
function `Q → Γ → Option (Q × Stmt Γ)` where a statement either moves the head
one cell or writes one symbol. The alphabet and state set are finite; the two
input bits are distinct and distinct from blank (so the end of the input is
detectable); the input is written in order starting under the head; the
machine must reach a halting configuration (`step … c = none`) within
`p(|w|)` steps; the halting state's label gives the answer. This is
precisely Sipser's single-tape deterministic decider, with the standard
quantifier order.

`Complexity.Classes.ModelEquivalence.singleTapeP_eq_P : SingleTapeP = P`
is proved, so the two definitions of P (and hence Sipser's and Arora–Barak's
presentations, modulo the multitape/stack simulations the port proves) agree.

### 1.3 Space: finite machines with a read-only input tape

```lean
/-- The input alphabet, with two distinct endmarkers. -/
inductive InputSymbol
  | leftEnd
  | bit (value : Bool)
  | rightEnd
  deriving DecidableEq, Fintype

/-- An elementary head movement, including staying in place. -/
inductive Move
  | left
  | stay
  | right
  deriving DecidableEq, Fintype

/-- Move a head on a semi-infinite tape, keeping it at zero on a leftward exit. -/
def Move.apply : Move → ℕ → ℕ
  | .left, i => i - 1
  | .stay, i => i
  | .right, i => i + 1

/-- Read the immutable input at a head position, including its endmarkers. -/
def readInput (w : Word) : ℕ → InputSymbol
  | 0 => .leftEnd
  | i + 1 => match w[i]? with
    | some b => .bit b
    | none => .rightEnd

/-- One local transition: change state, write a work symbol, and move the heads. -/
structure Action (Γ Q : Type) where
  state : Q
  write : Γ
  inputMove : Move
  workMove : Move

/-- The complete finite description of a possibly nondeterministic machine. -/
structure Machine where
  Γ : Type
  Q : Type
  [alphabet : Fintype Γ]
  [control : Fintype Q]
  blank : Γ
  start : Q
  transition : Q → InputSymbol → Γ → Finset (Action Γ Q)
  accept : Q → Bool

/-- The two head positions, control state, and work-tape contents. -/
structure Configuration (Γ Q : Type) where
  state : Q
  inputHead : ℕ
  workHead : ℕ
  tape : ℕ → Γ

/-- The work tape is blank; the input is supplied separately to the step relation. -/
def Machine.initial (M : Machine) : M.Config :=
  ⟨M.start, 0, 0, fun _ => M.blank⟩

/-- Execute one action. The input head is clipped to the two endmarkers. -/
def Machine.execute (M : Machine) (w : Word) (c : M.Config)
    (a : Action M.Γ M.Q) : M.Config :=
  ⟨a.state, min (a.inputMove.apply c.inputHead) (w.length + 1),
    a.workMove.apply c.workHead, Function.update c.tape c.workHead a.write⟩

/-- One legal transition consults only the state and the two scanned symbols. -/
def Machine.Step (M : Machine) (w : Word) (c d : M.Config) : Prop :=
  ∃ a ∈ M.transition c.state (readInput w c.inputHead) (c.tape c.workHead),
    d = M.execute w c a

/-- A computation prefix consisting of exactly the indicated number of transitions. -/
inductive Machine.Run (M : Machine) (w : Word) : ℕ → M.Config → Prop
  | zero : M.Run w 0 M.initial
  | succ {n : ℕ} {c d : M.Config} :
      M.Run w n c → M.Step w c d → M.Run w (n + 1) d
```
(`Complexity/Classes/SpaceMachines.lean`)

This is the textbook "offline" machine used to define sublinear space classes
(Sipser §8.4 "read-only input tape"; Arora–Barak §4.1): a finite control, a
finite work alphabet with a blank, a read-only input tape holding the input
between two endmarkers, and a work tape that is initially blank. In one step
the machine reads the control state, the scanned input symbol and the scanned
work symbol, and then changes state, writes one work symbol and moves each
head by at most one cell. Points worth checking against the informal model:

* **Finite description.** `transition : Q → InputSymbol → Γ → Finset (Action Γ Q)`
  with `Fintype Q`, `Fintype Γ`, `Fintype InputSymbol` is a finite table. It
  cannot see head positions, the input length, or any tape cell other than the
  two scanned ones. There is no oracle and no unbounded register.
* **Input tape is really read-only and really bounded.** The input is never
  stored in the configuration; `readInput w` is a function of the immutable
  `w`. The input head is clamped to `[0, |w|+1]` by `min … (w.length + 1)`
  on the right and by truncated subtraction on the left, and the ported lemma
  `Complexity.ClassesProofs.SpaceSemantics.inputHead_le` proves the
  invariant for every run. Without clamping, an unbounded input-head position
  would be a free counter that could break the logarithmic-space classes.
* **Work tape is semi-infinite and initially blank.** The tape is represented
  as `ℕ → Γ`, but the initial tape is the constant blank function and each
  step changes only the scanned cell (`Function.update`), so the function
  representation carries no hidden information;
  `SpaceSemantics.unvisited_tail_blank` proves that cells beyond the space
  bound stay blank on every reachable configuration.
* **Deterministic vs nondeterministic.** The same structure serves both; see
  §3.

**Deviation (single work tape).** The textbooks allow several work tapes.
Space is robust under the number of tapes (with a constant-factor blow-up), so
the resulting named classes are the same, but the port does not formalize a
multi-work-tape model or that equivalence. All space classes in the library
are stated for this one-work-tape model.

**Deviation (two models).** P and EXPTIME are defined on Mathlib's
stack/tape machines, while L, NL, PSPACE, NPSPACE are defined on the space
machine above. The library nevertheless proves the cross-model inclusions
`NL ⊆ P`, `NP ⊆ PSPACE` and `NPSPACE ⊆ EXPTIME` by explicit simulations
(`Complexity/ClassesProofs/NLPolynomialTime.lean`, `NPPolynomialSpace.lean`,
`NPSpaceExponentialTime.lean` and their `InclusionAux`/`SavitchProofs`
support). Those proofs are the evidence that the two models are consistent
with each other in the way the textbooks assume.

---

## 2. Space accounting

```lean
/-- Every branch stays within the first `s` work cells, whether blank or nonblank. -/
def Machine.UsesSpace (M : Machine) (w : Word) (s : ℕ) : Prop :=
  ∀ (n : ℕ) (c : M.Config), M.Run w n c → c.workHead < s
```
(`Complexity/Classes/SpaceMachines.lean`)

The textbook definition (Sipser Def. 8.1, Arora–Barak Def. 4.1) charges the
number of work-tape cells *scanned* during the computation (blank or not), on
every branch. `UsesSpace M w s` says that on every reachable configuration of
every branch, the work head sits at a position below `s`. Because the work
tape starts at cell 0 and the head moves by at most one cell per step, the
set of scanned cells is always the prefix `{0, …, max head position}`, so
"head position < s on all reachable configurations" is exactly "at most `s`
cells were ever scanned". In particular:

* Cells scanned and later blanked are charged (the head visited them).
* Rejecting branches and computation prefixes that have not halted yet are
  charged (the quantifier is over *all* `Run`s, not only accepting or
  terminal ones).
* The initial cell is charged: `SpaceSemantics.space_positive : UsesSpace M w s → 0 < s`.
* The input tape and the input head are not charged, as required for
  sublinear space.

```lean
/-- Deterministic deciders using at most `s n` work cells on inputs of length `n`. -/
def DSPACE (s : ℕ → ℕ) : Set Language :=
  {A | ∃ M : Machine, M.Deterministic ∧ M.Decides A ∧
    ∀ w : Word, M.UsesSpace w (s w.length)}

/-- Nondeterministic deciders using at most `s n` work cells on every branch. -/
def NSPACE (s : ℕ → ℕ) : Set Language :=
  {A | ∃ M : Machine, M.Decides A ∧ ∀ w : Word, M.UsesSpace w (s w.length)}

/-- An integer logarithm that is positive even at input length zero. -/
def logSpace (n : ℕ) : ℕ := Nat.log 2 (n + 2)
```
(`Complexity/Classes/SpaceBounds.lean`)

`DSPACE s` / `NSPACE s` use the *exact* bound `s(n)`; there is no implicit
big-O. This is stricter than Sipser's `SPACE(f(n))`, which is defined with
`O(f(n))`. The named classes restore the constant factors explicitly (§4), so
no generality is lost where it matters; but a reader should not expect
`DSPACE s` to be closed under constant-factor changes of `s` by definition.

**Deviation (no space constructibility, no time bound).** The textbooks
sometimes assume `s` is space-constructible; nothing here needs it, because a
decider must halt on every branch by definition (§3), so no clock is
required. No time bound is imposed on space-bounded deciders; that is the
standard choice (the `2^{O(s)}` time bound is a theorem, used in the port's
proofs of `NL ⊆ P` and `NPSPACE ⊆ EXPTIME`, not an assumption).

---

## 3. Nondeterminism, halting and acceptance

```lean
/-- No choice of action is available at a terminal configuration. -/
def Machine.Terminal (M : Machine) (w : Word) (c : M.Config) : Prop :=
  ∀ d : M.Config, ¬ M.Step w c d

/-- All computation branches on this input have bounded finite length. -/
def Machine.HaltsOn (M : Machine) (w : Word) : Prop :=
  ∃ t : ℕ, ∀ (n : ℕ) (c : M.Config), M.Run w n c → n ≤ t

/-- Existential acceptance at a terminal configuration. -/
def Machine.Accepts (M : Machine) (w : Word) : Prop :=
  ∃ (n : ℕ) (c : M.Config), M.Run w n c ∧ M.Terminal w c ∧ M.accept c.state = true

/-- A decider halts on every branch and accepts exactly its language. -/
def Machine.Decides (M : Machine) (A : Language) : Prop :=
  ∀ w : Word, M.HaltsOn w ∧ (M.Accepts w ↔ w ∈ A)

/-- The transition table has at most one action for each local observation. -/
def Machine.Deterministic (M : Machine) : Prop :=
  ∀ (q : M.Q) (i : InputSymbol) (b : M.Γ),
    ∀ a ∈ M.transition q i b, ∀ a' ∈ M.transition q i b, a = a'
```
(`Complexity/Classes/SpaceMachines.lean`)

* **Nondeterminism** is the standard one: a transition table returning a
  finite *set* of actions; a computation is any sequence of legal steps
  (`Run`). A machine is deterministic when every set has at most one element,
  and `SpaceSemantics.deterministic_step` proves that this gives at most one
  successor configuration, i.e. the usual deterministic step function.
* **Acceptance** is existential over branches ("some branch reaches an
  accepting halting configuration"), which is the textbook NTM acceptance
  condition (Sipser Def. 7.9; Arora–Barak Def. 2.5). Acceptance is only
  granted at a *terminal* configuration, so a machine that passes through an
  accepting state but keeps running has not accepted.
* **Halting / decider.** `HaltsOn` asks for a uniform bound `t` on the length
  of every computation prefix. Since the transition table is finite, the
  computation tree is finitely branching, and by König's lemma "every branch
  halts" is equivalent to "there is a uniform bound on branch length". The
  formalization uses the uniform-bound form directly, which is the stronger
  looking but equivalent statement; `SpaceSemantics.not_infinite_path` proves
  that it excludes infinite computation paths. So `Decides` is exactly
  Sipser's "nondeterministic decider": all branches halt, and the input is in
  the language iff some branch accepts. This is what the textbook definitions
  of NL and NPSPACE require ("every branch halts and respects the bound").
* **Space on every branch.** `NSPACE` in §2 quantifies `UsesSpace` over all
  runs, so every nondeterministic branch, accepting or not, respects the
  bound, as in Arora–Barak Def. 4.1.

Nondeterminism for *time* classes is handled differently: NP is defined by
certificates (§4.2), which is Arora–Barak's primary definition and Sipser's
Theorem 7.20 characterization. There is no NTM-based definition of NP in the
library, and no theorem that the certificate definition equals an NTM time
definition (that equivalence is textbook but not formalized). Since every
downstream use (Cook–Levin, `P ⊆ NP`, `NP ⊆ PSPACE`) is stated against the
certificate definition, nothing depends on the missing equivalence.

---

## 4. The language classes

### 4.1 P
See §1.1. Standard.

### 4.2 NP and the pairing function

```lean
/-- A self-delimiting encoding of the first string, followed by the second. -/
def pair : Word → Word → Word
  | [], y => true :: y
  | b :: x, y => false :: b :: pair x y
```
(`Complexity/Classes/Certificates.lean`)

```lean
/-- Languages with polynomially bounded, polynomial-time verifiable certificates. -/
def NP : Set Language :=
  {A | ∃ V : Language, V ∈ P ∧ ∃ p : Polynomial ℕ, ∀ x : Word,
    x ∈ A ↔ ∃ y : Word, y.length ≤ p.eval x.length ∧ pair x y ∈ V}
```
(`Complexity/Classes/NondeterministicPolynomialTime.lean`)

This is Arora–Barak Definition 2.1 verbatim: `A ∈ NP` iff there is a
polynomial `p` and a polynomial-time verifier `V` such that
`x ∈ A ⟺ ∃ u, |u| ≤ p(|x|) ∧ V(x,u) = 1`. Two details that matter:

* The verifier is a *language in P* on the pair encoding, i.e. one
  deterministic polynomial-time machine, and its running time is polynomial
  in `|pair x y| = 2|x| + |y| + 1`. Because `|y| ≤ p(|x|)`, that is a
  polynomial in `|x|`, exactly as in the textbook. Both the injectivity and
  the length of the encoding are proved
  (`Certificates.pair_injective`, `Certificates.pair_length`,
  `Certificates.unpair_pair`), so the verifier really receives `(x, y)` and
  nothing else.
* The explicit certificate bound `y.length ≤ p.eval x.length` is essential:
  without it, "verifier polynomial in the combined length" would define a
  different (larger) class. It is present.

### 4.3 coNP and coNL

```lean
/-- The class of languages whose complements belong to the given class. -/
def co (C : Set Language) : Set Language := {A | Aᶜ ∈ C}

/-- Complements of languages in NL. -/
def coNL : Set Language := co NL

/-- Complements of languages in NP. -/
def coNP : Set Language := co NP
```
(`Complexity/Classes/ComplementClasses.lean`)

Standard (Arora–Barak Def. 2.20): the complement is applied to each language,
not to the class. `co_co : co (co C) = C` and the universal-certificate
characterization `mem_coNP_iff` are proved.

### 4.4 L, NL, PSPACE, NPSPACE

```lean
/-- Deterministic logarithmic work space. -/
def L : Set Language :=
  {A | ∃ c : ℕ, 0 < c ∧ A ∈ DSPACE (fun n => c * logSpace n)}

/-- Nondeterministic logarithmic work space. -/
def NL : Set Language :=
  {A | ∃ c : ℕ, 0 < c ∧ A ∈ NSPACE (fun n => c * logSpace n)}

/-- Deterministic polynomial work space. -/
def PSPACE : Set Language :=
  {A | ∃ p : Polynomial ℕ, A ∈ DSPACE p.eval}

/-- Nondeterministic polynomial work space. -/
def NPSPACE : Set Language :=
  {A | ∃ p : Polynomial ℕ, A ∈ NSPACE p.eval}
```
(`LogarithmicSpace.lean`, `NondeterministicLogarithmicSpace.lean`,
`PolynomialSpace.lean`, `NondeterministicPolynomialSpace.lean`)

* L and NL are "space `O(log n)`" with the constant made explicit:
  `c · ⌊log₂(n+2)⌋` for some `c > 0`. Using `n+2` rather than `n` makes the
  bound positive at `n = 0` and `n = 1` (a machine must be allowed to scan at
  least one cell), and `⌊log₂(n+2)⌋ ≤ 1 + ⌊log₂ n⌋` for `n ≥ 2`, so the
  family `{c·⌊log₂(n+2)⌋}` generates the same class as `O(log n)`. This is
  Sipser Def. 8.17 / Arora–Barak Def. 4.2 up to that harmless reindexing.
* PSPACE and NPSPACE quantify over an arbitrary polynomial with natural
  coefficients, which already absorbs constants and additive terms;
  this is `⋃_c SPACE(n^c)` in Sipser's notation.
* Savitch's theorem `PSPACE = NPSPACE`
  (`Complexity.Classes.PolynomialSpaceEquality.PSPACE_eq_NPSPACE`) is proved
  in the port, on this machine model, so NPSPACE is not merely a definition
  left dangling.

### 4.5 EXPTIME

```lean
/-- Deterministic time bounded by two to a polynomial in the input length. -/
def EXPTIME : Set Language :=
  {A | ∃ (M : SingleTape) (p : Polynomial ℕ), ∀ w : Word,
    ∃ c : TM0.Cfg M.Γ M.Q,
      Nonempty (StateTransition.EvalsToInTime (TM0.step M.transition)
        (TM0.init (w.map M.input)) (some c) (2 ^ p.eval w.length)) ∧
      TM0.step M.transition c = none ∧ (M.accept c.q = true ↔ w ∈ A)}
```
(`Complexity/Classes/ExponentialTime.lean`)

The same single-tape decider as `SingleTapeP`, with time bound `2^{p(n)}` for
an arbitrary polynomial `p`. This is EXP = ⋃_c DTIME(2^{n^c})
(Arora–Barak Def. 1.13 / Sipser §9.1), not the smaller class E = DTIME(2^{O(n)}).

**Deviation.** EXPTIME is defined only in the single-tape model, and no
theorem relates it to a stack-machine or multitape version. This does not
affect the ported results, all of which produce single-tape machines; but a
future user who has a `TM2` exponential-time machine cannot yet conclude
membership in EXPTIME without a (routine, not formalized) simulation.

### 4.6 The inclusion chain

All of the following are theorems in the library, with only
`propext`, `Classical.choice`, `Quot.sound` as axioms (checked by
`scripts/AxiomCheck.lean`):

```
L ⊆ NL          Complexity.Classes.BasicProperties.L_subset_NL
NL ⊆ P          Complexity.Classes.BasicProperties.NL_subset_P
P ⊆ NP          Complexity.Classes.BasicProperties.P_subset_NP
NP ⊆ PSPACE     Complexity.Classes.BasicProperties.NP_subset_PSPACE
PSPACE = NPSPACE  Complexity.Classes.PolynomialSpaceEquality.PSPACE_eq_NPSPACE
NPSPACE ⊆ EXPTIME Complexity.Classes.BasicProperties.NPSPACE_subset_EXPTIME
P closed under complement   Complexity.Classes.ComplementClosure.closed_under_complement
SingleTapeP = P             Complexity.Classes.ModelEquivalence.singleTapeP_eq_P
FiniteStackP = P            Complexity.Classes.FiniteStackEquivalence.finiteStackP_eq_P
```

Not included: `P ≠ NP`. The archived source states it as an axiom marked
"open question". This port does not admit it (it would violate the
no-added-axioms acceptance criterion) and nothing depends on it.

---

## 5. Polynomial-time many-one reductions and completeness

```lean
def ManyOne (A B : Language) : Prop :=
  ∃ f : Word → Word, Nonempty (Turing.TM2ComputableInPolyTime id id f) ∧
    ∀ x, x ∈ A ↔ f x ∈ B

def NPComplete (B : Language) : Prop := B ∈ NP ∧ ∀ A : Language, A ∈ NP → ManyOne A B
```
(`Complexity/CookLevin/Reductions.lean`)

```lean
def Hard (B : Language) : Prop := ∀ A : Language, A ∈ PSPACE → ManyOne A B

def Complete (B : Language) : Prop := B ∈ PSPACE ∧ Hard B
```
(`Complexity/ArcKayles/PSPACE.lean`)

`ManyOne A B` is the Karp reduction of Arora–Barak Def. 2.7 / Sipser Def. 7.29:
a function `f` on binary words computed by a deterministic polynomial-time
machine, with `x ∈ A ⟺ f(x) ∈ B` for *all* words `x` (including malformed
encodings). Points to check:

* **The reduction is computed by an actual machine**, the same `FinTM2`
  model used for P, with `id` encodings on both sides so that the input and
  output stacks literally hold the binary words `x` and `f x`. This is
  stronger than merely asserting that `f` is "polynomial-time computable" as
  an abstract predicate. Because the machine halts within `p(|x|)` steps and
  each step pushes at most one symbol, `|f x| ≤ p(|x|)` follows, as it should.
* **Same time model as P.** Membership (P, NP verifier) and reductions use
  the same machine model and time accounting, so composing reductions with
  deciders is meaningful; the port's
  `Complexity.ClassesProofs.PolynomialComposition.comp` performs that
  composition in the final completeness proof.
* `NPComplete` and `PSPACE.Complete` are the textbook definitions
  (Arora–Barak Def. 2.7 and Def. 4.10): membership plus hardness under
  polynomial many-one reductions, with hardness quantified over *every*
  language in the class.

The Cook–Levin theorem `Complexity.CookLevin.CookLevin.np_complete :
NPComplete SAT` is proved for the explicit CNF encoding

```lean
def SAT : Language := {w | ∃ F, encodeCNF F = w ∧ Satisfiable F}
```
(`Complexity/CookLevin/Satisfiability.lean`)

whose decoding round trip `EncodingCorrect.roundtrip : decodeCNF (encodeCNF F) = some F`
is proved, so `encodeCNF` is injective and `SAT` is the set of encodings of
satisfiable formulas, with malformed words outside the language.

**Weakness (Cook–Levin as used).** Arc Kayles hardness does not go through
the full NP-completeness of SAT; it uses the gate-level lemma
`Complexity.CookLevin.GateCorrect.correct` (Tseitin gate clauses evaluate
like the gate) and the reduction machinery. So the Cook–Levin theorem is
ported and proved, but the PSPACE-hardness proof depends on a smaller piece
of it. This is a strength for auditing, not a deviation.

---

## 6. Game and winning-position semantics

### 6.1 Arc Kayles

```lean
variable {V : Type} [DecidableEq V]

/-- The position after playing an edge with endpoints `u` and `v`. -/
def remove (S : Finset V) (u v : V) : Finset V := (S.erase u).erase v

/-- Legal moves, represented by ordered pairs of endpoints. -/
noncomputable def moves (G : SimpleGraph V) (S : Finset V) : Finset (V × V) := by
  classical
  exact (S ×ˢ S).filter fun e => G.Adj e.1 e.2

/-- Winning for the next player, by backward induction on surviving vertices. -/
def Winning (G : SimpleGraph V) (S : Finset V) : Prop :=
  ∃ e : {e // e ∈ moves G S}, ¬ Winning G (remove S e.val.1 e.val.2)
termination_by S.card
```
(`Complexity/ArcKayles/ArcKayles.lean`)

A position is a finite set `S` of surviving vertices of a simple graph `G`
(Mathlib's `SimpleGraph`: symmetric, irreflexive). A move picks an edge with
both endpoints surviving and deletes both endpoints. `Winning G S` is the
normal-play recursion "the player to move wins iff some move leads to a
position that is losing for the opponent", well-founded on `|S|`, which
decreases by two at every move. A position with no moves is losing
(the existential is over an empty type), which is the normal-play convention
"the player who cannot move loses". This is the standard definition of Arc
Kayles (Schaefer 1978) and of "winning position" in combinatorial game
theory (a P-position / N-position recursion).

Details:

* Moves are *ordered* pairs, so each edge appears twice; both copies lead to
  the same position (`remove S u v = remove S v u` as sets), so this changes
  nothing.
* Isolated vertices stay in `S` and never take part in a move. This matches
  the game: they are simply irrelevant, and it keeps the encoding (a full
  adjacency matrix) faithful.
* The recursion is on `S.card`, not on the graph; the graph is fixed. This is
  the intended game, where the board is the induced subgraph on `S`.

### 6.2 Sprague–Grundy values

```lean
noncomputable def mex (S : Finset ℕ) : ℕ := sInf {n : ℕ | n ∉ S}

noncomputable def value {V : Type} [DecidableEq V]
    (G : SimpleGraph V) (S : Finset V) : ℕ :=
  mex ((moves G S).attach.image fun e => value G (remove S e.val.1 e.val.2))
termination_by S.card
```
(`Complexity/ArcKayles/Grundy.lean`)

The Grundy value is the minimum excluded value of the options' values, the
standard Sprague–Grundy recursion. The link to the independent `Winning`
definition is a theorem, not a definition:
`GrundyProperties.losing_iff_zero : ¬ Winning G S ↔ value G S = 0`, together
with `smaller_reachable`, `value_not_reachable` (the two halves of the mex
characterization) and `disjoint_union :
value G (S ∪ T) = Nat.xor (value G S) (value G T)` for disjoint,
non-adjacent `S`, `T` (the Sprague–Grundy theorem for a disjoint union of two
components). These are the paper's Observation 2 and Lemmas 3–4.

### 6.3 The positive CNF game (Schaefer's G_pos(POS CNF))

```lean
structure Formula where
  nvars : ℕ
  clauses : List (Finset (Fin nvars))

def Satisfied (φ : Formula) (T : Finset (Fin φ.nvars)) : Prop :=
  ∀ C ∈ φ.clauses, ∃ x ∈ C, x ∈ T

/-- Whether True can force satisfaction from the specified position and turn. -/
def TrueWins (φ : Formula) (U T : Finset (Fin φ.nvars)) (trueTurn : Bool) : Prop :=
  if U = ∅ then Satisfied φ T
  else if trueTurn then
    ∃ x : U, TrueWins φ (U.erase x.val) (insert x.val T) false
  else
    ∀ x : U, TrueWins φ (U.erase x.val) T true
termination_by U.card

def FirstWins (φ : Formula) : Prop := TrueWins φ Finset.univ ∅ true
```
(`Complexity/ArcKayles/PositiveCNF.lean`)

This is Schaefer's positive-CNF game: players True and False alternately
pick an unassigned variable (`U` = unassigned, `T` = set to true), True moves
first, and True wins iff, when all variables are assigned, every clause
contains a true variable. Empty clauses (unsatisfiable) and unused variables
are allowed, matching the paper. `TrueWins` is the usual alternating
∃/∀ recursion on the number of unassigned variables. This is the game whose
PSPACE-hardness is Schaefer's theorem, proved here as
`Complexity.ArcKayles.PositiveCNFHardness.hard`.

### 6.4 Encodings and the decision languages

```lean
structure Graph where
  vertices : ℕ
  graph : SimpleGraph (Fin vertices)

noncomputable def graphWord (G : Graph) : Word := by
  classical
  exact List.replicate G.vertices true ++ [false] ++
    (List.finRange G.vertices).flatMap fun u =>
      (List.finRange G.vertices).map fun v => decide (G.graph.Adj u v)

def arcKayles : Language :=
  {w | ∃ G : Graph, graphWord G = w ∧ ArcKayles.Winning G.graph Finset.univ}

def positiveCNF : Language :=
  {w | ∃ φ : PositiveCNF.Formula, formulaWord φ = w ∧ PositiveCNF.FirstWins φ}
```
(`Complexity/ArcKayles/Encoding.lean`)

The Arc Kayles decision problem is the set of encodings of labeled graphs on
which the first player wins from the full board. The encoding is a unary
vertex count followed by the complete row-major adjacency matrix; it is
proved injective (`Complexity.ArcKaylesProofs.GraphEncoding.graphWord_injective`,
and `FormulaParser.formulaWord_injective` for formulas), so the language is
"the" problem and not an existential over ambiguous decodings, and its length
`n² + n + 1` is proved (`Sizes.graph_length`). Malformed words are not in the
language, which is the usual convention.

**Deviation (labeled graphs, quadratic encoding).** The problem is stated on
labeled graphs with an explicit adjacency matrix. Textbook statements are
usually "given a graph"; any reasonable encoding (adjacency lists, etc.) is
polynomially interconvertible, so PSPACE-completeness is encoding-independent
in the usual sense, but only this one encoding is formalized.

### 6.5 The reduction from positive CNF and its correctness

```lean
def graph (φ : Formula) : SimpleGraph ℕ := SimpleGraph.fromRel (Edge φ)
def board (φ : Formula) : Finset ℕ := Finset.range (size φ)
```
(`Complexity/ArcKayles/Construction.lean`; `Edge` is the explicit edge
relation of the paper's gadget, and `size φ = 13n + 4m + 18` is proved in
`Sizes.construction_size`.)

The correctness statements are the paper's Claims 9 and 10, stated for
formulas with an odd number of clauses:

```
true_strategy  : φ.clauses.length % 2 = 1 → FirstWins φ → Winning (graph φ) (board φ)
false_strategy : φ.clauses.length % 2 = 1 → ¬ FirstWins φ → ¬ Winning (graph φ) (board φ)
```

and the full word-level reduction
`Reduction.polynomial_reduction : ManyOne Encoding.positiveCNF Encoding.arcKayles`
handles the parity normalization (duplicate a clause), the empty conjunction
and malformed inputs with fixed yes/no instances, and supplies a compiled
`TM2` machine as the polynomial-time witness. The supporting lemmas
(`Passes.outcome_equivalent`: a finite shared supply of passes and the
freedom to assign either truth value do not change the winner;
`RegularPlay.deviation_loses` and `RegularPlay.exceptional_parity`: any move
outside the intended simulation loses, except for one exceptional move whose
outcome is determined by a parity;
`Biclique.value_eq`: the Grundy formula
`g(a,b) = (a+b) mod 2 + 2·(min(a,b) mod 2)` for a biclique with pendant
neighbours) are all theorems.

**Weakness (`Passes` is the finite form of the paper's Lemma 5).** The paper's
lemma allows unboundedly many passes; the port proves the version with a
shared finite pass budget, which is what the reduction actually needs and
which excludes infinite play. This is a strengthening of the hypotheses of a
lemma, not of the final theorem.

---

## 7. PSPACE-completeness of Arc Kayles

```
Complexity.ArcKayles.Completeness.membership      : Encoding.arcKayles ∈ PSPACE
Complexity.ArcKayles.PositiveCNFHardness.hard      : PSPACE.Hard Encoding.positiveCNF
Complexity.ArcKayles.Reduction.polynomial_reduction : ManyOne Encoding.positiveCNF Encoding.arcKayles
Complexity.ArcKayles.Completeness.pspace_complete  : PSPACE.Complete Encoding.arcKayles
```

Unfolding the definitions of §5 and §4.4, the final theorem says: there is a
deterministic machine of the §1.3 model, halting on every input, using
`p(|w|)` work cells, that accepts exactly the encodings of first-player-win
graphs; and for every language `A` decided by such a machine in polynomial
space there is a polynomial-time (`FinTM2`) computable `f` with
`x ∈ A ⟺ f(x) ∈ arcKayles`. That is Arora–Barak Definition 4.10 applied to
the Arc Kayles language, i.e. the textbook statement "Arc Kayles is
PSPACE-complete under polynomial-time many-one reductions".

The hardness half is not assumed from the literature. Schaefer's theorem is
itself proved from the §1.3 definition of PSPACE: a polynomial-space
machine's configuration graph is encoded by a uniformly generated circuit,
reachability is expressed by quantified repeated squaring (a Savitch-style
recursion), the circuit is converted to quantified CNF with the ported
Tseitin gate lemma, block quantifiers are normalized to an alternating game,
and Byskov's strategy-preserving gadgets turn that into a True-first positive
CNF instance; each of these word maps has a compiled polynomial-time machine
witness. The membership half is a depth-first evaluation of the game tree
with an explicitly bounded stack, compiled to a deterministic work-space
machine with a polynomial bound.

**What is *not* claimed.** The theorem is about this specific encoding and
this specific machine model, with reductions in the `FinTM2` model. It does
not by itself say anything about, e.g., Arc Kayles restricted to graph
classes, or about completeness under log-space reductions (the textbooks'
other common choice); those are strictly stronger statements and are outside
the port.

---

## 8. Summary of deviations and weaknesses

| Item | Status |
| --- | --- |
| Toolchain | Lean `v4.33.0`, Mathlib `db584cd6…` — the revisions the pinned source commits actually use. The v4.30.0 line only exists on an older, superseded branch of classical-complexity that the arc-kayles sources cannot build against. |
| `P ≠ NP` | Stated as an axiom in the source ("open question"); dropped here, unused. |
| Two machine models | Time classes on Mathlib `FinTM2` / `TM0`, space classes on a custom read-only-input machine. Cross-model inclusions are proved by simulation; no general "model equivalence" theorem beyond `SingleTapeP = P`, `FiniteStackP = P`. |
| Non-input stack alphabets in `FinTM2` | Mathlib allows infinite alphabets; harmless, and `FiniteStackP = P` is proved. |
| Single work tape | Space classes use one work tape; multitape equivalence not formalized. |
| `DSPACE`/`NSPACE` exact bounds | No big-O in the generic classes; constants are explicit in L, NL; polynomials absorb them in PSPACE, NPSPACE. |
| NP by certificates only | No NTM-time definition of NP and no equivalence theorem; not needed downstream. |
| EXPTIME single-tape only | No stack-machine version. |
| Arc Kayles encoding | Labeled graphs, full adjacency matrix, injectivity proved. Other encodings not formalized. |
| Reductions | Polynomial-time many-one (Karp), not log-space. |
| Passes lemma | Finite pass budget (what the reduction needs), not the paper's unbounded version. |

Nothing in the list weakens the headline theorems as stated; they are the
standard statements for the standard definitions, and the only axioms they
use are `propext`, `Classical.choice` and `Quot.sound`.
