module Tutorials.SetTheoryVsTypes-Live where

-- ═══════════════════════════════════════════════════════════════════════
-- FROM SET THEORY TO DEPENDENT TYPES
-- A 30-minute interactive tutorial for pure mathematicians
--
-- "If you have a BSc or MSc in mathematics, you already know
--  everything in this file.  You just know it under different names."
--
-- We fill in the holes {!!} together, interactively.
--
-- References:
--   Thorsten Altenkirch — "Naive Type Theory" (2019)
--   Philip Wadler — "Propositions as Types" (2015)
--   Andrej Bauer — "Five Stages of Accepting Constructive Mathematics"
--   Martín Escardó — "Introduction to Univalent Foundations" (2019)
--   Conor McBride — "Why Dependent Types Matter" (2006)
--
-- PRESENTER: see stt-present.el for keybindings (F1–F12).
-- ═══════════════════════════════════════════════════════════════════════


-- ┌─────────────────────────────────────────────────────────┐
-- │  ACT I.   THE GROUND RULES                              │
-- │  What changes when you move from ZFC to type theory     │
-- └─────────────────────────────────────────────────────────┘

-- ─────────────────────────────────────────────────
-- §1  JUDGMENT vs PROPOSITION  (Altenkirch, 2019)
-- ─────────────────────────────────────────────────

-- You already use types informally.  When you write "let n ∈ ℕ" on the
-- blackboard, you are making a typing judgment.  Type theory just takes
-- this seriously.  (Altenkirch calls this "naive type theory" — the
-- natural analogue of naive set theory.)
--
-- In ZFC, "x ∈ A" is a PROPOSITION — a statement inside the system.
-- It can be true or false.  You prove or disprove it.
--
--   3 ∈ ℕ  (true)     π ∈ ℚ  (false — and this is a theorem)
--
-- An element can belong to many sets.  ℕ ⊂ ℤ ⊂ ℚ ⊂ ℝ ⊂ ℂ.
-- "Is the monster group a real number?" is a grammatically valid
-- question in ZFC.  (The answer is no, but you need a proof.)

-- In type theory, "x : A" is a JUDGMENT — a statement ABOUT the system.
-- It is not proved.  It is unchallengeable, like declaring a variable.
--
--   3 : ℕ
--
-- Full stop.  This 3 does not simultaneously have type ℤ.
-- In set theory, 3 is one object living in many sets.  In type theory,
-- there are many 3s — one per type:
--
--   3 : ℕ       (built from suc (suc (suc zero)))
--   3 : ℤ       (built from +3, a signed integer)
--   3 : Fin 7   (built as the fourth element of a 7-element type)
--
-- A mathematician sees "the same number."  The type checker sees three
-- distinct terms that happen to print the same way.  To move between
-- them you need an explicit coercion — a function ℕ → ℤ that maps
-- a natural number to the corresponding positive integer.  You already
-- know this map; you just never had to write it down.
-- In a textbook, "3 ∈ ℤ" is free.  In Agda, you write "pos 3 : ℤ"
-- to apply the embedding.  (The standard library abbreviates pos to
-- a prefix "+", so you see "+ 3 : ℤ" — not to be confused with
-- addition, which is infix: "3 + 5".  Agda tells them apart by arity.)
--
-- "Is the monster group a real number?" is a type error, caught before
-- any mathematics begins.
--
--   set theory = one universe, membership is internal
--   type theory = many types, typing is external

-- A type is defined by its CONSTRUCTORS — the ways to build elements.
-- "data" = inductive defn.  "Set" = the universe of types.  "→" = function arrow.

data ℕ : Set where
  zero : ℕ                 -- 0
  suc  : ℕ → ℕ             -- successor: suc n = n + 1
-- Exhaustive: every ℕ is either zero or suc of a smaller one.  No third option.

{-# BUILTIN NATURAL ℕ #-}  -- Agda shorthand: lets us write 3 instead of suc (suc (suc zero))

-- The empty type: no constructors, so nothing can be built.
-- You know this as ∅, falsehood, the initial object.
data ⊥ : Set where

-- The unit type: exactly one element.  You know this as {∗}, truth, the terminal object.
-- A "record" is like "data" with exactly one constructor whose arguments are named fields.
record ⊤ : Set where
  constructor tt


-- ─────────────────────────────────────────────────
-- §2  PROPOSITIONS AS TYPES  (Curry, 1934; Howard, 1969)
-- ─────────────────────────────────────────────────

-- So types replace sets.  But what replaces proofs?

-- In a standard math degree, there are three separate activities:
--   (1) Define objects    (e.g., "let G be a group")
--   (2) State theorems    (e.g., "the center of G is normal")
--   (3) Write proofs      (e.g., "let g ∈ Z(G), h ∈ G, then...")
--
-- In type theory, ALL THREE are the same thing: TERMS.
--   (1) A definition is a term       (e.g., ℕ, _+_)
--   (2) A theorem statement is a TYPE (e.g., n + 0 ≡ n)
--   (3) A proof is a TERM of that type
--
-- "P is true"  = the type P is inhabited (someone built a term)
-- "P is false" = the type P is empty     (no term can be built)
--
--   Logic              Types               You already know this as
--   ─────              ─────               ───────────────────────
--   ⊥  (falsehood)     ⊥  (empty type)     ∅
--   ⊤  (truth)         ⊤  (unit type)      {∗}
--   P ∧ Q              P × Q  (pair)       cartesian product
--   P ∨ Q              P ⊎ Q  (tagged)     disjoint union / coproduct
--   P ⟹ Q             P → Q  (function)   Hom(P,Q)
--   ¬ P                P → ⊥               "P implies absurdity"
--   ∀x∈A. P(x)        (x : A) → P x       a section of a bundle
--   ∃x∈A. P(x)        Σ(x : A) (P x)      total space of a bundle
--
-- (If you know fibre bundles: Π is the type of sections, Σ is the
-- total space.  The base is A, the fibre over x is P x.)

-- Product type: a proof of P ∧ Q is a pair (proof of P, proof of Q).
--
-- SYNTAX: Underscores mark where ARGUMENTS go.  "_×_" is infix: "A × B".
-- "field" lists named components.  "open _×_" makes fst/snd standalone.
record _×_ (A B : Set) : Set where
  constructor _,_
  field
    fst : A
    snd : B
open _×_

-- Sum type (disjoint union / coproduct): a proof of P ∨ Q is
-- EITHER a proof of P OR a proof of Q, tagged so you know which.
data _⊎_ (A B : Set) : Set where
  inl : A → A ⊎ B
  inr : B → A ⊎ B

-- Negation:  ¬P  =  P → ⊥   ("P implies absurdity").
¬_ : Set → Set
¬ A = A → ⊥

-- EXERCISE 1: ex falso quodlibet — from ⊥, anything follows.
--
-- {A : Set} means A is IMPLICIT — Agda infers it.
-- Since ⊥ has NO constructors, use "()" to tell Agda "impossible."
absurd : {A : Set} → ⊥ → A
absurd = {!!}

-- EXERCISE 2: P ∧ Q ⟹ Q ∧ P.  Swap the pair.  (Try F7 to case-split.)
×-comm : {A B : Set} → A × B → B × A
×-comm = {!!}

-- EXERCISE 3: P ∨ Q ⟹ Q ∨ P.  Swap the tag.
⊎-comm : {A B : Set} → A ⊎ B → B ⊎ A
⊎-comm = {!!}

-- Read ×-comm again: it takes a pair and returns a swapped pair.
-- It is simultaneously a proof that conjunction commutes AND a
-- program that swaps two values in memory.  In type theory, every
-- proof is a program you can execute.  This is not a metaphor.


-- ┌─────────────────────────────────────────────────────────┐
-- │  ACT II.  THE DIVERGENCE                                │
-- │  Where type theory and classical mathematics part ways  │
-- └─────────────────────────────────────────────────────────┘

-- ─────────────────────────────────────────────────
-- §3  EXISTENCE REQUIRES A WITNESS  (Bauer, 2016)
-- ─────────────────────────────────────────────────

-- Andrej Bauer describes five stages of accepting constructive math,
-- parallel to the stages of grief.
--
-- In classical math you routinely prove ∃x.P(x) by:
--   "Suppose no such x exists.  Then ... contradiction.  ∴ ∃x.P(x)."
-- The witness x is never produced.
--
-- In type theory, a proof of "there exists x in A such that P(x)"
-- IS a pair:  (x , evidence-that-P-holds-for-x).
-- You MUST hand over the witness.
--
-- You are not "giving up" classical mathematics.  You are visiting a
-- world where every existence proof comes with a construction.
-- Classical axioms (LEM, choice) remain consistent — you can always
-- postulate them if you need them (see below).

-- The dependent pair (existential quantifier).
-- Σ A P packs a WITNESS (element of A) with EVIDENCE (P holds for it).
-- "P : A → Set" is a predicate: for each x : A, the type P x is the
-- proposition "P holds for x" — inhabited if true, empty if false.
record Σ (A : Set) (P : A → Set) : Set where
  constructor _,,_
  field
    witness  : A
    evidence : P witness
open Σ

-- A predicate: "n is even."  A function from ℕ to types.
-- Even 4 = Even 2 = Even 0 = ⊤ (true).  Even 3 = Even 1 = ⊥ (false).
-- Try F1 to see Agda compute these!
Even : ℕ → Set
Even zero          = ⊤
Even (suc zero)    = ⊥
Even (suc (suc n)) = Even n

-- EXERCISE 4: "There exists an even natural number."
-- Exhibit a witness and provide evidence.
there-exists-an-even : Σ ℕ Even
there-exists-an-even = {!!}

-- EXERCISE 5: A → ¬¬A.  You have (a : A) and (f : A → ⊥).
to-¬¬ : {A : Set} → A → ¬ ¬ A
to-¬¬ = {!!}

-- Try the reverse and GET STUCK — this is the wall:
--   from-¬¬ : {A : Set} → ¬ ¬ A → A
--   from-¬¬ f = ?   -- f : (A → ⊥) → ⊥.  No way to extract an A.

-- EXERCISE 6: ¬∃ ⟹ ∀¬  ("if nothing satisfies P, everything satisfies ¬P")
¬∃⇒∀¬ : {A : Set} {P : A → Set} → ¬ Σ A P → (x : A) → ¬ P x
¬∃⇒∀¬ = {!!}

-- EXERCISE 7: ∀¬ ⟹ ¬∃  ("if everything satisfies ¬P, nothing satisfies P")
∀¬⇒¬∃ : {A : Set} {P : A → Set} → ((x : A) → ¬ P x) → ¬ Σ A P
∀¬⇒¬∃ = {!!}

-- THE WALL: ¬∀ ⟹ ∃¬ requires excluded middle.
-- Knowing a universal fails does not hand you a counterexample.
-- "postulate" declares a term without definition — an axiom.
-- "λ x →" is an anonymous function (like "x ↦" in math).
postulate
  classical-escape : {A : Set} {P : A → Set}
    → ¬ ((x : A) → P x) → Σ A (λ x → ¬ P x)

-- Escardó's point: type theory is not anti-classical — it is pre-classical.
-- LEM and choice are CONSISTENT; you just lose computation (proofs using
-- LEM don't reduce to normal forms).  You can always postulate them.

-- But sometimes you CAN decide.  "Dec A" means: either I have a proof
-- of A, or I have a proof of ¬A — and I know WHICH.  Unlike LEM, which
-- asserts one holds, Dec is an algorithm that computes the answer.

data Dec (A : Set) : Set where
  yes :   A → Dec A
  no  : ¬ A → Dec A

-- For natural numbers, equality IS decidable — compare digit by digit.
-- For real numbers, it is NOT.  Consider (Buzzard's example):
--
--   Σ(1+14n+76n²+168n³)/2^(20n) · C(2n,n)^7  =?  32/π³
--
-- This is the Gourevitch conjecture.  It is open.  No algorithm can
-- decide all such equalities over ℝ — this is a theorem.
-- For decidable propositions, you get LEM for free.
-- For undecidable ones, you simply do not.


-- ─────────────────────────────────────────────────
-- §4  EQUALITY: two notions where you had one
-- ─────────────────────────────────────────────────

-- Existence required a witness.  Equality has a similar surprise.
--
-- In set theory, a = b.  One notion.  In type theory, two:
--
-- DEFINITIONAL: the machine verifies it by unfolding definitions —
--   like simplifying (x+1)(x−1) to x²−1 by mechanical expansion.
--
-- PROPOSITIONAL: you must construct a proof.
--   The machine cannot see it by unfolding — you must explain why.
--
-- Which equalities are definitional depends on how you WROTE the
-- definition.  Think of a group presentation: the relations you listed
-- are "free," but their consequences need derivation.  Choosing a
-- definition in type theory is like choosing a presentation — different
-- choices make different facts trivially available.

infix 4 _≡_
-- The identity type.  One constructor: refl proves x ≡ x.
-- refl only typechecks when both sides COMPUTE to the same value.
data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

{-# BUILTIN EQUALITY _≡_ #-}

-- Addition, by recursion on the first argument.
_+_ : ℕ → ℕ → ℕ
zero  + m = m
suc n + m = suc (n + m)

-- DEFINITIONAL in action: 2 + 2 unfolds to suc (suc (suc (suc zero))).
-- refl suffices.
2+2≡4 : 2 + 2 ≡ 4
2+2≡4 = refl

-- Postulate ⊥ and the system collapses.  "module" creates a sandbox.

module Danger where
  postulate oops : ⊥              -- assert that falsehood holds

  -- DEMO: now "prove" 1 + 1 ≡ 3.  Use absurd.
  1+1≡3 : 1 + 1 ≡ 3
  1+1≡3 = {!!}

  0≡1 : 0 ≡ 1                    -- arithmetic is dead
  0≡1 = {!!}

-- Outside the module, oops is gone.  --safe forbids postulates entirely.

-- DEFINITIONAL: 0 + n unfolds to n by the first clause of _+_.  Free.
+-idˡ : (n : ℕ) → 0 + n ≡ n
+-idˡ _ = refl

-- PROPOSITIONAL: n + 0 does NOT unfold — _+_ pattern-matches on the
-- first argument, and n is a variable, so the definition is stuck.
-- We must prove it by induction.  This is the "consequence that needs
-- derivation" from our group presentation analogy.

-- Tool: if x ≡ y then f x ≡ f y (apply any function to both sides).
cong : {A B : Set} {x y : A} (f : A → B) → x ≡ y → f x ≡ f y
cong f refl = refl

-- EXERCISE 8: n + 0 ≡ n.  Prove by induction on n.
-- The recursive call +-idʳ n IS the induction hypothesis.
+-idʳ : (n : ℕ) → n + 0 ≡ n
+-idʳ = {!!}

-- ▸ Both are equally trivial in a textbook.  Here, one is a "relation in
-- the presentation" (free) and the other is a "derived consequence" (costs
-- a proof).  Had we defined _+_ by recursion on the SECOND argument,
-- the roles would reverse.  The math is the same; the presentation differs.
--
-- ▸ Buzzard hit this formalizing sheaf pushforward: id(U) and U are only
-- propositionally equal, but his proof silently assumed they were
-- definitionally equal.  His conclusion: "I was wrong to use equality."
-- (See "Grothendieck's use of equality," Buzzard 2024.)


-- ┌─────────────────────────────────────────────────────────┐
-- │  ACT III.  THE PAYOFF                                   │
-- │  What you gain from this way of doing mathematics       │
-- └─────────────────────────────────────────────────────────┘

-- ─────────────────────────────────────────────────
-- §5  INDUCTION IS RECURSION  (no axiom needed)
-- ─────────────────────────────────────────────────

-- We just used induction to prove n + 0 ≡ n.  But where was the axiom?
-- In PA, induction is an AXIOM SCHEMA.
-- In type theory, induction IS structural recursion — the termination
-- checker verifies it.

-- Symmetry and transitivity of ≡.
sym : {A : Set} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

trans : {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl q = q

-- EXERCISE 9: n + suc m ≡ suc (n + m), by induction on n.
+-suc : (n m : ℕ) → n + suc m ≡ suc (n + m)
+-suc = {!!}

-- EXERCISE 10: commutativity of addition.
-- Textbook proof:
--   Base (m = 0): use +-idʳ.
--   Step (m → suc m): use +-suc and IH.
+-comm : (n m : ℕ) → n + m ≡ m + n
+-comm = {!!}

-- Equational reasoning: syntactic sugar for chains of "trans".
-- Usage:  x ≡⟨ reason₁ ⟩  y ≡⟨ reason₂ ⟩  z ∎
infix  3 _∎
infixr 2 step-≡
infix  1 begin_

begin_ : {A : Set} {x y : A} → x ≡ y → x ≡ y
begin p = p

step-≡ : {A : Set} (x : A) {y z : A} → y ≡ z → x ≡ y → x ≡ z
step-≡ _ yz xy = trans xy yz

syntax step-≡ x yz xy = x ≡⟨ xy ⟩ yz

-- Close the chain: "x ∎" means "x ≡ x by refl."
_∎ : {A : Set} (x : A) → x ≡ x
_ ∎ = refl

-- EXERCISE 11: commutativity in equational reasoning style.
-- Read the result aloud — it reads like a blackboard calculation.
-- The machine just checks each step.
+-comm′ : (n m : ℕ) → n + m ≡ m + n
+-comm′ n zero = +-idʳ n
+-comm′ n (suc m) = begin
  n + suc m    ≡⟨ {!!} ⟩
  suc (n + m)  ≡⟨ {!!} ⟩
  suc (m + n)  ∎


-- ─────────────────────────────────────────────────
-- §6  DEPENDENT TYPES REPLACE SET-BUILDER NOTATION
-- ─────────────────────────────────────────────────

-- So far, types have replaced propositions.  Now they replace subsets.
-- In set theory: {x ∈ ℕ | x < 5}.  In type theory: no subsets.
-- Instead, build a type whose STRUCTURE guarantees the property.

-- Fin n: exactly n elements.  Replaces "{x ∈ ℕ | x < n}" with no bounds check.
-- Fin is a FAMILY of types indexed by ℕ.  Each constructor targets Fin (suc n),
-- never Fin 0 — so Fin 0 is empty not by proof but because no constructor fits.
data Fin : ℕ → Set where
  zero : {n : ℕ} → Fin (suc n)     -- zero is in Fin 1, Fin 2, Fin 3, ...
  suc  : {n : ℕ} → Fin n → Fin (suc n)  -- if i is in Fin n, then suc i is in Fin (n+1)

-- EXERCISE 12: Fin 0 is empty — no constructor can target it.
Fin0-empty : Fin 0 → ⊥
Fin0-empty = {!!}

-- Vec A n: a list whose length n is tracked in the TYPE.
data Vec (A : Set) : ℕ → Set where
  []  : Vec A 0
  _∷_ : {n : ℕ} → A → Vec A n → Vec A (suc n)

infixr 5 _∷_

-- EXERCISE 13: concatenation.  The type IS the length lemma,
-- the definition IS the proof.
_++_ : {A : Set} {n m : ℕ} → Vec A n → Vec A m → Vec A (n + m)
_++_ = {!!}

-- EXERCISE 14: safe indexing.  Out-of-bounds is a type error.
lookup : {A : Set} {n : ℕ} → Vec A n → Fin n → A
lookup = {!!}

-- No [] case.  We did not handle it and forget — we CANNOT write it.
-- The index would need type Fin 0, which has no constructors.
-- The impossible case is not suppressed; it does not exist.

-- McBride: "pay-as-you-go correctness" — encode more in the type,
-- the machine checks more.

-- EXERCISE 15: verified halving.
-- Same trick: no case for n = 1.  Even 1 = ⊥, so the case is unwritable.
half : (n : ℕ) → Even n → ℕ
half = {!!}


-- ─────────────────────────────────────────────────
-- §7  A TASTE OF REAL ALGEBRA
-- ─────────────────────────────────────────────────

-- Now put it together: a group, same axioms as any algebra textbook,
-- but machine-checked.  Since propositions are types, operations and
-- axioms live side by side in one record — there is no separate
-- "definition" and "axiom list."  They are the same kind of thing.
-- "∀ x" = "(x : G) →".

record Group (G : Set) : Set where
  field
    ε     : G                                           -- identity element
    _·_   : G → G → G                                  -- group operation
    _⁻¹   : G → G                                      -- inverse
    assoc : ∀ x y z → (x · y) · z ≡ x · (y · z)       -- associativity
    idˡ   : ∀ x → ε · x ≡ x                           -- left identity
    idʳ   : ∀ x → x · ε ≡ x                           -- right identity
    invˡ  : ∀ x → (x ⁻¹) · x ≡ ε                     -- left inverse
    invʳ  : ∀ x → x · (x ⁻¹) ≡ ε                     -- right inverse

  infixl 7 _·_
  infix  8 _⁻¹

  -- EXERCISE 16: the identity is unique.
  id-unique : ∀ e → (∀ x → e · x ≡ x) → e ≡ ε
  id-unique e e-id = begin
    e      ≡⟨ {!!} ⟩
    e · ε  ≡⟨ {!!} ⟩
    ε      ∎

  -- EXERCISE 17: (x⁻¹)⁻¹ = x.
  inv-inv : ∀ x → (x ⁻¹) ⁻¹ ≡ x
  inv-inv x = begin
    (x ⁻¹) ⁻¹                        ≡⟨ {!!} ⟩
    ((x ⁻¹) ⁻¹) · ε                  ≡⟨ {!!} ⟩
    ((x ⁻¹) ⁻¹) · ((x ⁻¹) · x)      ≡⟨ {!!} ⟩
    (((x ⁻¹) ⁻¹) · (x ⁻¹)) · x      ≡⟨ {!!} ⟩
    ε · x                             ≡⟨ {!!} ⟩
    x                                 ∎


-- ─────────────────────────────────────────────────
-- APPENDIX.  TRANSLATION DICTIONARY
-- ─────────────────────────────────────────────────

-- ┌──────────────────────────┬─────────────────────────────────────────┐
-- │ Set theory (your BSc)    │ Type theory (Agda)                      │
-- ├──────────────────────────┼─────────────────────────────────────────┤
-- │ x ∈ A  (proposition)     │ x : A  (judgment — unchallengeable)     │
-- │ set = its elements       │ type = its constructors                 │
-- │ A ⊂ B                    │ no subtyping; use Σ or indexed type     │
-- │ f ⊂ A × B  (graph)       │ f : A → B  (primitive, computes)        │
-- │ a = b  (one equality)    │ definitional (free) + propositional     │
-- │ {x ∈ A | P(x)}          │ Σ A P  or  an indexed data type         │
-- │ ∀x ∈ A. P(x)            │ (x : A) → P x  (dependent function)    │
-- │ ∃x ∈ A. P(x)            │ Σ A P  (witness + evidence)             │
-- │ proof by contradiction   │ only proves ¬A, not A                   │
-- │ induction axiom          │ structural recursion (+ termination)    │
-- │ proposition              │ type                                    │
-- │ proof                    │ term  (program!)                        │
-- │ true / false             │ inhabited / empty                       │
-- │ definition, theorem,     │ all the same thing: a term              │
-- │ and proof are separate   │                                         │
-- └──────────────────────────┴─────────────────────────────────────────┘
--
-- THE DEEPEST SHIFT:
-- In set theory, logic is external — a different layer from the math.
-- In type theory, logic IS mathematics: proofs are programs, one language.


-- ─────────────────────────────────────────────────
-- RESOURCES
-- ─────────────────────────────────────────────────

-- Foundations & philosophy:
--   Thorsten Altenkirch, "Naive Type Theory" (2019)
--     https://www.cs.nott.ac.uk/~psztxa/publ/fomus19.pdf
--   Philip Wadler, "Propositions as Types" (2015)
--     https://homepages.inf.ed.ac.uk/wadler/papers/propositions-as-types/propositions-as-types.pdf
--   Andrej Bauer, "Five Stages of Accepting Constructive Mathematics" (2016)
--     https://math.andrej.com/2016/10/10/five-stages-of-accepting-constructive-mathematics/
--   nLab, "From Set Theory to Type Theory"
--     https://golem.ph.utexas.edu/category/2013/01/from_set_theory_to_type_theory.html

-- Agda tutorials & textbooks:
--   Uma Zalakain, "Programming with Evidence" — BCAM tutorial (2021)
--     https://umazalakain.github.io/agda-bcam/
--   Philip Wadler, "Programming Language Foundations in Agda" (PLFA)
--     https://plfa.github.io/
--   Martín Escardó, "Introduction to Univalent Foundations with Agda" (2019)
--     https://martinescardo.github.io/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html
--   Jesper Cockx, "Programming and Proving in Agda" (2024)
--     https://github.com/jespercockx/agda-lecture-notes
--   Dan Licata, "Dependently Typed Programming in Agda" — OPLSS (2013)
--     https://dlicata.wescreates.wesleyan.edu/teaching.html

-- Dependent types — why they matter:
--   Conor McBride, Thorsten Altenkirch, "Why Dependent Types Matter" (2006)
--     https://www.cs.nott.ac.uk/~psztxa/publ/ydtm.pdf
--   Daniel Friedman & David Christiansen, "The Little Typer" (MIT Press, 2018)
--     https://mitpress.mit.edu/9780262536431/the-little-typer/
--   Conor McBride, "The Derivative of a Regular Type is its Type of One-Hole Contexts"
--     http://strictlypositive.org/diff.pdf

-- Homotopy type theory:
--   Egbert Rijke, "Introduction to Homotopy Type Theory" (Cambridge UP, 2023)
--     https://github.com/EgbertRijke/HoTT-Intro
--   The agda-unimath library
--     https://github.com/UniMath/agda-unimath
--   The HoTT Book
--     https://homotopytypetheory.org/book/

-- Constructive mathematics — surprising results:
--   Martín Escardó, "Seemingly Impossible Functional Programs" (2007)
--     https://math.andrej.com/2007/09/28/seemingly-impossible-functional-programs/
--   Andrej Bauer, "Seemingly Impossible Constructive Proofs" (2014)
--     https://math.andrej.com/2014/05/08/seemingly-impossible-proofs/

-- For the working mathematician:
--   Neil Strickland, "Agda for the Working Mathematician"
--     https://strickland1.org/formal/agda.pdf
--   Agda documentation & tutorial list
--     https://agda.readthedocs.io/en/latest/getting-started/tutorial-list.html
--   The Agda standard library
--     https://agda.github.io/agda-stdlib/

-- Pedagogy & classroom evidence:
--   Kevin Buzzard, "Mathematics in Type Theory" (Xena Project, 2020)
--     https://xenaproject.wordpress.com/2020/06/20/mathematics-in-type-theory/
--   Kevin Buzzard, "Formalising Mathematics" course notes (Imperial, 2024)
--     https://www.ma.imperial.ac.uk/~buzzard/xena/formalising-mathematics-2024/formalisingmathematics.pdf
--   Bottoni, Cattaneo, Sacikara, "Teaching Foundations of Math with Lean" (2025)
--     https://arxiv.org/abs/2501.03352
--   Juhosova, Zaidman, Cockx, "Pinpointing Learning Obstacles of an ITP" (ICPC, 2025)
--     https://sarajuhosova.com/assets/files/2025-icpc.pdf
--   Iannone & Thoma, "It Feels Like Cheating" (2025)
--     https://link.springer.com/article/10.1007/s40751-025-00193-w
--   Avigad, "Learning Logic and Proof with an ITP"
--     https://www.andrew.cmu.edu/user/avigad/Papers/learning_logic_and_proof.pdf
--   Kevin Buzzard, "Equality part 1: definitional equality" (Xena, 2019)
--     https://xenaproject.wordpress.com/2019/05/21/equality-part-1-definitional-equality/
--   Kevin Buzzard, "Equality, specifications, and implementations" (Xena, 2020)
--     https://xenaproject.wordpress.com/2020/07/03/equality-specifications-and-implementations/
--   Kevin Buzzard, "Grothendieck's use of equality" (2024)
--     https://arxiv.org/abs/2405.10387
--   Kevin Buzzard, guest post on Mathematics Without Apologies (2018)
--     https://mathematicswithoutapologies.wordpress.com/2018/09/11/guest-post-by-kevin-buzzard/
--   Kevin Buzzard, decidability of real equality (Mastodon, 2023)
--     https://mathstodon.xyz/@xenaproject/109958579175843725
