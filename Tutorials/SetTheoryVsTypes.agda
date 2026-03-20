module Tutorials.SetTheoryVsTypes where

-- ═══════════════════════════════════════════════════════════════════════
-- FROM SET THEORY TO DEPENDENT TYPES
-- A 30-minute interactive tutorial for pure mathematicians
--
-- "If you have a BSc or MSc in mathematics, you already know
--  everything in this file.  You just know it under different names."
--
-- Style: everything from scratch.  No imports, no libraries.
-- Each definition builds on the last.  The machine checks every step.
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

-- In ZFC, "x ∈ A" is a PROPOSITION — a statement inside the system.
-- It can be true or false.  You prove or disprove it.
--
--   3 ∈ ℕ     (true)
--   3 ∈ ℤ     (true)
--   3 ∈ ℝ     (true)
--   π ∈ ℚ     (false, and this is a theorem)
--
-- An element can belong to many sets.  ℕ ⊂ ℤ ⊂ ℚ ⊂ ℝ ⊂ ℂ.
-- "Is the monster group a real number?" is a grammatically valid
-- question in ZFC.  (The answer is no, but you need a proof.)
--
-- In type theory, "x : A" is a JUDGMENT — a statement ABOUT the system.
-- It is not something you prove.  It is static, unchallengeable
-- information, like the declaration of a variable's type in algebra.
--
--   3 : ℕ
--
-- Full stop.  3 does not simultaneously have type ℤ.
-- If you want an integer 3, that is a DIFFERENT term, built differently.
-- "Is the monster group a real number?" is not even a well-formed
-- question — it is a type error, caught before any mathematics begins.
--
-- This is the deepest shift:
--   set theory = one universe, membership is internal
--   type theory = many types, typing is external

-- A type is defined by its CONSTRUCTORS — the ways to build elements.
--
-- READING AGDA SYNTAX:
-- "data" lists constructors — the ONLY ways to build elements (an inductive defn).
-- "Set" = the type of types (a universe).  "ℕ : Set" means "ℕ is a type."
-- "→" = function arrow.  "A → B" = functions from A to B.

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
-- §2  PROPOSITIONS AS TYPES  (Curry 1934, Howard 1969)
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

-- Ex falso quodlibet: from ⊥, anything follows.
--
-- {A : Set} means A is IMPLICIT — Agda infers it, so you write "absurd x"
-- not "absurd ℕ x".  Think: universally quantified but never written down.
--
-- Since ⊥ has NO constructors, there are ZERO cases to handle.
-- "()" tells Agda "this case is impossible" — the proof is vacuously complete.
absurd : {A : Set} → ⊥ → A
absurd ()

-- P ∧ Q ⟹ Q ∧ P: swap the pair.
-- Pattern matching "(a , b)" on the left of "=" decomposes the input.
×-comm : {A B : Set} → A × B → B × A
×-comm (a , b) = b , a

-- P ∨ Q ⟹ Q ∨ P: swap the tag.
-- Exhaustive case analysis — one clause per constructor, like "proof by cases."
⊎-comm : {A B : Set} → A ⊎ B → B ⊎ A
⊎-comm (inl a) = inr a
⊎-comm (inr b) = inl b

-- These are not just proofs — they are programs you can run on data.


-- ┌─────────────────────────────────────────────────────────┐
-- │  ACT II.  THE DIVERGENCE                                │
-- │  Where type theory and classical mathematics part ways  │
-- └─────────────────────────────────────────────────────────┘

-- ─────────────────────────────────────────────────
-- §3  EXISTENCE REQUIRES A WITNESS  (Bauer, 2016)
-- ─────────────────────────────────────────────────

-- Andrej Bauer describes five stages of accepting constructive math,
-- parallel to the stages of grief.  The crux:
--
-- In classical math you routinely prove ∃x.P(x) by:
--   "Suppose no such x exists.  Then ... contradiction.  ∴ ∃x.P(x)."
-- The witness x is never produced.
--
-- In type theory, a proof of "there exists x in A such that P(x)"
-- IS a pair:  (x , evidence-that-P-holds-for-x).
-- You MUST hand over the witness.  No exceptions.
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
Even : ℕ → Set
Even zero          = ⊤
Even (suc zero)    = ⊥
Even (suc (suc n)) = Even n

-- "There exists an even natural number."  We exhibit the witness.
there-exists-an-even : Σ ℕ Even
there-exists-an-even = 4 ,, tt    -- witness: 4.  evidence: Even 4 reduces to ⊤.

-- DOUBLE NEGATION: the boundary of constructivism.
-- A → ¬¬A is always provable.  But ¬¬A → A is not.
-- Recall ¬A = A → ⊥, so ¬¬A = (A → ⊥) → ⊥.
-- A proof of ¬¬A knows that denying A leads to absurdity — but it
-- never hands you an actual witness of A.
to-¬¬ : {A : Set} → A → ¬ ¬ A
to-¬¬ a f = f a     -- Given a : A and f : A → ⊥, we apply f to a to get ⊥.

-- Try this and get stuck:
--   from-¬¬ : {A : Set} → ¬ ¬ A → A
--   from-¬¬ f = ?   -- f : (A → ⊥) → ⊥.  No way to extract an A.

-- Three of the four quantifier De Morgan laws are constructive.  The fourth is not.

¬∃⇒∀¬ : {A : Set} {P : A → Set} → ¬ Σ A P → (x : A) → ¬ P x
¬∃⇒∀¬ f x px = f (x ,, px)

∃¬⇒¬∀ : {A : Set} {P : A → Set} → Σ A (λ x → ¬ P x) → ¬ ((x : A) → P x)
∃¬⇒¬∀ (x ,, ¬px) f = ¬px (f x)

∀¬⇒¬∃ : {A : Set} {P : A → Set} → ((x : A) → ¬ P x) → ¬ Σ A P
∀¬⇒¬∃ f (x ,, px) = f x px

-- THE WALL: ¬∀ ⟹ ∃¬ requires excluded middle.
-- Knowing a universal fails does not hand you a counterexample.
-- "postulate" declares a term without definition — an axiom.
-- "λ x →" is an anonymous function (like "x ↦" in math).
postulate
  classical-escape : {A : Set} {P : A → Set}
    → ¬ ((x : A) → P x) → Σ A (λ x → ¬ P x)

-- NOTE (Escardó): type theory is not anti-classical — it is pre-classical.
-- LEM and choice are CONSISTENT; you just lose computation (proofs using
-- LEM don't reduce to normal forms).  You can always postulate them.

-- ─────────────────────────────────────────────────
-- §4  EQUALITY: two notions where you had one
-- ─────────────────────────────────────────────────

-- Existence required a witness.  Equality has a similar surprise.
-- In set theory, a = b.  One notion.
-- In type theory, TWO:
--   (1) DEFINITIONAL — the machine checks by computation.  Free.
--   (2) PROPOSITIONAL — a type you inhabit with a proof.  May cost work.
-- Why two?  Because definitions have a computational direction:
-- _+_ recurses on its FIRST argument, so (0 + n) reduces but (n + 0) does not.

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

-- 2 + 2 computes to 4, so refl suffices.
2+2≡4 : 2 + 2 ≡ 4
2+2≡4 = refl

-- Postulate ⊥ and the system collapses — like an inconsistent axiom set.
-- "module" creates a local scope (sandbox).

module Danger where
  postulate oops : ⊥              -- assert that falsehood holds

  1+1≡3 : 1 + 1 ≡ 3              -- sure, why not
  1+1≡3 = absurd oops

  0≡1 : 0 ≡ 1                    -- arithmetic is dead
  0≡1 = absurd oops

-- Outside the module, oops is gone.  --safe forbids postulates entirely.

-- 0 + n reduces to n by definition.
+-idˡ : (n : ℕ) → 0 + n ≡ n
+-idˡ _ = refl

-- But n + 0 does NOT reduce — n is a variable, so _+_ is stuck.  We need induction.

-- Congruence (Leibniz): matching on refl unifies x with y, making the goal trivial.
cong : {A B : Set} {x y : A} (f : A → B) → x ≡ y → f x ≡ f y
cong f refl = refl

+-idʳ : (n : ℕ) → n + 0 ≡ n
+-idʳ zero    = refl
+-idʳ (suc n) = cong suc (+-idʳ n)  -- recursive call = induction hypothesis

-- ▸ KEY INSIGHT:  0 + n = n is free (computation).  n + 0 = n costs induction.
-- In a textbook both are equally trivial.  Definitions have a direction.


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
-- checker replaces "well-founded induction."  No axiom needed.

-- Symmetry and transitivity: matching on refl unifies both sides.
sym : {A : Set} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

trans : {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl q = q

+-suc : (n m : ℕ) → n + suc m ≡ suc (n + m)
+-suc zero    m = refl
+-suc (suc n) m = cong suc (+-suc n m)

-- Commutativity of addition.
+-comm : (n m : ℕ) → n + m ≡ m + n
+-comm n zero    = +-idʳ n
+-comm n (suc m) = trans (+-suc n m) (cong suc (+-comm n m))

-- Equational reasoning: syntactic sugar for chains of "trans".
-- Usage:  x ≡⟨ reason₁ ⟩  y ≡⟨ reason₂ ⟩  z ∎
-- You do not need to understand the definitions — just the pattern.
infix  3 _∎
infixr 2 step-≡
infix  1 begin_

begin_ : {A : Set} {x y : A} → x ≡ y → x ≡ y
begin p = p

step-≡ : {A : Set} (x : A) {y z : A} → y ≡ z → x ≡ y → x ≡ z
step-≡ _ yz xy = trans xy yz

syntax step-≡ x yz xy = x ≡⟨ xy ⟩ yz

_∎ : {A : Set} (x : A) → x ≡ x
_ ∎ = refl

-- Same proof as +-comm, in blackboard style.
+-comm′ : (n m : ℕ) → n + m ≡ m + n
+-comm′ n zero = +-idʳ n
+-comm′ n (suc m) = begin
  n + suc m    ≡⟨ +-suc n m ⟩
  suc (n + m)  ≡⟨ cong suc (+-comm′ n m) ⟩
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

Fin0-empty : Fin 0 → ⊥
Fin0-empty ()

-- Vec A n: a list whose length n is tracked in the TYPE.
data Vec (A : Set) : ℕ → Set where
  []  : Vec A 0
  _∷_ : {n : ℕ} → A → Vec A n → Vec A (suc n)

infixr 5 _∷_

-- Concatenation.  In a textbook, "|xs ++ ys| = |xs| + |ys|" is a separate
-- lemma.  Here the type signature IS the lemma, and the definition IS the proof.
_++_ : {A : Set} {n m : ℕ} → Vec A n → Vec A m → Vec A (n + m)
[]       ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

-- Safe indexing.  Out-of-bounds is a type error, not a runtime error.
lookup : {A : Set} {n : ℕ} → Vec A n → Fin n → A
lookup (x ∷ _)  zero    = x
lookup (_ ∷ xs) (suc i) = lookup xs i
-- No [] case: the index would need type Fin 0, which is empty.

-- McBride: "pay-as-you-go correctness" — encode more in the type,
-- the machine checks more.  One more example of specifications-as-types:

half : (n : ℕ) → Even n → ℕ
half zero          _  = 0
half (suc (suc n)) ev = suc (half n ev)
-- No case for n = 1: Even 1 = ⊥, so the call can never be made.


-- ─────────────────────────────────────────────────
-- §7  A TASTE OF REAL ALGEBRA
-- ─────────────────────────────────────────────────

-- We have all the ingredients.  Types encode data (ℕ, Vec, Fin).
-- Types encode propositions (_≡_, Even).  Types encode specifications
-- (Vec n guarantees length, Even n guards half).  Now let us put
-- it all together: a group, with the same axioms as any algebra
-- textbook, but machine-checked.  Since propositions are types,
-- operations and axioms live together in one record.  "∀ x" = "(x : G) →".

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

  -- The identity is unique.
  id-unique : ∀ e → (∀ x → e · x ≡ x) → e ≡ ε
  id-unique e e-id = begin
    e      ≡⟨ sym (idʳ e) ⟩
    e · ε  ≡⟨ e-id ε ⟩
    ε      ∎

  -- (x⁻¹)⁻¹ = x.
  inv-inv : ∀ x → (x ⁻¹) ⁻¹ ≡ x
  inv-inv x = begin
    (x ⁻¹) ⁻¹                        ≡⟨ sym (idʳ _) ⟩
    ((x ⁻¹) ⁻¹) · ε                  ≡⟨ cong (λ e → ((x ⁻¹) ⁻¹) · e) (sym (invˡ x)) ⟩
    ((x ⁻¹) ⁻¹) · ((x ⁻¹) · x)      ≡⟨ sym (assoc _ _ _) ⟩
    (((x ⁻¹) ⁻¹) · (x ⁻¹)) · x      ≡⟨ cong (λ e → e · x) (invˡ (x ⁻¹)) ⟩
    ε · x                             ≡⟨ idˡ x ⟩
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
