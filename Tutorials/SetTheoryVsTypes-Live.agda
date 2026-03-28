{-# OPTIONS --allow-unsolved-metas #-}

module Tutorials.SetTheoryVsTypes-Live where
open import Agda.Primitive using (Level)

-- FROM SET THEORY TO DEPENDENT TYPES

-- § JUDGMENT vs PROPOSITION  
-- ────────────────────────────

-- In set theory, `x ∈ A` is a proposition.
-- It is a statement that may be true or false.
--
-- In type theory, `x : A` is a judgment. It is already a proof!
--                    ↑ 
--              `x has type A`  

--   set theory = one universe, membership is internal
--   type theory = many types (universes), typing is external


-- `⊥` has no constructors, so nothing can inhabit it.
data ⊥ : Set where

-- `⊤` has one constructor, so it has exactly one inhabitant.
record ⊤ : Set where
  constructor tt


-- § PROPOSITIONS AS TYPES:  0-th order LOGIC
-- ───────────────────────────────────────────
variable
  ℓ : Level
  A B C : Set ℓ
  P Q : A → Set ℓ
  x y z : A

-- Propositions become types, and proofs become terms.
-- A theorem is a type; to prove it is to build an inhabitant of that type.
--
--   `⊥`             means false
--   `⊤`             means true
--   `P × Q`         means P and Q
--   `P ⊎ Q`         means P or Q
--   `P → Q`         means if P then Q
--
-- A value of `A × B` stores both an `A` AND a `B`.
record _×_ (A B : Set ℓ) : Set ℓ where
  constructor _,_
  field
    fst : A
    snd : B
open _×_

-- A value of `A ⊎ B` stores either an `A` OR a `B`.
data _⊎_ (A B : Set ℓ) : Set ℓ where
  inl : A → A ⊎ B
  inr : B → A ⊎ B

-- Negation is defined as "P implies absurdity".
¬_ : Set ℓ → Set ℓ
¬ A = A → ⊥

-- EXERCISE: from `⊥`, build anything.
-- There are no cases to handle, because `⊥` has no constructors.
absurd : ⊥ → A
absurd ()

-- EXERCISE: double-negation introduction.
to-¬¬ : A → ¬ ¬ A          -- (A →f ⊥) → ⊥
to-¬¬ a f = f a

-- ──────────────────────────────────────────────────────────
-- But `¬¬ A → A` is not provable in general.
--   from-¬¬ : ¬ ¬ A → A
--   from-¬¬ f = ?
-- Recall ¬A = A → ⊥, so ¬¬A = (A → ⊥) → ⊥.
--   A proof of ¬¬A knows that denying A leads to absurdity
--    but never hands you an actual witness.
-- ──────────────────────────────────────────────────────────

-- EXERCISE: from `A × B`, build `B × A`.
×-comm : A × B → B × A
×-comm (a , b) =  b , a

-- EXERCISE: from `A ⊎ B`, build `B ⊎ A`.
⊎-comm : A ⊎ B → B ⊎ A
⊎-comm (inl x) = inr x
⊎-comm (inr x) = inl x


-- § NATURAL NUMBERS
-- `data` introduces a type by listing its constructors.
data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ


three : ℕ
three = suc (suc (suc zero))


-- 3 ≠ 4
-- {}



{-# BUILTIN NATURAL ℕ #-}  -- lets us write numerals


variable
  n m l : ℕ


--   `(x : A) → P x` means for all `x : A`, `P x`
--   `Σ A P`         means there exists `x : A` such that `P x`

-- §4  EQUALITY
-- ─────────────────────────────────────────────────
-- There are two equalities to keep apart.

-- DEFINITIONAL: equality is checked by computation.
-- PROPOSITIONAL: equality is a type that we prove.

-- Which equalities are definitional depends on the chosen definition.
infix 4 _≡_
-- `refl` works when both sides compute to the same term.
data _≡_ {A : Set ℓ} (x : A) : A → Set ℓ where
  refl : x ≡ x

{-# BUILTIN EQUALITY _≡_ #-}


-- EXAMPLE: the Definition of addition of naturals
_+_ : ℕ → ℕ → ℕ
zero  + m = m
suc n + m = suc (n + m)

-- Here addition recurses on the first argument.
-- So `2 + 2` computes to `4`.
2+2≡4 : 2 + 2 ≡ 4
2+2≡4 = refl

-- If we assume `⊥`, then `absurd` lets us prove anything.
module LeDanger where
  postulate nonsense : ⊥

  1+1≡3 : 1 + 1 ≡ 3
  1+1≡3 = absurd nonsense 

  0≡1 : 0 ≡ 1
  0≡1 = absurd nonsense


-- Because `_+_` recurses on the first argument,
-- `0 + n` reduces by definition.
+-idˡ : (n : ℕ) → 0 + n ≡ n 
+-idˡ n = refl


variable
 f : A → B 

-- But `n + 0 = n` does not reduce, so it needs a proof.
-- these are Propositionally equal but NOT Definitionally equal

-- to prove it we first need this new type:
-- If `x ≡ y`, then `f x ≡ f y`.
cong : (f : A → B) → x ≡ y → f x ≡ f y
cong f refl = refl


-- § INDUCTION IS RECURSION 
-- EXERCISE: prove `n + 0 ≡ n` by induction on `n`.
+-idʳ : (n : ℕ) → n + 0 ≡ n
+-idʳ zero = refl
+-idʳ (suc n) = cong suc (+-idʳ n)  


-- Basic operations on equality.
sym : x ≡ y → y ≡ x
sym refl = refl

trans : x ≡ y → y ≡ z → x ≡ z
trans refl q = q

-- A lemma we need for commutativity: addition and successor commute.
+-suc : (n m : ℕ) → n + suc m ≡ suc (n + m)
+-suc zero    m = refl
+-suc (suc n) m = cong suc (+-suc n m)



-- EQUATIONAL REASONING: sugar
-- IGNORE ME: ────────────────────────────┐
infix  3 _∎                               
infixr 2 step-≡                            
infix  1 begin_

begin_ : x ≡ y → x ≡ y
begin p = p

step-≡ : (x : A) → y ≡ z → x ≡ y → x ≡ z
step-≡ _ yz xy = trans xy yz

syntax step-≡ x yz xy = x ≡⟨ xy ⟩ yz
_∎ : (x : A) → x ≡ x
_ ∎ = refl
-- ───────────────────────────────────────┘
-- Ty for ignoring...

-- EXERCISE 11: the same proof in equational style.
+-comm : (n m : ℕ) → n + m ≡ m + n
+-comm n zero = +-idʳ n
+-comm n (suc m) = begin
  n + suc m    ≡⟨ +-suc n m ⟩
  suc (n + m)  ≡⟨ cong suc ( +-comm n m) ⟩
  suc (m + n)  ∎


-- ──────────────────────────────────────────────────────
-- § DEPENDENT TYPES 1th-order LOGIC a.k.a. NORMAL MATH
-- ──────────────────────────────────────────────────────
--   `(x : A) → P x` means for all `x : A`, `P x`
--   `Σ A P`         means there exists `x : A` such that `P x`

-- § EXISTENCE REQUIRES A WITNESS 
-- ─────────────────────────────────────────────────
-- `Σ A P` is a dependent pair. 
-- It stores `x : A` together with a proof of `P x`.

record Σ (A : Set ℓ) (P : A → Set ℓ) : Set ℓ where
  constructor _,,_
  field
    witness  : A
    evidence : P witness
open Σ

-- `Even n` computes to `⊤` for even numbers and `⊥` for odd ones.
Even : ℕ → Set
Even zero          = ⊤
Even (suc zero)    = ⊥
Even (suc (suc n)) = Even n

-- EXERCISE: give an even natural number together with evidence.
there-exists-an-even : Σ ℕ Even
there-exists-an-even  = 2 ,, tt


-- ─────────────────────────────────────────────────
-- AGDA IS A FULLY FLEDGED (T. complete) PROGRAMMING LANGUAGE
-- `Vec A n` is the type of lists of `A` of length `n`.
data Vec (A : Set) : ℕ → Set where
  []  : Vec A 0
  _∷_ : A → Vec A n → Vec A (suc n)

infixr 5 _∷_

-- EXERCISE: concatenation.
_++_ : Vec A n → Vec A m → Vec A (n + m)
_++_ = {!!}


-- ────────────────────────────
-- §7  A TASTE OF REAL MATH == ALGEBRA
-- ────────────────────────────
-- In type theory, a structure and its laws can live in one record.
-- Here is the type of groups.

record Group (G : Set) : Set where
  field
    ε     : G
    _·_   : G → G → G
    _⁻¹   : G → G
    assoc : ∀ x y z → (x · y) · z ≡ x · (y · z)
    idˡ   : ∀ x → ε · x ≡ x
    idʳ   : ∀ x → x · ε ≡ x
    invˡ  : ∀ x → (x ⁻¹) · x ≡ ε
    invʳ  : ∀ x → x · (x ⁻¹) ≡ ε

  infixl 7 _·_
  infix  8 _⁻¹

  -- EXERCISE: the identity is unique.
  id-unique : ∀ e → (∀ x → e · x ≡ x) → e ≡ ε
  id-unique e e-id = begin
    e      ≡⟨ sym (idʳ e) ⟩
    e · ε  ≡⟨  e-id ε ⟩
    ε      ∎

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
