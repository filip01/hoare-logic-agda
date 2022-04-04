{-
   Allowing overlapping instances for `∈` to use in `hyp`.

   Warning: If used carelessly, could lead to exponential
   slowdown and looping behaviour during instance search.
-}

{-# OPTIONS --overlapping-instances #-}

module PQSemantics (AtomicFormula : Set) where

{-
   Imports from the standard library.
-}

open import Data.Product

import Relation.Binary.PropositionalEquality as Eq
open Eq renaming ([_] to [|_|])
open Eq.≡-Reasoning

open import Data.Nat using (ℕ ; suc ; _≟_) renaming (_<ᵇ_ to _ℕ<ᵇ_)
open import Data.Integer using (ℤ; _+_; +_; _-_; -_; _≤ᵇ_) renaming (∣_∣ to abs; _≟_ to _≟ℤ_)

{-
   Importing the deeply embedded propositional logic together with its
   natural dediction proof system, parametrised by atomic formulae type.
-}

import PQDeduction
open module ND = PQDeduction AtomicFormula

open import HProp

{-
   Importing a custom inequational reasoning module that provides a
   `beginᵇ` and `∎ᵇ` style reasoning for the `≤` relation on `Bool`.

   A typical proof with this equational reasoning machinery looks like

     beginᵇ
       lhs
     ≤⟨ reason why `lhs ≤ intermediate-result` ⟩
       intermediate-result
     ≡ᵇ⟨ reason why `intermediate-result ≡ rhs` ⟩
       rhs
     ∎ᵇ

   Notice the superscript `ᵇ` to distinguish this reasoning from
   `begin` and `∎` style equational reasoning for `≡`. You can
   get the superscript symbol `ᵇ` in unicode by typing \^b.
-}

-- open import Sol5.≤-Reasoning

{-
   The universe of truth values into which we interpret our logic.

   As we are interpreting propositional logic, we shall just use
   booleans. For predicate logics (e.g., in your projects), you will
   want to choose something different as the interpretation target.

   While the propositional logic we interpret is intuitionistic,
   this boolean semantics also models classical logical axioms.
   We will make this claim precise in Exercise 9 below.
-}

ℙ = HProp   -- unicode \bP

{-
   Environments/valuations assigning truth values to atomic formulae.
-}

L = ℕ
-- Env = AtomicFormula → ℙ
State = L → ℤ

----------------
-- Exercise 6 --
----------------

{-
   Define logical implication between boolean values.
-}

-- _implies_ : ℙ → ℙ → ℙ
-- b₁ implies b₂ = not b₁ or b₂

{-
   The recursively defined interpretation function for formulae.
-}

postulate ⟦_⟧ₑ : AExprₚ → State → ℤ

_=ₑₕ_ : ℤ → ℤ → HProp
x =ₑₕ y = {!   !}

_<ₑₕ_ : ℤ → ℤ → HProp
x <ₑₕ y = {!   !}

⟦_⟧ : Formula → State → ℙ
-- ⟦ ` x ⟧ S = {!   !}
⟦ ⊤ ⟧ S = ⊤ʰ
⟦ ⊥ ⟧ S = ⊥ʰ
⟦ P₁ ∧ P₂ ⟧ S = ⟦ P₁ ⟧ S ∧ʰ ⟦ P₂ ⟧ S
⟦ P₁ ∨ P₂ ⟧ S = ⟦ P₁ ⟧ S ∨ʰ ⟦ P₂ ⟧ S
⟦ P₁ ⇒ P₂ ⟧ S = ⟦ P₁ ⟧ S ⇒ʰ ⟦ P₂ ⟧ S
⟦ x₁ =ₑ x₂ ⟧ S = (⟦ x₁ ⟧ₑ S) =ₑₕ (⟦ x₂ ⟧ₑ S)
⟦ x₁ <ₑ x₂ ⟧ S = (⟦ x₁ ⟧ₑ S) <ₑₕ (⟦ x₂ ⟧ₑ S)

{-
   The interpretation function is also extended to hypotheses.
-}

-- ⟦_⟧ₑ : Hypotheses → Env → ℙ             -- unicode \[[ \]] \_e