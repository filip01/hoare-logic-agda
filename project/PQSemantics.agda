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
open Eq using (_≡_; refl; sym; trans; cong; cong₂; subst; inspect) renaming ([_] to [|_|])
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; step-≡˘; _∎)

open import Data.Nat using (ℕ ; suc ; _≟_) renaming (_<ᵇ_ to _ℕ<ᵇ_)
open import Data.Integer using (ℤ; _+_; +_; _-_; -_; _≤ᵇ_) renaming (∣_∣ to abs; _≟_ to _≟ℤ_)
open import Data.Bool

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

-- open import ≤-Reasoning

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
x =ₑₕ y = ⟨ x ≡ y , (λ {refl refl → refl}) ⟩

_<ₑₕ_ : ℤ → ℤ → HProp
x <ₑₕ y = ⟨ (x ≤ᵇ y) ≡ true , ≤ᵇ≡true-is-prop x y ⟩
   where
      ≤ᵇ≡true-is-prop : (x y : ℤ) → is-proposition ((x ≤ᵇ y) ≡ true)
      ≤ᵇ≡true-is-prop x y p q with x ≤ᵇ y
      ≤ᵇ≡true-is-prop x y refl refl | true = refl
{-
x <ₑₕ y with x ≤ᵇ y
... | b = ⟨ (x ≤ᵇ y) ≡ true , (λ p q → {!   !}) ⟩
-}

⟦_⟧ : Formula → State → ℙ
⟦ ⊤ ⟧ s = ⊤ʰ
⟦ ⊥ ⟧ s = ⊥ʰ
⟦ P₁ ∧ P₂ ⟧ S = ⟦ P₁ ⟧ S ∧ʰ ⟦ P₂ ⟧ S
⟦ P₁ ∨ P₂ ⟧ S = ⟦ P₁ ⟧ S ∨ʰ ⟦ P₂ ⟧ S
⟦ P₁ ⇒ P₂ ⟧ S = ⟦ P₁ ⟧ S ⇒ʰ ⟦ P₂ ⟧ S
⟦ x₁ =ₑ x₂ ⟧ S = (⟦ x₁ ⟧ₑ S) =ₑₕ (⟦ x₂ ⟧ₑ S)
⟦ x₁ <ₑ x₂ ⟧ S = (⟦ x₁ ⟧ₑ S) <ₑₕ (⟦ x₂ ⟧ₑ S)

{-
   The interpretation function is also extended to hypotheses.
-}

⟦_⟧ₕ : Hypotheses → State → ℙ
⟦ [] ⟧ₕ s = ⊤ʰ
⟦ P ∷ Δ ⟧ₕ s = ⟦ P ⟧ s ∧ʰ ⟦ Δ ⟧ₕ s

⟦_⟧ₓ : {Δ : Hypotheses} → {φ : Formula} → (Δ ⊢ φ) → 
      ∀ {s : State} → proof (⟦ Δ ⟧ₕ s) -> proof (⟦ φ ⟧ s)

⟦ weaken {Δ₁} {Δ₂} φ {ψ} h ⟧ₓ {s} p = {!   !}
⟦ PQDeduction.contract φ h ⟧ₓ {s} p = {!   !}
⟦ PQDeduction.exchange φ₁ φ₂ h ⟧ₓ {s} p = {!   !}
⟦ PQDeduction.hyp _ ⟧ₓ {s} p = {!   !}
⟦ PQDeduction.⊤-intro ⟧ₓ {s} p = {!   !}
⟦ PQDeduction.⊥-elim h ⟧ₓ {s} p = {!   !}
⟦ PQDeduction.∧-intro h h₁ ⟧ₓ {s} p = {!   !}
⟦ PQDeduction.∧-elim₁ h ⟧ₓ {s} p = {!   !}
⟦ PQDeduction.∧-elim₂ h ⟧ₓ {s} p = {!   !}
⟦ PQDeduction.∨-intro₁ h ⟧ₓ {s} p = {!   !}
⟦ PQDeduction.∨-intro₂ h ⟧ₓ {s} p = {!   !}
⟦ PQDeduction.∨-elim h h₁ h₂ ⟧ₓ {s} p = {!   !}
⟦ PQDeduction.⇒-intro h ⟧ₓ {s} p = {!   !}
⟦ PQDeduction.⇒-elim h h₁ ⟧ₓ {s} p = {!   !}
⟦ PQDeduction.=ₑ-intro ⟧ₓ {s} p = {!   !}
⟦ PQDeduction.=ₑ-refl h ⟧ₓ {s} p = {!   !}
⟦ PQDeduction.=ₑ-trans h h₁ ⟧ₓ {s} p = {!   !}
⟦ PQDeduction.<ₑ-add h ⟧ₓ {s} p = {!   !}
⟦ PQDeduction.+ₚ-zero ⟧ₓ {s} p = {!   !}
⟦ PQDeduction.+ₚ-comm ⟧ₓ {s} p = {!   !}