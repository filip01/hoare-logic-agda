import PQSyntax

open import Data.Nat using (ℕ)
open import Agda.Builtin.Equality using (_≡_)
open import Relation.Nullary using (Dec)
open import Data.Integer using (ℤ)
open import Data.Bool using (Bool; true; false)

open import Relation.Binary.Definitions using (Decidable)


--
-- Substitution for PQ logic
--

module PQSubstitution (L : Set) (_≟_ : Decidable {A = L} _≡_) where

    open import PQSyntax L

    open import WhileSyntax L

    -- Substitution for expressions
    _[_/_]ᵃ : Expr → Expr → L → Expr
    (int x) [ e / l ]ᵃ = (int x)
    (loc l') [ e / l ]ᵃ with (Dec.does (l ≟ l'))
    ... | false = (loc l')
    ... | true = e
    (suc a) [ e / l ]ᵃ = (suc (a [ e / l ]ᵃ))
    (-ₑ a) [ e / l ]ᵃ = (-ₑ (a [ e / l ]ᵃ))
    (a₁ +ₑ a₂) [ e / l ]ᵃ = ((a₁ [ e / l ]ᵃ) +ₑ (a₂ [ e / l ]ᵃ))

    -- Substitution for formulas
    _[_/_]ᶠ : Formula → Expr → L → Formula
    ⊤ [ e / l ]ᶠ = ⊤
    ⊥ [ e / l ]ᶠ = ⊥
    (ϕ₁ ∧ ϕ₂) [ e / l ]ᶠ = ((ϕ₁ [ e / l ]ᶠ) ∧ (ϕ₂ [ e / l ]ᶠ))
    (ϕ₁ ∨ ϕ₂) [ e / l ]ᶠ = ((ϕ₁ [ e / l ]ᶠ) ∨ (ϕ₂ [ e / l ]ᶠ))
    (ϕ₁ ⇒ ϕ₂) [ e / l ]ᶠ = ((ϕ₁ [ e / l ]ᶠ) ⇒ (ϕ₂ [ e / l ]ᶠ))
    (x₁ =ₑ x₂) [ e / l ]ᶠ = (x₁ [ e / l ]ᵃ) =ₑ (x₂ [ e / l ]ᵃ)
    (x₁ ≤ₑ x₂) [ e / l ]ᶠ = (x₁ [ e / l ]ᵃ) ≤ₑ (x₂ [ e / l ]ᵃ) 