open import PQDeduction

open import Data.Nat using (ℕ ; _≟_)
open import Relation.Nullary using (Dec)
open import Data.Integer using (ℤ)
open import Data.Bool using (Bool; true; false)

module PQSubstitution where

    _[_/_]ᵉ : AExprₚ → AExprₚ → ℕ → AExprₚ
    (x ₚ) [ e / l ]ᵉ = (x ₚ)
    (Locₚ x) [ e / l ]ᵉ with (Dec.does (x ≟ l))
    ... | false = (Locₚ x)
    ... | true = e
    (-ₚ a) [ e / l ]ᵉ = (-ₚ (a [ e / l ]ᵉ))
    (a₁ +ₚ a₂) [ e / l ]ᵉ = ((a₁ [ e / l ]ᵉ) +ₚ (a₂ [ e / l ]ᵉ))

    _[_/_]ᶠ : Formula → AExprₚ → ℕ → Formula
    ⊤ [ e / l ]ᶠ = ⊤
    ⊥ [ e / l ]ᶠ = ⊥
    (ϕ₁ ∧ ϕ₂) [ e / l ]ᶠ = ((ϕ₁ [ e / l ]ᶠ) ∧ (ϕ₂ [ e / l ]ᶠ))
    (ϕ₁ ∨ ϕ₂) [ e / l ]ᶠ = ((ϕ₁ [ e / l ]ᶠ) ∨ (ϕ₂ [ e / l ]ᶠ))
    (ϕ₁ ⇒ ϕ₂) [ e / l ]ᶠ = ((ϕ₁ [ e / l ]ᶠ) ⇒ (ϕ₂ [ e / l ]ᶠ))
    (x₁ =ₑ x₂) [ e / l ]ᶠ = (x₁ [ e / l ]ᵉ) =ₑ (x₂ [ e / l ]ᵉ)
    (x₁ <ₑ x₂) [ e / l ]ᶠ = (x₁ [ e / l ]ᵉ) <ₑ (x₂ [ e / l ]ᵉ)