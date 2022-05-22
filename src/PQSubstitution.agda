open import Data.Nat using (ℕ ; _≟_)
open import Relation.Nullary using (Dec)
open import Data.Integer using (ℤ)
open import Data.Bool using (Bool; true; false)

module PQSubstitution where

    L = ℕ

    open import PQDeduction L

    open import WhileSyntax L

    _[_/_]ᵃ : AExprₕ → AExprₕ → ℕ → AExprₕ
    (intʷ x) [ e / l ]ᵃ = (intʷ x)
    (locʷ x) [ e / l ]ᵃ with (Dec.does (l ≟ x))
    ... | false = (locʷ x)
    ... | true = e
    (-ʷ a) [ e / l ]ᵃ = (-ʷ (a [ e / l ]ᵃ))
    (a₁ +ʷ a₂) [ e / l ]ᵃ = ((a₁ [ e / l ]ᵃ) +ʷ (a₂ [ e / l ]ᵃ))

    _[_/_]ᶠ : Formula → AExprₕ → ℕ → Formula
    ⊤ [ e / l ]ᶠ = ⊤
    ⊥ [ e / l ]ᶠ = ⊥
    (ϕ₁ ∧ ϕ₂) [ e / l ]ᶠ = ((ϕ₁ [ e / l ]ᶠ) ∧ (ϕ₂ [ e / l ]ᶠ))
    (ϕ₁ ∨ ϕ₂) [ e / l ]ᶠ = ((ϕ₁ [ e / l ]ᶠ) ∨ (ϕ₂ [ e / l ]ᶠ))
    (ϕ₁ ⇒ ϕ₂) [ e / l ]ᶠ = ((ϕ₁ [ e / l ]ᶠ) ⇒ (ϕ₂ [ e / l ]ᶠ))
    (x₁ =ₑ x₂) [ e / l ]ᶠ = (x₁ [ e / l ]ᵃ) =ₑ (x₂ [ e / l ]ᵃ)
    (x₁ ≤ₑ x₂) [ e / l ]ᶠ = (x₁ [ e / l ]ᵃ) ≤ₑ (x₂ [ e / l ]ᵃ) 