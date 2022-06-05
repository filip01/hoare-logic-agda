open import Data.Nat using (ℕ ; _≟_)
open import Relation.Nullary using (Dec)
open import Data.Integer using (ℤ)
open import Data.Bool using (Bool; true; false)

module PQSubstitution where

    L = ℕ

    open import PQDeduction L

    open import WhileSyntax L

    _[_/_]ᵃ : AExprₕ → AExprₕ → ℕ → AExprₕ
    (Int x) [ e / l ]ᵃ = (Int x)
    (Loc x) [ e / l ]ᵃ with (Dec.does (l ≟ x))
    ... | false = (Loc x)
    ... | true = e
    (-' a) [ e / l ]ᵃ = (-' (a [ e / l ]ᵃ))
    (a₁ +' a₂) [ e / l ]ᵃ = ((a₁ [ e / l ]ᵃ) +' (a₂ [ e / l ]ᵃ))

    _[_/_]ᶠ : Formula → AExprₕ → ℕ → Formula
    ⊤ [ e / l ]ᶠ = ⊤
    ⊥ [ e / l ]ᶠ = ⊥
    (ϕ₁ ∧ ϕ₂) [ e / l ]ᶠ = ((ϕ₁ [ e / l ]ᶠ) ∧ (ϕ₂ [ e / l ]ᶠ))
    (ϕ₁ ∨ ϕ₂) [ e / l ]ᶠ = ((ϕ₁ [ e / l ]ᶠ) ∨ (ϕ₂ [ e / l ]ᶠ))
    (ϕ₁ ⇒ ϕ₂) [ e / l ]ᶠ = ((ϕ₁ [ e / l ]ᶠ) ⇒ (ϕ₂ [ e / l ]ᶠ))
    (x₁ =ₑ x₂) [ e / l ]ᶠ = (x₁ [ e / l ]ᵃ) =ₑ (x₂ [ e / l ]ᵃ)
    (x₁ ≤ₑ x₂) [ e / l ]ᶠ = (x₁ [ e / l ]ᵃ) ≤ₑ (x₂ [ e / l ]ᵃ) 