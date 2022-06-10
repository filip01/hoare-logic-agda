open import Data.Nat using (ℕ ; _≟_)
open import Relation.Nullary using (Dec)
open import Data.Integer using (ℤ)
open import Data.Bool using (Bool; true; false)

module PQSubstitution where

    L = ℕ

    open import PQSyntax L

    open import WhileSyntax L

    _[_/_]ᵃ : Expr → Expr → ℕ → Expr
    (int x) [ e / l ]ᵃ = (int x)
    (loc x) [ e / l ]ᵃ with (Dec.does (l ≟ x))
    ... | false = (loc x)
    ... | true = e
    (suc a) [ e / l ]ᵃ = (suc (a [ e / l ]ᵃ))
    (-ₑ a) [ e / l ]ᵃ = (-ₑ (a [ e / l ]ᵃ))
    (a₁ +ₑ a₂) [ e / l ]ᵃ = ((a₁ [ e / l ]ᵃ) +ₑ (a₂ [ e / l ]ᵃ))

    _[_/_]ᶠ : Formula → Expr → ℕ → Formula
    ⊤ [ e / l ]ᶠ = ⊤
    ⊥ [ e / l ]ᶠ = ⊥
    (ϕ₁ ∧ ϕ₂) [ e / l ]ᶠ = ((ϕ₁ [ e / l ]ᶠ) ∧ (ϕ₂ [ e / l ]ᶠ))
    (ϕ₁ ∨ ϕ₂) [ e / l ]ᶠ = ((ϕ₁ [ e / l ]ᶠ) ∨ (ϕ₂ [ e / l ]ᶠ))
    (ϕ₁ ⇒ ϕ₂) [ e / l ]ᶠ = ((ϕ₁ [ e / l ]ᶠ) ⇒ (ϕ₂ [ e / l ]ᶠ))
    (x₁ =ₑ x₂) [ e / l ]ᶠ = (x₁ [ e / l ]ᵃ) =ₑ (x₂ [ e / l ]ᵃ)
    (x₁ ≤ₑ x₂) [ e / l ]ᶠ = (x₁ [ e / l ]ᵃ) ≤ₑ (x₂ [ e / l ]ᵃ) 