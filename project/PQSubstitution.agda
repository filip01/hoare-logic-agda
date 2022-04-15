open import Data.Nat using (ℕ ; _≟_)
open import Relation.Nullary using (Dec)
open import Data.Integer using (ℤ)
open import Data.Bool using (Bool; true; false)

module PQSubstitution where

    L = ℕ

    open import PQDeduction L

    open import WhileSyntax L


    _[_/_]ᵉ : AExprₕ → AExprₕ → ℕ → AExprₕ
    (intₕ x) [ e / l ]ᵉ = (intₕ x)
    (locₕ x) [ e / l ]ᵉ with (Dec.does (l ≟ x))
    ... | false = (locₕ x)
    ... | true = e
    (-ₕ a) [ e / l ]ᵉ = (-ₕ (a [ e / l ]ᵉ))
    (a₁ +ₕ a₂) [ e / l ]ᵉ = ((a₁ [ e / l ]ᵉ) +ₕ (a₂ [ e / l ]ᵉ))

    _[_/_]ᶠ : Formula → AExprₕ → ℕ → Formula
    ⊤ [ e / l ]ᶠ = ⊤
    ⊥ [ e / l ]ᶠ = ⊥
    (ϕ₁ ∧ ϕ₂) [ e / l ]ᶠ = ((ϕ₁ [ e / l ]ᶠ) ∧ (ϕ₂ [ e / l ]ᶠ))
    (ϕ₁ ∨ ϕ₂) [ e / l ]ᶠ = ((ϕ₁ [ e / l ]ᶠ) ∨ (ϕ₂ [ e / l ]ᶠ))
    (ϕ₁ ⇒ ϕ₂) [ e / l ]ᶠ = ((ϕ₁ [ e / l ]ᶠ) ⇒ (ϕ₂ [ e / l ]ᶠ))
    (x₁ =ₑ x₂) [ e / l ]ᶠ = (x₁ [ e / l ]ᵉ) =ₑ (x₂ [ e / l ]ᵉ)
    (x₁ <ₑ x₂) [ e / l ]ᶠ = (x₁ [ e / l ]ᵉ) <ₑ (x₂ [ e / l ]ᵉ) 