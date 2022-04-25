open import Data.Nat using (ℕ ; _≟_)
open import Relation.Nullary using (Dec)
open import Data.Integer using (ℤ)
open import Data.Bool using (Bool; true; false)

module PQSubstitution where

    L = ℕ

    open import PQDeduction L

    open import WhileSyntax L


    _[_/_]ᵉ : AExprₕ → AExprₕ → ℕ → AExprₕ
    (intʷ x) [ e / l ]ᵉ = (intʷ x)
    (locʷ x) [ e / l ]ᵉ with (Dec.does (l ≟ x))
    ... | false = (locʷ x)
    ... | true = e
    (-ʷ a) [ e / l ]ᵉ = (-ʷ (a [ e / l ]ᵉ))
    (a₁ +ʷ a₂) [ e / l ]ᵉ = ((a₁ [ e / l ]ᵉ) +ʷ (a₂ [ e / l ]ᵉ))

    _[_/_]ᶠ : Formula → AExprₕ → ℕ → Formula
    ⊤ [ e / l ]ᶠ = ⊤
    ⊥ [ e / l ]ᶠ = ⊥
    (ϕ₁ ∧ ϕ₂) [ e / l ]ᶠ = ((ϕ₁ [ e / l ]ᶠ) ∧ (ϕ₂ [ e / l ]ᶠ))
    (ϕ₁ ∨ ϕ₂) [ e / l ]ᶠ = ((ϕ₁ [ e / l ]ᶠ) ∨ (ϕ₂ [ e / l ]ᶠ))
    (ϕ₁ ⇒ ϕ₂) [ e / l ]ᶠ = ((ϕ₁ [ e / l ]ᶠ) ⇒ (ϕ₂ [ e / l ]ᶠ))
    (x₁ =ₑ x₂) [ e / l ]ᶠ = (x₁ [ e / l ]ᵉ) =ₑ (x₂ [ e / l ]ᵉ)
    (x₁ <ₑ x₂) [ e / l ]ᶠ = (x₁ [ e / l ]ᵉ) <ₑ (x₂ [ e / l ]ᵉ) 