import WhileSyntax
import PQDeduction
open import PQSubstitution using (_[_/_]ᶠ ; _[_/_]ᵃ)

open import Data.Bool using (Bool; true; false)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong; cong₂; subst; [_]; inspect)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)

open import Data.List using (List; []; _∷_; [_]; _++_)

open import Data.Nat using (ℕ)

--
--  Hoare logic for WHILE language with state and angelic nondeterminism
--

module AngelicHoareLogic where

    -- Define location type
    L = ℕ

    -- Introduce WHILE syntax that uses natural numbers as location.
    open module WhileSyntaxNat = WhileSyntax L

    -- Introduce PQ syntax that uses natural numbers as location.
    open module PQDeductionNat = PQDeduction L

    toₚ : Bool → Formula
    toₚ false = ⊥
    toₚ true = ⊤

    -- Covert BExprₕ to Formula.
    toFormulaₚ : BExprₕ → Formula
    toFormulaₚ True = ⊤
    toFormulaₚ False = ⊥
    toFormulaₚ (¬' b) = ¬ (toFormulaₚ b)
    toFormulaₚ (b₁ ∧' b₂) = (toFormulaₚ b₁) ∧ (toFormulaₚ b₂)
    toFormulaₚ (b₁ ∨' b₂) = (toFormulaₚ b₁) ∨ (toFormulaₚ b₂)
    toFormulaₚ (a₁ ≤' a₂) = a₁ ≤ₑ a₂

    -- Hoare triples
    data ⟪_⟫_⟪_⟫ : Formula → Cmdₕ → Formula → Set where
        
        composition   : {ϕ θ ψ : Formula}
                      → {c₁ c₂ : Cmdₕ}
                      → (⟪ ϕ ⟫ c₁ ⟪ θ ⟫)
                      → (⟪ θ ⟫ c₂ ⟪ ψ ⟫)
                      ------------------------
                      → ⟪ ϕ ⟫ (c₁ ； c₂) ⟪ ψ ⟫


        assignment    : {ϕ : Formula}
                      → {a : AExprₕ}
                      → {l : L}
                      ------------------
                      → ⟪ ϕ [ a / l ]ᶠ ⟫ l ≔ a ⟪ ϕ ⟫

        if-statement  : {ϕ ψ : Formula}
                      → {b : BExprₕ}
                      → {c₁ c₂ : Cmdₕ}
                      → ⟪ ϕ ∧ (toFormulaₚ b) ⟫ c₁ ⟪ ψ ⟫
                      → ⟪ ϕ ∧ ¬ (toFormulaₚ b) ⟫ c₂ ⟪ ψ ⟫
                      -----------------------------------
                      → ⟪ ϕ ⟫ If b Then c₁ Else c₂ ⟪ ψ ⟫

        for-statement : {ϕ ψ : Formula}
                      → {a : AExprₕ}
                      → {c : Cmdₕ}
                      → ⟪ ϕ ⟫ c ⟪ ϕ ⟫
                      ----------------
                      → ⟪ ϕ ⟫ (For a Do c) ⟪ ϕ ⟫

        implied       : {Δ : Hypotheses}
                      → {ϕ ϕ' ψ ψ' : Formula}
                      → {c : Cmdₕ}
                      → ([] ⊢ ϕ' ⇒ ϕ)
                      → ([] ⊢ ψ ⇒ ψ')
                      → ⟪ ϕ ⟫ c ⟪ ψ ⟫
                      ----------------
                      → ⟪ ϕ' ⟫ c ⟪ ψ' ⟫
    
        or-statement  : {Δ : Hypotheses}
                      → {ϕ₁ ϕ₂ ψ : Formula}
                      → {c₁ c₂ : Cmdₕ}
                      → ⟪ ϕ₁ ⟫ c₁ ⟪ ψ ⟫
                      → ⟪ ϕ₂ ⟫ c₂ ⟪ ψ ⟫
                      ----------------
                      → ⟪ ϕ₁ ∨ ϕ₂ ⟫ c₁ Or c₂ ⟪ ψ ⟫