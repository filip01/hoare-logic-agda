import PQSyntax
import PQDeduction
import PQSubstitution
import WhileSemantics
import WhileSyntax

open import Data.Nat using (ℕ; _≡ᵇ_)

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

    -- Define type for locations
    L = ℕ

    module PQSyntaxℕ = PQSyntax L
    open PQSyntaxℕ
    
    module PQDeductionℕ = PQDeduction L _≡ᵇ_
    open PQDeductionℕ

    module PQSubstitutionℕ = PQSubstitution L _≡ᵇ_
    open PQSubstitutionℕ

    module WhileSemanticsℕ = WhileSemantics L
    open WhileSemanticsℕ

    module WhileSyntaxℕ = WhileSyntax L
    open WhileSyntaxℕ


    toₚ : Bool → Formula
    toₚ false = ⊥
    toₚ true = ⊤

    -- Covert AExprₕ to Expr.
    toExprₚ : AExprₕ → Expr
    toExprₚ (Int x) = int x
    toExprₚ (Loc x) = loc x
    toExprₚ (-' e) = -ₑ (toExprₚ e)
    toExprₚ (e₁ +' e₂) = ((toExprₚ e₁) +ₑ (toExprₚ e₂))

    -- Covert BExprₕ to Formula.
    toFormulaₚ : BExprₕ → Formula
    toFormulaₚ True = ⊤
    toFormulaₚ False = ⊥
    toFormulaₚ (¬' b) = ¬ (toFormulaₚ b)
    toFormulaₚ (b₁ ∧' b₂) = (toFormulaₚ b₁) ∧ (toFormulaₚ b₂)
    toFormulaₚ (b₁ ∨' b₂) = (toFormulaₚ b₁) ∨ (toFormulaₚ b₂)
    toFormulaₚ (a₁ ≤' a₂) = (toExprₚ a₁) ≤ₑ (toExprₚ a₂)

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
                      → ⟪ ϕ [ (toExprₚ a) / l ]ᶠ ⟫ l ≔ a ⟪ ϕ ⟫

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