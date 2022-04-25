import WhileSyntax
open import WhileSemantics using (⟦_⟧ₒ)
import PQDeduction
open import PQSubstitution using (_[_/_]ᶠ ; _[_/_]ᵉ)

open import Data.Bool using (Bool; true; false)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong; cong₂; subst; [_]; inspect)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)

open import Data.Nat using (ℕ)

{-
    Here you can find HoarLogic for WHILE programming language.

    Logic is parameeterised over a (state) logic SL that can be used to reason about the state of the program.
-}
module HoareLogicForWhile where

    -- Define location type
    L = ℕ

    -- Introduce WHILE syntax that uses natural numbers as location.
    open module WhileSyntaxNat = WhileSyntax L

    -- Intrudce PQ syntax that uses natural numbers as location.
    open module PQDeductionNat = PQDeduction L

    toₚ : Bool → Formula
    toₚ false = ⊥
    toₚ true = ⊤

    -- Covert BExprₕ to Formula.
    toFormulaₚ : BExprₕ → Formula
    toFormulaₚ trueₕ = ⊤
    toFormulaₚ falseₕ = ⊥
    toFormulaₚ (¬ₕ b) = ¬ (toFormulaₚ b)
    toFormulaₚ (b₁ ∧ₕ b₂) = (toFormulaₚ b₁) ∧ (toFormulaₚ b₂)
    toFormulaₚ (b₁ ∨ₕ b₂) = (toFormulaₚ b₁) ∨ (toFormulaₚ b₂)
    toFormulaₚ (a₁ ≤ₕ a₂) = a₁ <ₑ a₂ -- TODO: Wrong conversion.


    -- Hoare triples
    data ⟪_⟫_⟪_⟫ : Formula → Cmdₕ → Formula → Set where
        
        composition   : {ϕ θ ψ : Formula}
                      → {c₁ c₂ : Cmdₕ}
                      → (⟪ ϕ ⟫ c₁ ⟪ θ ⟫)
                      → (⟪ θ ⟫ c₂ ⟪ ψ ⟫)
                      ------------------------
                      → ⟪ ϕ ⟫ (c₁ |ₕ c₂) ⟪ ψ ⟫


        assignment    : {ϕ : Formula}
                      → {a : AExprₕ}
                      → {l : L}
                      ------------------
                      → ⟪ ϕ [ a / l ]ᶠ ⟫ l :=ₕ a ⟪ ϕ ⟫

        if-statement  : {ϕ ψ : Formula}
                      → {b : BExprₕ}
                      → {c₁ c₂ : Cmdₕ}
                      → ⟪ ϕ ∧ (toFormulaₚ b) ⟫ c₁ ⟪ ψ ⟫
                      → ⟪ ϕ ∧ ¬ (toFormulaₚ b) ⟫ c₂ ⟪ ψ ⟫
                      -----------------------------------
                      → ⟪ ϕ ⟫ ifₕ b then c₁ else c₂ ⟪ ψ ⟫

        for-statement : {ϕ ψ : Formula}
                      → {a : AExprₕ}
                      → {c : Cmdₕ}
                      → ⟪ ϕ ⟫ c ⟪ ϕ ⟫
                      ----------------
                      → ⟪ ϕ ⟫ (forₕ a doo c) ⟪ ϕ ⟫

        implied       : {Δ : Hypotheses}
                      → {ϕ ϕ' ψ ψ' : Formula}
                      → {a : AExprₕ}
                      → {c : Cmdₕ}
                      → ([] ⊢ ϕ' ⇒ ϕ)
                      → ([] ⊢ ψ ⇒ ψ')
                      → ⟪ ϕ ⟫ c ⟪ ψ ⟫
                      ----------------
                      → ⟪ ϕ' ⟫ c ⟪ ψ' ⟫


    -- TODO: An alternative way of structuring Hoar triples. Not sure which one is more appropriate.
    --          Remove when no longer needed.
    -- data ⟪_⟫_⟪_⟫ : {Δ : Hypotheses} → {ϕ ψ : Formula} → (Δ ⊢ ϕ) → Cmdₕ → (Δ ⊢ ψ) → Set where
        
    --     composition : {Δ : Hypotheses}
    --                 → {ϕ θ ψ : Formula}
    --                 → {c₁ c₂ : Cmdₕ}
    --                 → {prc : Δ ⊢ ϕ}
    --                 → {mc : Δ ⊢ θ}
    --                 → {poc : Δ ⊢ ψ}
    --                 → (⟪ prc ⟫ c₁ ⟪ mc ⟫)
    --                 → (⟪ mc ⟫ c₂ ⟪ poc ⟫)
    --                 ------------------------
    --                 → ⟪ prc ⟫ (c₁ |ₕ c₂) ⟪ poc ⟫


    --     assignment  : {Δ : Hypotheses}
    --                 → {ϕ θ ψ : Formula}
    --                 → {prc : (Δ ∷ ()) ⊢ ϕ}
    --                 → {poc : Δ ⊢ ψ}
    --                 → {a : AExprₕ}
    --                 → {l : L}
    --                 ------------------
    --                 → (⟪ prc ⟫ l :=ₕ a ⟪ poc ⟫)   