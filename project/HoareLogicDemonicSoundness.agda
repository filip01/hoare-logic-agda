import PQDeduction --renaming (∈ to ∈ₗ)
open import PQSemantics
import WhileSemantics
open import HoareLogicForWhile
open import HProp
open import PQSubstitution

open import Data.List renaming (map to mapᴸ)

open import Data.Maybe

open import Data.Nat using (ℕ) renaming (_≟_ to _≟ℕ_)
open import Data.Integer using (ℤ; _+_; +_; _-_; -_; _≤ᵇ_) renaming (∣_∣ to abs)
open import Data.Bool using (Bool; true; false)
open import Data.Empty renaming (⊥ to ⊥ᶠ; ⊥-elim to ⊥-elimᶠ)
open import Data.Unit renaming (⊤ to ⊤ᶠ)
open import Data.Product
open import Data.Sum

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong; cong₂; subst; [_]; inspect)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)

open import Relation.Nullary renaming (¬_ to ¬ᶠ_ )

--
-- Demonic soundness of Hoar logic for While language
--

module HoareLogicDemonicSoundness where

    open WhileSyntaxNat
    open WhileSemantics renaming (⟦_⟧ to ⟦_⟧ᶜ)
    open PQDeductionNat
    
    open import MonadDef    
    open Monad NDS-Monad
    
    -- TODO: Remove when no longer needed.
    -- angelic_soundness : {P Q : Formula} {C : Cmdₕ}
    --           → ⟪ P ⟫ C ⟪ Q ⟫
    --           → ∀ {s : State}
    --             → proof (⟦ P ⟧ s)
    --             → Σ[ s' ∈ State ](
    --               (s' ∈ (mapᴸ proj₂ (⟦ C ⟧ᶜ s))) → proof (⟦ Q ⟧ s'))
    -- angelic_soundness = {!   !}

    -- Some useful lemmas
    
    dcondition : {A : Set} → (Q : Formula) → List (A × State) → HProp
    dcondition Q [] = ⊤ʰ
    dcondition Q (x ∷ sts) = (⟦ Q ⟧ (proj₂ x)) ∧ʰ dcondition Q sts

    dc-++-eq-∧ʰ : {A : Set} {Q : Formula} {ls ls' : List (A × State)}
      → proof ((dcondition Q ls) ∧ʰ (dcondition Q ls')) → proof (dcondition Q (ls ++ ls'))
    dc-++-eq-∧ʰ {_} {_} {[]} {ls'} (hₗ , hᵣ) = hᵣ
    dc-++-eq-∧ʰ {_} {_} {x ∷ ls} {ls'} (hₗ , hᵣ) = (proj₁ hₗ) , dc-++-eq-∧ʰ {_} {_} {ls} {ls'} ((proj₂ hₗ) , hᵣ)

    apply-and-fold : Cmdₕ → List (⊤ᶠ × State) → List (⊤ᶠ × State)
    apply-and-fold c ls = foldr _++_ [] (mapᴸ (λ {(_ , s) → ⟦ c ⟧ᶜ s }) ls)

    aux : {A : Set} {ls : List A} → (ls ++ []) ≡ ls
    aux {ls = []} = refl
    aux {ls = x ∷ ls} = cong (λ y → x ∷ y) aux

    dc-++-[] :  {θ : Formula} {c : Cmdₕ} {x : ⊤ᶠ × State}
      → proof (dcondition θ (⟦ c ⟧ᶜ (proj₂ x) ++ [])) → proof (dcondition θ (⟦ c ⟧ᶜ (proj₂ x)))
    dc-++-[] {_} {c} {x} h rewrite (aux {_} {⟦ c ⟧ᶜ (proj₂ x)}) = h
    
    dsoundness' : {P Q : Formula} {C : Cmdₕ}
              → ⟪ P ⟫ C ⟪ Q ⟫
              → ∀ (ls : List (⊤ᶠ × State))
                → proof (dcondition P ls)
                → proof (dcondition Q (apply-and-fold C ls))

    dsoundness' {P} {Q} {.(_ |ʷ _)} (composition {_} {_} {_} {c₁} {c₂} h₁ h₂) [] pPs = tt
    dsoundness' {P} {Q} {.(_ |ʷ _)} (composition {_} {_} {_} {c₁} {c₂} h₁ h₂) (x ∷ ls) pPs =
      dc-++-eq-∧ʰ {⊤ᶠ} {Q} {foldr _++_ [] (mapᴸ (λ { (_ , s') → ⟦ c₂ ⟧ᶜ s' }) (⟦ c₁ ⟧ᶜ (proj₂ x)))} 
         (dsoundness' h₂ (⟦ c₁ ⟧ᶜ (proj₂ x)) (dc-++-[]  {_} {c₁} {x} (dsoundness' h₁ (x ∷ []) ((proj₁ pPs) , tt))) ,
          dsoundness' (composition h₁ h₂) ls (proj₂ pPs))

    dsoundness' {.(Q [ _ / _ ]ᶠ)} {Q} {.(_ :=ʷ _)} assignment ls pPs = {!   !}

    dsoundness' {P} {Q} {.(ifʷ _ then _ else _)} (if-statement h h₁) ls pPs = {!   !}

    dsoundness' {P} {.P} {.(forʷ _ doo _)} (for-statement h) ls pPs = {!   !}
    
    dsoundness' {P} {Q} {C} (implied x x₁ h) ls pPs = {!   !}


    dsoundness : {P Q : Formula} {C : Cmdₕ}
              → ⟪ P ⟫ C ⟪ Q ⟫
              → ∀ (s : State)
                → proof (⟦ P ⟧ s)
                → proof (dcondition Q (⟦ C ⟧ᶜ s))
    dsoundness {P} {Q} {C} h s pPs = dc-++-[] {_} {C} {tt , s} (dsoundness' {P} {Q} {C} h ((tt , s) ∷ []) (pPs , tt))
         

    -- ((tt , s) ∷ [])