import PQDeduction
open import PQSemantics
import WhileSemantics
open import HoareLogicForWhile
open import HProp
open import PQSubstitution

open import Data.Nat using (ℕ)
open import Data.Bool using (Bool; true; false)
open import Data.Empty renaming (⊥ to ⊥ᶠ; ⊥-elim to ⊥-elimᶠ)
open import Data.Unit renaming (⊤ to ⊤ᶠ)
open import Data.Product
open import Data.Sum

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong; cong₂; subst; [_]; inspect)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)

open import Relation.Nullary renaming (¬_ to ¬ᶠ_ )

module HoareLogicSoundness where

    open WhileSyntaxNat
    open WhileSemantics renaming (⟦_⟧ to ⟦_⟧ᶜ)
    open PQDeductionNat

    is-proposition' : {s : State} {b₁ b₂ : BExprₕ} → 
      (∥ proof (⟦ toFormulaₚ b₁ ⟧ s) ⊎ proof (⟦ toFormulaₚ b₂ ⟧ s) ∥) →
        (proof (⟦ toFormulaₚ b₁ ⟧ s) ⊎ proof (⟦ toFormulaₚ b₂ ⟧ s))
    is-proposition' {s} {b₁} {b₂} p = ∥∥-elim {! is-proposition  !} {!   !} {!   !}
    
    interleaved mutual

      aux  : {s : State} → {b : BExprₕ} → (⟦ b ⟧ₒ s ≡ true) → (proof (⟦ toFormulaₚ b ⟧ s))
      aux' : {s : State} → {b : BExprₕ} → (⟦ b ⟧ₒ s ≡ false) → ¬ᶠ (proof (⟦ toFormulaₚ b ⟧ s))

      aux  {s} {trueₕ} p = tt
      aux' {s} {trueₕ} ()
    
      aux  {s} {¬ₕ b} p x with ⟦ b ⟧ₒ s | inspect ⟦ b ⟧ₒ s
      ... | false | Eq.[ eq ] = aux' {s} {b} eq  x
      aux' {s} {¬ₕ b} p x with ⟦ b ⟧ₒ s | inspect ⟦ b ⟧ₒ s
      ... | true | Eq.[ eq ] = x (aux {s} {b} eq)

      aux  {s} {b₁ ∧ₕ b₂} x with ⟦ b₁ ⟧ₒ s | ⟦ b₂ ⟧ₒ s |  inspect ⟦ b₁ ⟧ₒ s | inspect ⟦ b₂ ⟧ₒ s
      ... | true | true | Eq.[ eq₁ ] | Eq.[ eq₂ ] = aux {s} {b₁} eq₁ , aux {s} {b₂} eq₂
      aux' {s} {b₁ ∧ₕ b₂} x x' with ⟦ b₁ ⟧ₒ s | ⟦ b₂ ⟧ₒ s |  inspect ⟦ b₁ ⟧ₒ s | inspect ⟦ b₂ ⟧ₒ s
      ... | false | false | Eq.[ eq₁ ] | Eq.[ eq₂ ] = aux' {s} {b₁} eq₁ (proj₁ x')
      ... | false | true | Eq.[ eq₁ ] | Eq.[ eq₂ ] = aux' {s} {b₁} eq₁ (proj₁ x')
      ... | true | false | Eq.[ eq₁ ] | Eq.[ eq₂ ] = aux' {s} {b₂} eq₂ (proj₂ x')

      aux  {s} {b₁ ∨ₕ b₂} x with ⟦ b₁ ⟧ₒ s | ⟦ b₂ ⟧ₒ s |  inspect ⟦ b₁ ⟧ₒ s | inspect ⟦ b₂ ⟧ₒ s
      ... | false | true | Eq.[ eq₁ ] | Eq.[ eq₂ ] = ∣ inj₂ (aux {s} {b₂} eq₂) ∣
      ... | true | false | Eq.[ eq₁ ] | Eq.[ eq₂ ] = ∣ inj₁ (aux {s} {b₁} eq₁) ∣
      ... | true | true | Eq.[ eq₁ ] | Eq.[ eq₂ ] = ∣ inj₁ (aux {s} {b₁} eq₁) ∣
      aux' {s} {b₁ ∨ₕ b₂} x x' with ⟦ b₁ ⟧ₒ s | ⟦ b₂ ⟧ₒ s |  inspect ⟦ b₁ ⟧ₒ s | inspect ⟦ b₂ ⟧ₒ s
      ... | false | false | Eq.[ eq₁ ] | Eq.[ eq₂ ] with (is-proposition' {s} {b₁} {b₂} x')
      ... | inj₁ y = aux' {s} {b₁} eq₁ y
      ... | inj₂ y = aux' {s} {b₂} eq₂ y
      

    soundness : {P Q : Formula} → {C : Cmdₕ}
              → ⟪ P ⟫ C ⟪ Q ⟫
              → ∀ {s : State}
                → proof (⟦ P ⟧ s)
                → proof (⟦ Q ⟧ (⟦ C ⟧ᶜ s))

    soundness {P} {Q} {.(_ |ₕ _)} (composition {P} {R} {Q} {c₁} {c₂} h₁ h₂) pP = soundness h₂ (soundness h₁ pP)
    
    soundness {.(_ [ _ / _ ]ᶠ)} {Q} {.( _ :=ₕ _)} (assignment {P} {Q} {a}) pP = {!  !}

    soundness {P} {Q} {.(ifₕ _ then _ else _)} (if-statement {P} {Q} {b} h₁ h₂) {s} pP with (⟦ b ⟧ₒ s) | inspect ⟦ b ⟧ₒ s 
    ... | false | Eq.[ eq ] = soundness h₂ (pP , λ x → aux' {s} {b} eq x )
    ... | true | Eq.[ eq ] = soundness h₁ (pP , aux {s} {b} eq)
    

    soundness {P} {Q} {.(forₕ _ doo _)} (for-statement h) pP = {!   !}
    
    soundness {P} {Q} {C} (implied x x₁ h) pP = {!   !}
    
    --soundness {P} {Q} {_ |ₕ _} (composition {P} {R} {Q} {c₁} {c₂} h₁ h₂) pP = {! sounness    !}         