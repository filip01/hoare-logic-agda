import PQDeduction
open import PQSemantics
import WhileSemantics
open import HoareLogicForWhile
open import HProp
open import PQSubstitution

open import Data.Nat using (ℕ)
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

module HoareLogicSoundness where

    open WhileSyntaxNat
    open WhileSemantics renaming (⟦_⟧ to ⟦_⟧ᶜ)
    open PQDeductionNat


    trueIsNotEqToFalse : (true ≡ false) → ⊥ᶠ
    trueIsNotEqToFalse ()

    --
    -- Relate how the boolean expressions are interpreted in WHILE language and how they are interpreted in the
    -- PQ logic.
    --
    
    interleaved mutual

      -- If `b` evaluates to true, then there exist a witness of `⟦ toFormulaₚ b ⟧ s`.
      bIsTrueFollows  : {s : State} → {b : BExprₕ} → (⟦ b ⟧ₒ s ≡ true) → (proof (⟦ toFormulaₚ b ⟧ s))
      -- If `b` evaluates to false, then there does NOT exist a witness of `⟦ toFormulaₚ b ⟧ s`.
      bIsFalseFollows : {s : State} → {b : BExprₕ} → (⟦ b ⟧ₒ s ≡ false) → ¬ᶠ (proof (⟦ toFormulaₚ b ⟧ s))

      bIsTrueFollows  {s} {trueₕ} p = tt
      bIsFalseFollows {s} {trueₕ} ()
    
      bIsTrueFollows  {s} {¬ₕ b} p x with ⟦ b ⟧ₒ s | inspect ⟦ b ⟧ₒ s
      ... | false | Eq.[ eq ] = bIsFalseFollows {s} {b} eq  x
      bIsFalseFollows {s} {¬ₕ b} p x with ⟦ b ⟧ₒ s | inspect ⟦ b ⟧ₒ s
      ... | true  | Eq.[ eq ] = x (bIsTrueFollows {s} {b} eq)

      bIsTrueFollows  {s} {b₁ ∧ₕ b₂} x with ⟦ b₁ ⟧ₒ s | ⟦ b₂ ⟧ₒ s |  inspect ⟦ b₁ ⟧ₒ s | inspect ⟦ b₂ ⟧ₒ s
      ... | true  | true  | Eq.[ eq₁ ] | Eq.[ eq₂ ] = bIsTrueFollows {s} {b₁} eq₁ , bIsTrueFollows {s} {b₂} eq₂
      bIsFalseFollows {s} {b₁ ∧ₕ b₂} x x' with ⟦ b₁ ⟧ₒ s | ⟦ b₂ ⟧ₒ s |  inspect ⟦ b₁ ⟧ₒ s | inspect ⟦ b₂ ⟧ₒ s
      ... | false | false | Eq.[ eq₁ ] | _          = bIsFalseFollows {s} {b₁} eq₁ (proj₁ x')
      ... | false | true  | Eq.[ eq₁ ] | _          = bIsFalseFollows {s} {b₁} eq₁ (proj₁ x')
      ... | true  | false | _          | Eq.[ eq₂ ] = bIsFalseFollows {s} {b₂} eq₂ (proj₂ x')

      bIsTrueFollows  {s} {b₁ ∨ₕ b₂} x with ⟦ b₁ ⟧ₒ s | ⟦ b₂ ⟧ₒ s |  inspect ⟦ b₁ ⟧ₒ s | inspect ⟦ b₂ ⟧ₒ s
      ... | false | true  | _          | Eq.[ eq₂ ] = ∣ inj₂ (bIsTrueFollows {s} {b₂} eq₂) ∣
      ... | true  | false | Eq.[ eq₁ ] | _          = ∣ inj₁ (bIsTrueFollows {s} {b₁} eq₁) ∣
      ... | true  | true  | Eq.[ eq₁ ] | _          = ∣ inj₁ (bIsTrueFollows {s} {b₁} eq₁) ∣
      bIsFalseFollows {s} {b₁ ∨ₕ b₂} x x' with ⟦ b₁ ⟧ₒ s | ⟦ b₂ ⟧ₒ s |  inspect ⟦ b₁ ⟧ₒ s | inspect ⟦ b₂ ⟧ₒ s
      ... | false | false | Eq.[ eq₁ ] | Eq.[ eq₂ ] =
        ∥∥-elim (λ x ())
          (λ { (inj₁ y) → bIsFalseFollows {s} {b₁} eq₁ y
             ; (inj₂ y) →  bIsFalseFollows {s} {b₂} eq₂ y } ) x'

      bIsTrueFollows  {S} {x₁ ≤ₕ x₂} x = x
      bIsFalseFollows {S} {x₂ ≤ₕ x₃} x x' rewrite x = trueIsNotEqToFalse (sym x')

    --
    -- Soundness
    --

    soundness : {P Q : Formula} → {C : Cmdₕ}
              → ⟪ P ⟫ C ⟪ Q ⟫
              → ∀ {s : State}
                → proof (⟦ P ⟧ s)
                → proof (⟦ Q ⟧ (⟦ C ⟧ᶜ s))

    soundness {P} {Q} {.(_ |ₕ _)} (composition {P} {R} {Q} {c₁} {c₂} h₁ h₂) pP = soundness h₂ (soundness h₁ pP)
    
    soundness {.(_ [ _ / _ ]ᶠ)} {Q} {_ :=ₕ _} (assignment {P} {Q} {a}) pP = {!  !}

    soundness {P} {Q} {ifₕ _ then _ else _} (if-statement {P} {Q} {b} h₁ h₂) {s} pP with (⟦ b ⟧ₒ s) | inspect ⟦ b ⟧ₒ s 
    ... | false | Eq.[ eq ] = soundness h₂ (pP , λ x → bIsFalseFollows {s} {b} eq x )
    ... | true | Eq.[ eq ] = soundness h₁ (pP , bIsTrueFollows {s} {b} eq)
    

    soundness {Q} {Q} {forₕ n doo c} (for-statement h) {s} pP with abs (⟦ n ⟧ₐ s) | inspect (λ s → abs (⟦ n ⟧ₐ s)) s
    ... | ℕ.zero   | _ = pP
    ... | ℕ.suc n' | Eq.[ eq ] = soundOfForDooAux {n'} {s} pP

      where 

        soundOfForDooAux : {m : ℕ} → ∀ {s : State}
                → proof (⟦ Q ⟧ s)
                → proof (⟦ Q ⟧ (forDooAux m c ⟦ c ⟧ᶜ (⟦ c ⟧ᶜ s)))
        soundOfForDooAux {ℕ.zero} {s} pP' = soundness h pP'
        soundOfForDooAux {ℕ.suc m'} {s} pP' = soundOfForDooAux {m'} {⟦ c ⟧ᶜ s} (soundness h pP')
    
    soundness {P} {Q} {C} (implied {Δ} iP iQ h) {s} pP with ⟦ iP ⟧ₓ {s} tt pP 
    ... | pϕ = ⟦ iQ ⟧ₓ { ⟦ C ⟧ᶜ s} tt (soundness h {s} pϕ)