open import Level

import PQDeduction hiding (_∈_)
open import PQSemantics
import WhileSemantics
open import AngelicHoareLogic
open import HProp
open import PQSubstitution
open import Monads

open import Data.Nat using (ℕ) renaming (_≟_ to _≟ℕ_)
open import Data.Integer using (ℤ; _+_; +_; _-_; -_; _≤ᵇ_) renaming (∣_∣ to abs)
open import Data.Bool using (Bool; true; false)
open import Data.Empty renaming (⊥ to ⊥ᶠ; ⊥-elim to ⊥-elimᶠ)
open import Data.Unit renaming (⊤ to ⊤ᶠ)
open import Data.List using (List; []; _∷_; [_]; _++_; foldr; map)
open import Data.List.Properties using (++-identityʳ)
open import Data.Product using (Σ; _,_; proj₁; proj₂; Σ-syntax; _×_)
open import Data.Sum  using (_⊎_; inj₁; inj₂; [_,_])

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong; cong₂; subst; [_]; inspect)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)

open import Relation.Nullary renaming (¬_ to ¬ᶠ_ )

--
-- Soundness of Hoar logic for WHILE with states and angelic nondeterminism
--

module AngelicSoundness where

    open WhileSyntaxNat
    open WhileSemantics renaming (⟦_⟧ to ⟦_⟧ᶜ)
    open PQDeductionNat
    
    open Monad NDS-Monad

    --
    -- Some useful lemmas
    --

    trueIsNotEqToFalse : (true ≡ false) → ⊥ᶠ
    trueIsNotEqToFalse ()

    -- Relate how the boolean expressions are interpreted in WHILE language and how they are interpreted in the
    -- PQ logic.

    interleaved mutual

      -- If `b` evaluates to true, then there exist a witness of `⟦ toFormulaₚ b ⟧ s`.
      bIsTrueFollows  : {s : State} → {b : BExprₕ} → (⟦ b ⟧ᵇ s ≡ true) → (proof (⟦ toFormulaₚ b ⟧ s))
      -- If `b` evaluates to false, then there does NOT exist a witness of `⟦ toFormulaₚ b ⟧ s`.
      bIsFalseFollows : {s : State} → {b : BExprₕ} → (⟦ b ⟧ᵇ s ≡ false) → ¬ᶠ (proof (⟦ toFormulaₚ b ⟧ s))
      bIsTrueFollows  {s} {trueʷ} p = tt
      bIsFalseFollows {s} {trueʷ} ()
      bIsTrueFollows  {s} {¬ʷ b} p x with ⟦ b ⟧ᵇ s | inspect ⟦ b ⟧ᵇ s
      ... | false | Eq.[ eq ] = bIsFalseFollows {s} {b} eq  x
      bIsFalseFollows {s} {¬ʷ b} p x with ⟦ b ⟧ᵇ s | inspect ⟦ b ⟧ᵇ s
      ... | true  | Eq.[ eq ] = x (bIsTrueFollows {s} {b} eq)
      bIsTrueFollows  {s} {b₁ ∧ʷ b₂} x with ⟦ b₁ ⟧ᵇ s | ⟦ b₂ ⟧ᵇ s |  inspect ⟦ b₁ ⟧ᵇ s | inspect ⟦ b₂ ⟧ᵇ s
      ... | true  | true  | Eq.[ eq₁ ] | Eq.[ eq₂ ] = bIsTrueFollows {s} {b₁} eq₁ , bIsTrueFollows {s} {b₂} eq₂
      bIsFalseFollows {s} {b₁ ∧ʷ b₂} x x' with ⟦ b₁ ⟧ᵇ s | ⟦ b₂ ⟧ᵇ s |  inspect ⟦ b₁ ⟧ᵇ s | inspect ⟦ b₂ ⟧ᵇ s
      ... | false | false | Eq.[ eq₁ ] | _          = bIsFalseFollows {s} {b₁} eq₁ (proj₁ x')
      ... | false | true  | Eq.[ eq₁ ] | _          = bIsFalseFollows {s} {b₁} eq₁ (proj₁ x')
      ... | true  | false | _          | Eq.[ eq₂ ] = bIsFalseFollows {s} {b₂} eq₂ (proj₂ x')
      bIsTrueFollows  {s} {b₁ ∨ʷ b₂} x with ⟦ b₁ ⟧ᵇ s | ⟦ b₂ ⟧ᵇ s |  inspect ⟦ b₁ ⟧ᵇ s | inspect ⟦ b₂ ⟧ᵇ s
      ... | false | true  | _          | Eq.[ eq₂ ] = ∣ inj₂ (bIsTrueFollows {s} {b₂} eq₂) ∣
      ... | true  | false | Eq.[ eq₁ ] | _          = ∣ inj₁ (bIsTrueFollows {s} {b₁} eq₁) ∣
      ... | true  | true  | Eq.[ eq₁ ] | _          = ∣ inj₁ (bIsTrueFollows {s} {b₁} eq₁) ∣
      bIsFalseFollows {s} {b₁ ∨ʷ b₂} x x' with ⟦ b₁ ⟧ᵇ s | ⟦ b₂ ⟧ᵇ s |  inspect ⟦ b₁ ⟧ᵇ s | inspect ⟦ b₂ ⟧ᵇ s
      ... | false | false | Eq.[ eq₁ ] | Eq.[ eq₂ ] =
        ∥∥-elim (λ x ())
          (λ { (inj₁ y) → bIsFalseFollows {s} {b₁} eq₁ y
             ; (inj₂ y) →  bIsFalseFollows {s} {b₂} eq₂ y } ) x'
      bIsTrueFollows  {S} {x₁ ≤ʷ x₂} x = x
      bIsFalseFollows {S} {x₂ ≤ʷ x₃} x x' rewrite x = trueIsNotEqToFalse (sym x')

    -- Show how is substitution related to a state.

    subR2StateA : {a : AExprₕ} → {b : AExprₕ} → {l : ℕ} → {s : state}
         →  (⟦ a [ b / l ]ᵃ ⟧ᵃ s) ≡ (⟦ a ⟧ᵃ (toSt l (⟦ b ⟧ᵃ s) s))
    subR2StateA {intʷ x} {b} {l} {s} = refl
    subR2StateA {locʷ l'} {b} {l} {s} with does (l ≟ℕ l')
    ... | false = refl
    ... | true = refl
    subR2StateA { -ʷ a} {b} {l} {s} = cong -_ (subR2StateA {a} {b} {l} {s})
    subR2StateA {a₁ +ʷ a₂} {b} {l} {s} = cong₂ _+_
      {⟦ a₁ [ b / l ]ᵃ ⟧ᵃ s}
      {⟦ a₁ ⟧ᵃ (toSt l (⟦ b ⟧ᵃ s) s)}
        (subR2StateA {a₁} {b} {l} {s}) (subR2StateA {a₂} {b} {l} {s})

    interleaved mutual

      -- A proof of substitution of 'a' for 'l' in 'Q' and then evaluating its interpretation at state 's' implies
      --    a proof of interpreting 'Q' evaluated at state where 'l' has a value '⟦ a ⟧ᵃ s'.
      subR2State  : {Q : Formula} → {a : AExprₕ} → {l : ℕ} → {s : state}
                      → proof (⟦ Q [ a / l ]ᶠ ⟧ s) → proof (⟦ Q ⟧ (toSt l (⟦ a ⟧ᵃ s) s))
      -- A proof of interpreting 'Q' evaluated at state where 'l' has a value '⟦ a ⟧ᵃ s' implies
      --    a proof of substitution of 'a' for 'l' in 'Q' and then evaluating its interpretation at state 's'.
      subR2State' : {Q : Formula} → {a : AExprₕ} → {l : ℕ} → {s : state}
                      → proof (⟦ Q ⟧ (toSt l (⟦ a ⟧ᵃ s) s)) → proof (⟦ Q [ a / l ]ᶠ ⟧ s) 
      subR2State {⊤} {a} {l} {s} _ = tt
      subR2State' {⊤} {a} {l} {s} _ = tt
      subR2State {⊥} {a} {l} {s} p = p
      subR2State' {⊥} {a} {l} {s} p = p
      subR2State {Q₁ ⇒ Q₂} {a} {l} {s} p pQ₁ =
        subR2State {Q₂} {a} {l} {s} (p (subR2State' {Q₁} {a} {l} {s} pQ₁))
      subR2State' {Q₁ ⇒ Q₂} {a} {l} {s} p pQ₁ =
        subR2State' {Q₂} {a} {l} {s} (p (subR2State {Q₁} {a} {l} {s} pQ₁))
      subR2State {x₁ =ₑ x₂} {a} {l} {s} p =
        begin
          ⟦ x₁ ⟧ᵃ (toSt l (⟦ a ⟧ᵃ s) s)
        ≡⟨ sym (subR2StateA {x₁} {a} {l} {s}) ⟩
          ⟦ x₁ [ a / l ]ᵃ ⟧ᵃ s
        ≡⟨ p ⟩
          ⟦ x₂ [ a / l ]ᵃ ⟧ᵃ s
        ≡⟨ subR2StateA {x₂} {a} {l} {s} ⟩
          ⟦ x₂ ⟧ᵃ (toSt l (⟦ a ⟧ᵃ s) s)
        ∎
      subR2State' {x₁ =ₑ x₂} {a} {l} {s} p =
        begin
          ⟦ x₁ [ a / l ]ᵃ ⟧ᵃ s
        ≡⟨ subR2StateA {x₁} {a} {l} {s} ⟩
          ⟦ x₁ ⟧ᵃ (toSt l (⟦ a ⟧ᵃ s) s)
        ≡⟨ p ⟩
          ⟦ x₂ ⟧ᵃ (toSt l (⟦ a ⟧ᵃ s) s)
        ≡⟨ sym ( subR2StateA {x₂} {a} {l} {s}) ⟩
          ⟦ x₂ [ a / l ]ᵃ ⟧ᵃ s
        ∎
      subR2State {Q₁ ∧ Q₂} {a} {l} {s} p =
        (subR2State {Q₁} {a} {l} {s} (∧ʰ-proj₁ (⟦ Q₁ [ a / l ]ᶠ ⟧ s) (⟦ Q₂ [ a / l ]ᶠ ⟧ s) p)) ,
        (subR2State {Q₂} {a} {l} {s} (∧ʰ-proj₂ (⟦ Q₁ [ a / l ]ᶠ ⟧ s) (⟦ Q₂ [ a / l ]ᶠ ⟧ s) p))
      subR2State' {Q₁ ∧ Q₂} {a} {l} {s} p =
        (subR2State' {Q₁} {a} {l} {s} (∧ʰ-proj₁ (⟦ Q₁ ⟧ (toSt l (⟦ a ⟧ᵃ s) s)) (⟦ Q₂ ⟧ (toSt l (⟦ a ⟧ᵃ s) s)) p)) ,
        (subR2State' {Q₂} {a} {l} {s} (∧ʰ-proj₂ (⟦ Q₁ ⟧ (toSt l (⟦ a ⟧ᵃ s) s)) (⟦ Q₂ ⟧ (toSt l (⟦ a ⟧ᵃ s) s)) p))
      subR2State {Q₁ ∨ Q₂} {a} {l} {s} p = 
        ∨ʰ-cong
          (⟦ Q₁ [ a / l ]ᶠ ⟧ s) (⟦ Q₂ [ a / l ]ᶠ ⟧ s)
          {⟦ Q₁ ⟧ (toSt l (⟦ a ⟧ᵃ s) s)} {⟦ Q₂ ⟧ (toSt l (⟦ a ⟧ᵃ s) s)}
          (subR2State {Q₁}) (subR2State {Q₂}) p
      subR2State' {Q₁ ∨ Q₂} {a} {l} {s} p = ∨ʰ-cong
        (⟦ Q₁ ⟧ (toSt l (⟦ a ⟧ᵃ s) s)) (⟦ Q₂ ⟧ (toSt l (⟦ a ⟧ᵃ s) s))
        {⟦ Q₁ [ a / l ]ᶠ ⟧ s} {⟦ Q₂ [ a / l ]ᶠ ⟧ s}
        (subR2State' {Q₁}) (subR2State' {Q₂}) p
      subR2State {x₁ ≤ₑ x₂} {a} {l} {s} p =
        begin
          ⟦ x₁ ⟧ᵃ (toSt l (⟦ a ⟧ᵃ s) s) ≤ᵇ ⟦ x₂ ⟧ᵃ (toSt l (⟦ a ⟧ᵃ s) s)
        ≡⟨ cong₂ _≤ᵇ_ (sym (subR2StateA {x₁} {a} {l} {s})) (sym (subR2StateA {x₂} {a} {l} {s})) ⟩
          ⟦ x₁ [ a / l ]ᵃ ⟧ᵃ s ≤ᵇ ⟦ x₂ [ a / l ]ᵃ ⟧ᵃ s
        ≡⟨ p ⟩
          true
        ∎
      subR2State' {x₁ ≤ₑ x₂} {a} {l} {s} p = 
        begin
          ⟦ x₁ [ a / l ]ᵃ ⟧ᵃ s ≤ᵇ ⟦ x₂ [ a / l ]ᵃ ⟧ᵃ s
        ≡⟨ cong₂ _≤ᵇ_ (subR2StateA {x₁} {a} {l} {s}) (subR2StateA {x₂} {a} {l} {s}) ⟩
          ⟦ x₁ ⟧ᵃ (toSt l (⟦ a ⟧ᵃ s) s) ≤ᵇ ⟦ x₂ ⟧ᵃ (toSt l (⟦ a ⟧ᵃ s) s)
        ≡⟨ p ⟩
          true
        ∎

      ∈-++l : {A : Set} → {x : A} → (L : List A) → {L' : List A}
              → (x ∈ L) → (x ∈ (L ++ L'))
      ∈-++l L {[]} p rewrite (++-identityʳ L) = p
      ∈-++l .(_ ∷ _) {l ∷ L'} ∈-here = ∈-here
      ∈-++l (_ ∷ xs) {l ∷ L'} (∈-there {{in-xs}}) = ∈-there {{∈-++l xs in-xs}}

      ∈-++r : {A : Set} → {x : A} → (L : List A) → {L' : List A}
            → (x ∈ L') → (x ∈ (L ++ L'))
      ∈-++r [] {L'} p = p
      ∈-++r (_ ∷ L₁) {.(_ ∷ _)} ∈-here = ∈-there {{∈-++r L₁ ∈-here}}
      ∈-++r (_ ∷ L₁) {.(_ ∷ _)} (∈-there {{in-xs}}) = ∈-there {{∈-++r L₁ (∈-there {{in-xs}})}}

      ∈-to-∈-list-× : {A B : Set} → {x y : B × A} → (L : List (B × A))
            → (x ∈ L)
            → (f : A → List (B × A))
            → (y ∈ (f (proj₂ x)))
            → (y ∈ (foldr _++_ [] (map (λ { (_ , s') → f s' }) L) ))

      ∈-to-∈-list-× ((_ , a) ∷ L₁) ∈-here f q = ∈-++l (f a) q
      ∈-to-∈-list-× ((_ , a) ∷ L₁) (∈-there {{in-xs}}) f q 
        = ∈-++r (f a) (∈-to-∈-list-× L₁ in-xs f q)

    ∥∥-to-∥∥ : {A : Set} → {B : Set} → ∥ A ∥ → (A → ∥ B ∥) → ∥ B ∥
    ∥∥-to-∥∥ x f = ∥∥-elim (∥∥-is-proposition _) f x

    angelic : (Q : Formula) → (C : Cmdₕ) → {s : State} → HProp
    angelic Q C {s} =  (∃ʰ State (λ s' → ⟨ ∥ (_ , s') ∈ ⟦ C ⟧ᶜ s ∥ , ∥∥-is-proposition _ ⟩ ∧ʰ (⟦ Q ⟧ s')))

    soundness : {P Q : Formula} 
              → {C : Cmdₕ}
              → ⟪ P ⟫ C ⟪ Q ⟫
              → {s : State}
              → proof (⟦ P ⟧ s)
              → proof (angelic Q C {s})

    soundness {P} {Q} {.(_ |ʷ _)} (composition {P} {R} {Q} {C₁} {C₂} h₁ h₂) {s} pP 
      = ∥∥-to-∥∥ (soundness h₁ pP) (λ {(s₁ , i₁ , p₁) 
        → ∥∥-to-∥∥ (soundness h₂ p₁) (λ {(s₂ , i₂ , p₂) 
          → ∣ s₂ , (∥∥-to-∥∥ i₁ (λ i¹ 
            → ∥∥-to-∥∥ i₂ λ i² → ∣ ∈-to-∈-list-× (⟦ C₁ ⟧ᶜ s) i¹ ⟦ C₂ ⟧ᶜ i² ∣) , p₂) ∣})})
    
    soundness {.(Q [ _ / _ ]ᶠ)} {Q} {l :=ʷ a} (assignment {Q} {a}) {s} pP
      = ∣ toSt l (⟦ a ⟧ᵃ s) s , (∣ ∈-here ∣ , subR2State {Q} {a} {l} {s} pP) ∣
    
    soundness {P} {Q} {.(ifʷ _ then _ else _)} (if-statement {P} {Q} {b} h₁ h₂) {s} pP with (⟦ b ⟧ᵇ s) | inspect ⟦ b ⟧ᵇ s
    ... | false | Eq.[ eq ] = soundness h₂ (pP , bIsFalseFollows {s} {b} eq)
    ... | true | Eq.[ eq ] = soundness h₁ (pP , bIsTrueFollows {s} {b} eq)
    
    soundness {P} {.P} {(forʷ a doo C)} (for-statement h) {s} pP
      = sound-for {P} {C} h pP (abs (⟦ a ⟧ᵃ s))
        where 
          sound-for : {P : Formula} 
                    → {C : Cmdₕ}
                    → ⟪ P ⟫ C ⟪ P ⟫
                    → {s : State}
                    → proof (⟦ P ⟧ s)
                    → (n : ℕ)
                    → proof (∃ʰ State (λ s' → ⟨ ∥ (_ , s') ∈ (forDooAux n ⟦ C ⟧ᶜ s) ∥ , ∥∥-is-proposition _ ⟩ ∧ʰ (⟦ P ⟧ s')))
          
          sound-for {P} {C} h {s} pP ℕ.zero = ∣ s , (∣ ∈-here ∣ , pP) ∣
          sound-for {P} {C} h {s} pP (ℕ.suc n) 
            = ∥∥-to-∥∥ (soundness h pP) (λ {(s₁ , i₁ , p₁) 
              → ∥∥-to-∥∥ (sound-for h p₁ n) λ {(s₂ , i₂ , p₂) 
                → ∣ s₂ , ∥∥-to-∥∥ i₁ (λ i¹ 
                  → ∥∥-to-∥∥ i₂ λ i² 
                    → ∣ ∈-to-∈-list-× (⟦ C ⟧ᶜ s) i¹ (forDooAux n ⟦ C ⟧ᶜ) i² ∣) , p₂ ∣}})
    
    soundness {P} {Q} {C} (implied iP iQ h) {s} pP
      = ∥∥-to-∥∥ (soundness h ((⟦ iP ⟧ₓ tt pP))) (λ {(s₁ , i₁ , p₁) → ∣ s₁ , i₁ , (⟦ iQ ⟧ₓ tt p₁) ∣})
    
    soundness {P} {Q} {C₁ orʷ C₂} (or-statement h₁ h₂) {s} pP
      = ∥∥-to-∥∥ pP (λ {(inj₁ p) → sound-to-or {C₁} {C₂} (∨ʰ-inj₁ (angelic Q C₁) (angelic Q C₂) (soundness h₁ p))
                    ; (inj₂ p) → sound-to-or {C₁} {C₂} (∨ʰ-inj₂ (angelic Q C₁) (angelic Q C₂) (soundness h₂ p))})
      where
        sound-to-or : {C C' : Cmdₕ} → proof ((angelic Q C {s}) ∨ʰ angelic Q C' {s})→ proof (angelic Q (C orʷ C'))
        sound-to-or {C} {C'} S = ∥∥-to-∥∥ S (λ {(inj₁ x) → ∥∥-to-∥∥ x (λ {(i , j , k) → ∣ i , (∥∥-to-∥∥ j (λ i → ∣ ∈-++l (⟦ C ⟧ᶜ s) i ∣) , k) ∣})
                                            ; (inj₂ x') → ∥∥-to-∥∥ x' (λ {(i , j , k) → ∣ i , (∥∥-to-∥∥ j (λ i → ∣ ∈-++r (⟦ C ⟧ᶜ s) i ∣) , k) ∣})})