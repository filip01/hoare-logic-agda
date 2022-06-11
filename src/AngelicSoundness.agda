open import AngelicHoareLogic

open import Level

open import HProp
open import Monads

open import Data.Nat using (ℕ; _≟_)
open import Data.Integer using (ℤ; _+_; +_; _-_; -_; _≤ᵇ_) renaming (∣_∣ to abs; suc to ℤ-suc)
open import Data.Bool using (Bool; true; false)
open import Data.Empty renaming (⊥ to ⊥ᶠ; ⊥-elim to ⊥-elimᶠ)
open import Data.Unit using (tt) renaming (⊤ to ⊤ᶠ)
open import Data.List using (List; []; _∷_; [_]; _++_; foldr; map)
open import Data.List.Properties using (++-identityʳ)
open import Data.Product using (Σ; _,_; proj₁; proj₂; Σ-syntax; _×_)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_])

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong; cong₂; subst; [_]; inspect)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)

open import Relation.Nullary renaming (¬_ to ¬ᶠ_ )


--
-- Soundness of Hoar logic for WHILE with states and angelic nondeterminism
--

module AngelicSoundness where

    open import PQSyntax L

    open import PQDeduction L _≟_ 

    open import PQSemantics L _≟_

    open import PQSubstitution L _≟_

    open import WhileSemantics L _≟_ renaming (⟦_⟧ to ⟦_⟧ᶜ)

    open import WhileSyntax L

    open Monad NDS-Monad


    --
    -- Some useful lemmas
    --

    trueIsNotEqToFalse : (true ≡ false) → ⊥ᶠ
    trueIsNotEqToFalse ()

     -- Show that the interpretation of Expr and AExprₕ are equivalent.
    itr-are-equal : (a : AExprₕ) → ⟦ toExprₚ a ⟧ₑ ≡ ⟦ a ⟧ᵃ
    itr-are-equal (intʷ x) = refl
    itr-are-equal (locʷ x) = refl
    itr-are-equal (-ʷ a) = cong ((λ e Γ → - e Γ )) (itr-are-equal a)
    itr-are-equal (a₁ +ʷ a₂) = cong₂ (λ e₁ e₂ Γ → e₁ Γ + e₂ Γ) (itr-are-equal a₁) (itr-are-equal a₂)

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
      bIsTrueFollows  {S} {x₁ ≤ʷ x₂} x rewrite itr-are-equal x₁ rewrite itr-are-equal x₂ = x
      bIsFalseFollows {S} {x₁ ≤ʷ x₂} x x' rewrite itr-are-equal x₁ rewrite itr-are-equal x₂
        rewrite x = trueIsNotEqToFalse (sym x')

    -- Show how is substitution related to a state.

    -- subR2StateA : {a : Expr} → {b : Expr} → {l : ℕ} → {s : state}
    --      →  (⟦ a [ b / l ]ᵃ ⟧ₑ s) ≡ (⟦ a ⟧ₑ (toSt l (⟦ b ⟧ₑ s) s))
    subR2StateA : {a : Expr} → {b : AExprₕ} → {l : ℕ} → {s : state}
         →  (⟦ a [ (toExprₚ b) / l ]ᵃ ⟧ₑ s) ≡ (⟦ a ⟧ₑ (toSt l (⟦ b ⟧ᵃ s) s))
    subR2StateA {int x} {b} {l} {s} = refl
    subR2StateA {loc l'} {b} {l} {s} with does (l ≟ l')
    ... | false = refl
    ... | true rewrite itr-are-equal b = refl
    subR2StateA {suc a} {b} {l} {s} = cong ℤ-suc (subR2StateA {a} {b} {l} {s})
    subR2StateA { -ₑ a} {b} {l} {s} = cong -_ (subR2StateA {a} {b} {l} {s})
    subR2StateA {a₁ +ₑ a₂} {b} {l} {s} = cong₂ _+_
      {⟦ a₁ [ (toExprₚ b) / l ]ᵃ ⟧ₑ s}
      {⟦ a₁ ⟧ₑ (toSt l (⟦ b ⟧ᵃ s) s)}
      ((subR2StateA {a₁} {b} {l} {s})) ((subR2StateA {a₂} {b} {l} {s}))

    interleaved mutual

      -- A proof of substitution of 'a' for 'l' in 'Q' and then evaluating its interpretation at state 's' implies
      --    a proof of interpreting 'Q' evaluated at state where 'l' has a value '⟦ a ⟧ₑ s'.
      subR2State  : {Q : Formula} → {a : AExprₕ} → {l : ℕ} → {s : state}
                      → proof (⟦ Q [ (toExprₚ a) / l ]ᶠ ⟧ s) → proof (⟦ Q ⟧ (toSt l (⟦ a ⟧ᵃ s) s))
      -- A proof of interpreting 'Q' evaluated at state where 'l' has a value '⟦ a ⟧ₑ s' implies
      --    a proof of substitution of 'a' for 'l' in 'Q' and then evaluating its interpretation at state 's'.
      subR2State' : {Q : Formula} → {a : AExprₕ} → {l : ℕ} → {s : state}
                      → proof (⟦ Q ⟧ (toSt l (⟦ a ⟧ᵃ s) s)) → proof (⟦ Q [ (toExprₚ a) / l ]ᶠ ⟧ s)
      subR2State  {⊤} {a} {l} {s} _ = tt
      subR2State' {⊤} {a} {l} {s} _ = tt
      subR2State {⊥} {a} {l} {s} p = p
      subR2State' {⊥} {a} {l} {s} p = p
      subR2State {Q₁ ⇒ Q₂} {a} {l} {s} p pQ₁ =
        subR2State {Q₂} {a} {l} {s} (p (subR2State' {Q₁} {a} {l} {s} pQ₁))
      subR2State' {Q₁ ⇒ Q₂} {a} {l} {s} p pQ₁ =
        subR2State' {Q₂} {a} {l} {s} (p (subR2State {Q₁} {a} {l} {s} pQ₁))
      subR2State {x₁ =ₑ x₂} {a} {l} {s} p =
        begin
          ⟦ x₁ ⟧ₑ (toSt l (⟦ a ⟧ᵃ s) s)
        ≡⟨ sym (subR2StateA {x₁} {a} {l} {s}) ⟩
          ⟦ x₁ [ (toExprₚ a) / l ]ᵃ ⟧ₑ s
        ≡⟨ p ⟩
          ⟦ x₂ [ (toExprₚ a) / l ]ᵃ ⟧ₑ s
        ≡⟨ subR2StateA {x₂} {a} {l} {s} ⟩
          ⟦ x₂ ⟧ₑ (toSt l (⟦ a ⟧ᵃ s) s)
        ∎
      
      subR2State' {x₁ =ₑ x₂} {a} {l} {s} p =
        begin
          ⟦ x₁ [ (toExprₚ a) / l ]ᵃ ⟧ₑ s
        ≡⟨ subR2StateA {x₁} {a} {l} {s} ⟩
          ⟦ x₁ ⟧ₑ (toSt l (⟦ a ⟧ᵃ s) s)
        ≡⟨ p ⟩
          ⟦ x₂ ⟧ₑ (toSt l (⟦ a ⟧ᵃ s) s)
        ≡⟨ sym ( subR2StateA {x₂} {a} {l} {s}) ⟩
          ⟦ x₂ [ (toExprₚ a) / l ]ᵃ ⟧ₑ s
        ∎
      subR2State {Q₁ ∧ Q₂} {a} {l} {s} p =
        (subR2State {Q₁} {a} {l} {s} (∧ʰ-proj₁ (⟦ Q₁ [ (toExprₚ a) / l ]ᶠ ⟧ s) (⟦ Q₂ [ (toExprₚ a) / l ]ᶠ ⟧ s) p)) ,
        (subR2State {Q₂} {a} {l} {s} (∧ʰ-proj₂ (⟦ Q₁ [ (toExprₚ a)/ l ]ᶠ ⟧ s) (⟦ Q₂ [ (toExprₚ a) / l ]ᶠ ⟧ s) p))
      subR2State' {Q₁ ∧ Q₂} {a} {l} {s} p =
        (subR2State' {Q₁} {a} {l} {s} (∧ʰ-proj₁ (⟦ Q₁ ⟧ (toSt l (⟦ a ⟧ᵃ s) s)) (⟦ Q₂ ⟧ (toSt l (⟦ a ⟧ᵃ s) s)) p)) ,
        (subR2State' {Q₂} {a} {l} {s} (∧ʰ-proj₂ (⟦ Q₁ ⟧ (toSt l (⟦ a ⟧ᵃ s) s)) (⟦ Q₂ ⟧ (toSt l (⟦ a ⟧ᵃ s) s)) p))
      subR2State {Q₁ ∨ Q₂} {a} {l} {s} p = 
        ∨ʰ-cong
          (⟦ Q₁ [ (toExprₚ a) / l ]ᶠ ⟧ s) (⟦ Q₂ [ (toExprₚ a) / l ]ᶠ ⟧ s)
          {⟦ Q₁ ⟧ (toSt l (⟦ a ⟧ᵃ s) s)} {⟦ Q₂ ⟧ (toSt l (⟦ a ⟧ᵃ s) s)}
          (subR2State {Q₁}) (subR2State {Q₂}) p
      subR2State' {Q₁ ∨ Q₂} {a} {l} {s} p = ∨ʰ-cong
        (⟦ Q₁ ⟧ (toSt l (⟦ a ⟧ᵃ s) s)) (⟦ Q₂ ⟧ (toSt l (⟦ a ⟧ᵃ s) s))
        {⟦ Q₁ [ (toExprₚ a) / l ]ᶠ ⟧ s} {⟦ Q₂ [ (toExprₚ a) / l ]ᶠ ⟧ s}
        (subR2State' {Q₁}) (subR2State' {Q₂}) p
      subR2State {x₁ ≤ₑ x₂} {a} {l} {s} p =
        begin
          ⟦ x₁ ⟧ₑ (toSt l (⟦ a ⟧ᵃ s) s) ≤ᵇ ⟦ x₂ ⟧ₑ (toSt l (⟦ a ⟧ᵃ s) s)
        ≡⟨ cong₂ _≤ᵇ_ (sym (subR2StateA {x₁} {a} {l} {s})) (sym (subR2StateA {x₂} {a} {l} {s})) ⟩
          ⟦ x₁ [ (toExprₚ a) / l ]ᵃ ⟧ₑ s ≤ᵇ ⟦ x₂ [ (toExprₚ a) / l ]ᵃ ⟧ₑ s
        ≡⟨ p ⟩
          true
        ∎
      subR2State' {x₁ ≤ₑ x₂} {a} {l} {s} p =
        begin
          ⟦ x₁ [ (toExprₚ a) / l ]ᵃ ⟧ₑ s ≤ᵇ ⟦ x₂ [ (toExprₚ a) / l ]ᵃ ⟧ₑ s
        ≡⟨ cong₂ _≤ᵇ_ (subR2StateA {x₁} {a} {l} {s}) (subR2StateA {x₂} {a} {l} {s}) ⟩
          ⟦ x₁ ⟧ₑ (toSt l (⟦ a ⟧ᵃ s) s) ≤ᵇ ⟦ x₂ ⟧ₑ (toSt l (⟦ a ⟧ᵃ s) s)
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