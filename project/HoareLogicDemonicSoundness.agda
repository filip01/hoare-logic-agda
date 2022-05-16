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
      bIsTrueFollows  {s} {trueʷ} p = tt
      bIsFalseFollows {s} {trueʷ} ()
    
      bIsTrueFollows  {s} {¬ʷ b} p x with ⟦ b ⟧ₒ s | inspect ⟦ b ⟧ₒ s
      ... | false | Eq.[ eq ] = bIsFalseFollows {s} {b} eq  x
      bIsFalseFollows {s} {¬ʷ b} p x with ⟦ b ⟧ₒ s | inspect ⟦ b ⟧ₒ s
      ... | true  | Eq.[ eq ] = x (bIsTrueFollows {s} {b} eq)
      bIsTrueFollows  {s} {b₁ ∧ʷ b₂} x with ⟦ b₁ ⟧ₒ s | ⟦ b₂ ⟧ₒ s |  inspect ⟦ b₁ ⟧ₒ s | inspect ⟦ b₂ ⟧ₒ s
      ... | true  | true  | Eq.[ eq₁ ] | Eq.[ eq₂ ] = bIsTrueFollows {s} {b₁} eq₁ , bIsTrueFollows {s} {b₂} eq₂
      bIsFalseFollows {s} {b₁ ∧ʷ b₂} x x' with ⟦ b₁ ⟧ₒ s | ⟦ b₂ ⟧ₒ s |  inspect ⟦ b₁ ⟧ₒ s | inspect ⟦ b₂ ⟧ₒ s
      ... | false | false | Eq.[ eq₁ ] | _          = bIsFalseFollows {s} {b₁} eq₁ (proj₁ x')
      ... | false | true  | Eq.[ eq₁ ] | _          = bIsFalseFollows {s} {b₁} eq₁ (proj₁ x')
      ... | true  | false | _          | Eq.[ eq₂ ] = bIsFalseFollows {s} {b₂} eq₂ (proj₂ x')
      bIsTrueFollows  {s} {b₁ ∨ʷ b₂} x with ⟦ b₁ ⟧ₒ s | ⟦ b₂ ⟧ₒ s |  inspect ⟦ b₁ ⟧ₒ s | inspect ⟦ b₂ ⟧ₒ s
      ... | false | true  | _          | Eq.[ eq₂ ] = ∣ inj₂ (bIsTrueFollows {s} {b₂} eq₂) ∣
      ... | true  | false | Eq.[ eq₁ ] | _          = ∣ inj₁ (bIsTrueFollows {s} {b₁} eq₁) ∣
      ... | true  | true  | Eq.[ eq₁ ] | _          = ∣ inj₁ (bIsTrueFollows {s} {b₁} eq₁) ∣
      bIsFalseFollows {s} {b₁ ∨ʷ b₂} x x' with ⟦ b₁ ⟧ₒ s | ⟦ b₂ ⟧ₒ s |  inspect ⟦ b₁ ⟧ₒ s | inspect ⟦ b₂ ⟧ₒ s
      ... | false | false | Eq.[ eq₁ ] | Eq.[ eq₂ ] =
        ∥∥-elim (λ x ())
          (λ { (inj₁ y) → bIsFalseFollows {s} {b₁} eq₁ y
             ; (inj₂ y) →  bIsFalseFollows {s} {b₂} eq₂ y } ) x'
      bIsTrueFollows  {S} {x₁ ≤ʷ x₂} x = x
      bIsFalseFollows {S} {x₂ ≤ʷ x₃} x x' rewrite x = trueIsNotEqToFalse (sym x')
    

    --
    -- Show how is substitution related to state.
    --
    subR2StateA : {a : AExprₕ} → {b : AExprₕ} → {l : ℕ} → {s : state}
         →  (⟦ a [ b / l ]ᵉ ⟧ₐ s) ≡ (⟦ a ⟧ₐ (toSt l (⟦ b ⟧ₐ s) s))
    subR2StateA {intʷ x} {b} {l} {s} = refl
    subR2StateA {locʷ l'} {b} {l} {s} with does (l ≟ℕ l')
    ... | false = refl
    ... | true = refl
    subR2StateA { -ʷ a} {b} {l} {s} = cong -_ (subR2StateA {a} {b} {l} {s})
    subR2StateA {a₁ +ʷ a₂} {b} {l} {s} = cong₂ _+_
      {⟦ a₁ [ b / l ]ᵉ ⟧ₐ s}
      {⟦ a₁ ⟧ₐ (toSt l (⟦ b ⟧ₐ s) s)}
        (subR2StateA {a₁} {b} {l} {s}) (subR2StateA {a₂} {b} {l} {s})
    interleaved mutual
      subR2State  : {Q : Formula} → {a : AExprₕ} → {l : ℕ} → {s : state}
                      → proof (⟦ Q [ a / l ]ᶠ ⟧ s) → proof (⟦ Q ⟧ (toSt l (⟦ a ⟧ₐ s) s))
      subR2State' : {Q : Formula} → {a : AExprₕ} → {l : ℕ} → {s : state}
                      → proof (⟦ Q ⟧ (toSt l (⟦ a ⟧ₐ s) s)) → proof (⟦ Q [ a / l ]ᶠ ⟧ s) 
  
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
          ⟦ x₁ ⟧ₐ (toSt l (⟦ a ⟧ₐ s) s)
        ≡⟨ sym (subR2StateA {x₁} {a} {l} {s}) ⟩
          ⟦ x₁ [ a / l ]ᵉ ⟧ₐ s
        ≡⟨ p ⟩
          ⟦ x₂ [ a / l ]ᵉ ⟧ₐ s
        ≡⟨ subR2StateA {x₂} {a} {l} {s} ⟩
          ⟦ x₂ ⟧ₐ (toSt l (⟦ a ⟧ₐ s) s)
        ∎
      subR2State' {x₁ =ₑ x₂} {a} {l} {s} p =
        begin
          ⟦ x₁ [ a / l ]ᵉ ⟧ₐ s
        ≡⟨ subR2StateA {x₁} {a} {l} {s} ⟩
          ⟦ x₁ ⟧ₐ (toSt l (⟦ a ⟧ₐ s) s)
        ≡⟨ p ⟩
          ⟦ x₂ ⟧ₐ (toSt l (⟦ a ⟧ₐ s) s)
        ≡⟨ sym ( subR2StateA {x₂} {a} {l} {s}) ⟩
          ⟦ x₂ [ a / l ]ᵉ ⟧ₐ s
        ∎
      subR2State {Q₁ ∧ Q₂} {a} {l} {s} p =
        (subR2State {Q₁} {a} {l} {s} (∧ʰ-proj₁ (⟦ Q₁ [ a / l ]ᶠ ⟧ s) (⟦ Q₂ [ a / l ]ᶠ ⟧ s) p)) ,
        (subR2State {Q₂} {a} {l} {s} (∧ʰ-proj₂ (⟦ Q₁ [ a / l ]ᶠ ⟧ s) (⟦ Q₂ [ a / l ]ᶠ ⟧ s) p))
      subR2State' {Q₁ ∧ Q₂} {a} {l} {s} p =
        (subR2State' {Q₁} {a} {l} {s} (∧ʰ-proj₁ (⟦ Q₁ ⟧ (toSt l (⟦ a ⟧ₐ s) s)) (⟦ Q₂ ⟧ (toSt l (⟦ a ⟧ₐ s) s)) p)) ,
        (subR2State' {Q₂} {a} {l} {s} (∧ʰ-proj₂ (⟦ Q₁ ⟧ (toSt l (⟦ a ⟧ₐ s) s)) (⟦ Q₂ ⟧ (toSt l (⟦ a ⟧ₐ s) s)) p))
      subR2State {Q₁ ∨ Q₂} {a} {l} {s} p = 
        ∨ʰ-cong
          (⟦ Q₁ [ a / l ]ᶠ ⟧ s) (⟦ Q₂ [ a / l ]ᶠ ⟧ s)
          {⟦ Q₁ ⟧ (toSt l (⟦ a ⟧ₐ s) s)} {⟦ Q₂ ⟧ (toSt l (⟦ a ⟧ₐ s) s)}
          (subR2State {Q₁}) (subR2State {Q₂}) p
      subR2State' {Q₁ ∨ Q₂} {a} {l} {s} p = ∨ʰ-cong
        (⟦ Q₁ ⟧ (toSt l (⟦ a ⟧ₐ s) s)) (⟦ Q₂ ⟧ (toSt l (⟦ a ⟧ₐ s) s))
        {⟦ Q₁ [ a / l ]ᶠ ⟧ s} {⟦ Q₂ [ a / l ]ᶠ ⟧ s}
        (subR2State' {Q₁}) (subR2State' {Q₂}) p
      subR2State {x₁ ≤ₑ x₂} {a} {l} {s} p =
        begin
          ⟦ x₁ ⟧ₐ (toSt l (⟦ a ⟧ₐ s) s) ≤ᵇ ⟦ x₂ ⟧ₐ (toSt l (⟦ a ⟧ₐ s) s)
        ≡⟨ cong₂ _≤ᵇ_ (sym (subR2StateA {x₁} {a} {l} {s})) (sym (subR2StateA {x₂} {a} {l} {s})) ⟩
          ⟦ x₁ [ a / l ]ᵉ ⟧ₐ s ≤ᵇ ⟦ x₂ [ a / l ]ᵉ ⟧ₐ s
        ≡⟨ p ⟩
          true
        ∎
      subR2State' {x₁ ≤ₑ x₂} {a} {l} {s} p = 
        begin
          ⟦ x₁ [ a / l ]ᵉ ⟧ₐ s ≤ᵇ ⟦ x₂ [ a / l ]ᵉ ⟧ₐ s
        ≡⟨ cong₂ _≤ᵇ_ (subR2StateA {x₁} {a} {l} {s}) (subR2StateA {x₂} {a} {l} {s}) ⟩
          ⟦ x₁ ⟧ₐ (toSt l (⟦ a ⟧ₐ s) s) ≤ᵇ ⟦ x₂ ⟧ₐ (toSt l (⟦ a ⟧ₐ s) s)
        ≡⟨ p ⟩
          true
        ∎ 
    
    --
    -- Demonic soundness
    --

    -- More general definition of soundness
    dsoundness' : {P Q : Formula} {C : Cmdₕ}
              → ⟪ P ⟫ C ⟪ Q ⟫
              → ∀ (ls : List (⊤ᶠ × State))
                → proof (dcondition P ls)
                → proof (dcondition Q (apply-and-fold C ls))

    dsoundness' {P} {Q} {_ |ʷ _} (composition {_} {_} {_} {c₁} {c₂} h₁ h₂) [] pPs = tt
    dsoundness' {P} {Q} {_ |ʷ _} (composition {_} {_} {_} {c₁} {c₂} h₁ h₂) (x ∷ ls) pPs =
      dc-++-eq-∧ʰ {⊤ᶠ} {Q} {foldr _++_ [] (mapᴸ (λ { (_ , s') → ⟦ c₂ ⟧ᶜ s' }) (⟦ c₁ ⟧ᶜ (proj₂ x)))} 
         (dsoundness' h₂ (⟦ c₁ ⟧ᶜ (proj₂ x)) (dc-++-[]  {_} {c₁} {x} (dsoundness' h₁ (x ∷ []) ((proj₁ pPs) , tt))) ,
          dsoundness' (composition h₁ h₂) ls (proj₂ pPs))

    dsoundness' {.(Q [ _ / _ ]ᶠ)} {Q} {_ :=ʷ _} assignment [] pPs = tt
    dsoundness' {.(Q [ _ / _ ]ᶠ)} {Q} {l :=ʷ a} (assignment {P} {a}) (x ∷ ls) pPs =
      subR2State {Q} {a} {l} {proj₂ x} ((proj₁ pPs)) ,
      dsoundness' (assignment {P} {a}) ls (proj₂ pPs)

    dsoundness' {P} {Q} {ifʷ b then _ else _} (if-statement {_} {_} {b} {c₁} {c₂} h₁ h₂) [] pPs = tt
    dsoundness' {P} {Q} {ifʷ b then _ else _} (if-statement {_} {_} {b} {c₁} {c₂} h₁ h₂) (x ∷ ls) pPs =
      dc-++-eq-∧ʰ {⊤ᶠ} {Q} {(⟦ ifʷ b then _ else _ ⟧ᶜ (proj₂ x))}
        (cases-b ,
         dsoundness' (if-statement {_} {_} {b} h₁ h₂) ls (proj₂ pPs))

      where

        cases-b : proof (dcondition Q (⟦ ifʷ b then c₁ else c₂ ⟧ᶜ (proj₂ x)))
        cases-b with (⟦ b ⟧ₒ (proj₂ x)) | inspect ⟦ b ⟧ₒ (proj₂ x)
        ... | false | Eq.[ eq ] =
          dc-++-[] {Q} {c₂} (dsoundness' h₂ (x ∷ []) (((proj₁ pPs) , bIsFalseFollows {proj₂ x} {b} eq) , tt))
        ... | true | Eq.[ eq ] =
          dc-++-[] {Q} {c₁} (dsoundness' h₁ (x ∷ []) (((proj₁ pPs) , bIsTrueFollows {proj₂ x} {b} eq) , tt))

    dsoundness' {P} {P} {forʷ _ doo _} (for-statement h) [] pPs = tt
    dsoundness' {P} {P} {forʷ _ doo _} (for-statement {_} {_} {a} {c} h) (x ∷ ls) pPs = 
      dc-++-eq-∧ʰ {⊤ᶠ} {P} {forDooAux (abs (⟦ a ⟧ₐ (proj₂ x))) ⟦ c ⟧ᶜ (proj₂ x)}
        ( cases-m (abs (⟦ a ⟧ₐ (proj₂ x))) x (proj₁ pPs) ,
         dsoundness' (for-statement {P} {P} {a} {c} h) ls (proj₂ pPs))

      where
      
        cases-m : (n : ℕ) → (x : (⊤ᶠ × State)) → (pPx : proof (⟦ P ⟧ (proj₂ x)))
          → proof (dcondition P (forDooAux n ⟦ c ⟧ᶜ (proj₂ x)))
        cases-m ℕ.zero x pPx = pPx , tt
        cases-m (ℕ.suc n) x pPx = soundOfC>>ForDooAux {n} {proj₂ x} pPx 

          where

            soundOfC>>ForDooAux : {n : ℕ} → ∀ {x' : State}
              → proof (⟦ P ⟧ x')
              → proof (dcondition P ((⟦ c ⟧ᶜ >> forDooAux n ⟦ c ⟧ᶜ) x'))
            soundOfC>>ForDooAux {n} {x'} pPs = 
              cases-ls (⟦ c ⟧ᶜ x')
                (dc-++-[] {P} {c} (dsoundness' h  (( tt , x' ) ∷ []) (pPs , tt)))

              where 

                -- Needed so that we able to recuse on (⟦ c ⟧ᶜ x').
                cases-ls : (ls : List (⊤ᶠ × State)) → (pPls : proof (dcondition P ls)) → 
                  proof (dcondition P (foldr _++_ [] (mapᴸ (λ { (a , s') → forDooAux n ⟦ c ⟧ᶜ s' }) ls)))
                cases-ls [] pPls = tt
                cases-ls (x'' ∷ ls'') pPls = dc-++-eq-∧ʰ {_} {P} {forDooAux n ⟦ c ⟧ᶜ (proj₂ x'')}
                  (cases-m n x'' (proj₁ pPls) ,
                   (cases-ls ls'' (proj₂ pPls)))

    dsoundness' {P} {Q} {C} (implied _ _ _) [] pPs = tt
    dsoundness' {P'} {Q'} {C} (implied {Δ} {P} {P'} {Q} {Q'} P'⇒P Q⇒Q' h) (x ∷ ls) pPs = 
      dc-++-eq-∧ʰ {⊤ᶠ} {Q'} {⟦ C ⟧ᶜ (proj₂ x)}
        (auxAppToCond {⟦ C ⟧ᶜ (proj₂ x)} Q⇒Q'
            (dc-++-[] {Q} {C} (dsoundness' h (x ∷ [])
              ((⟦ P'⇒P ⟧ₓ {proj₂ x} tt ((proj₁ pPs))) , tt))) ,
         (dsoundness' (implied {Δ} {P} {P'} {Q} {Q'} P'⇒P Q⇒Q' h) ls ((proj₂ pPs))))

        where

          auxAppToCond : {ls' : List (⊤ᶠ × State)} → ([] ⊢ Q ⇒ Q')
            → proof (dcondition Q ls') → proof (dcondition Q' ls')
          auxAppToCond {[]} iQ h = tt
          auxAppToCond {x' ∷ ls'} iQ h = (⟦ iQ ⟧ₓ tt ((proj₁ h))) , (auxAppToCond {ls'} iQ (proj₂ h))

    dsoundness' {P} {Q} {_ orʷ _} (or-statement h h₁) [] pPs = tt
    dsoundness' {P} {Q} {_ orʷ _} (or-statement {Δ} {P} {Q} {cₗ} {cᵣ} h₁ h₂) (x ∷ ls) pPs = 
      dc-++-eq-∧ʰ {⊤ᶠ} {Q} {(⟦ cₗ ⟧ᶜ (proj₂ x) ++ ⟦ cᵣ ⟧ᶜ (proj₂ x))}
        (dc-++-eq-∧ʰ {⊤ᶠ}  {Q}  {⟦ cₗ ⟧ᶜ (proj₂ x)}
          (dc-++-[] {Q} {cₗ} (dsoundness' h₁ (x ∷ []) ((proj₁ pPs) , tt)) ,
           dc-++-[] {Q} {cᵣ} (dsoundness' h₂ (x ∷ []) ((proj₁ pPs) , tt))) ,
         dsoundness' (or-statement {Δ} {P} {Q} {cₗ} {cᵣ} h₁ h₂) ls ((proj₂ pPs)))

    -- Soundness
    dsoundness : {P Q : Formula} {C : Cmdₕ}
              → ⟪ P ⟫ C ⟪ Q ⟫
              → ∀ (s : State)
                → proof (⟦ P ⟧ s)
                → proof (dcondition Q (⟦ C ⟧ᶜ s))
    dsoundness {P} {Q} {C} h s pPs = dc-++-[] {_} {C} {tt , s} (dsoundness' {P} {Q} {C} h ((tt , s) ∷ []) (pPs , tt))