open import DemonicHoareLogic
open import HProp
open import Monads

open import Data.Nat using (ℕ; _≡ᵇ_)
open import Data.Integer using (ℤ; _+_; +_; _-_; -_; _≤ᵇ_) renaming (∣_∣ to abs; suc to ℤ-suc)
open import Data.Bool using (Bool; true; false)
open import Data.Empty renaming (⊥ to ⊥ᶠ; ⊥-elim to ⊥-elimᶠ)
open import Data.Unit using (tt) renaming (⊤ to ⊤ᶠ)
open import Data.List using (List; []; _∷_; [_]; _++_; foldr; map)
open import Data.Product using (Σ; _,_; proj₁; proj₂; Σ-syntax; _×_)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_])

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong; cong₂; subst; [_]; inspect)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)

open import Relation.Nullary renaming (¬_ to ¬ᶠ_ )


--
-- Soundness of Hoar logic for WHILE with states and demonic nondeterminism
--

module DemonicSoundness where 

    open import PQSyntax L

    open import PQDeduction L _≡ᵇ_ 

    open import PQSemantics L _≡ᵇ_

    open import PQSubstitution L _≡ᵇ_

    open import WhileSemantics L _≡ᵇ_ renaming (⟦_⟧ to ⟦_⟧ᶜ)

    open import WhileSyntax L

    open Monad NDS-Monad


    -- Demonic condition - A formula `Q` needs to hold for all the states of a list.
    dcondition : {A : Set} → (Q : Formula) → List (A × State) → HProp
    dcondition Q [] = ⊤ʰ
    dcondition Q (x ∷ sts) = (⟦ Q ⟧ (proj₂ x)) ∧ʰ dcondition Q sts

    --
    -- Some useful lemmas
    --

    dc-++-eq-∧ʰ : {A : Set} {Q : Formula} {ls ls' : List (A × State)}
      → proof ((dcondition Q ls) ∧ʰ (dcondition Q ls')) → proof (dcondition Q (ls ++ ls'))
    dc-++-eq-∧ʰ {_} {_} {[]} {ls'} (hₗ , hᵣ) = hᵣ
    dc-++-eq-∧ʰ {_} {_} {x ∷ ls} {ls'} (hₗ , hᵣ) = (proj₁ hₗ) , dc-++-eq-∧ʰ {_} {_} {ls} {ls'} ((proj₂ hₗ) , hᵣ)

    apply-and-fold : Cmdₕ → List (⊤ᶠ × State) → List (⊤ᶠ × State)
    apply-and-fold c ls = foldr _++_ [] (map (λ {(_ , s) → ⟦ c ⟧ᶜ s }) ls)

    aux : {A : Set} {ls : List A} → (ls ++ []) ≡ ls
    aux {ls = []} = refl
    aux {ls = x ∷ ls} = cong (λ y → x ∷ y) aux

    dc-++-[] :  {θ : Formula} {c : Cmdₕ} {x : ⊤ᶠ × State}
      → proof (dcondition θ (⟦ c ⟧ᶜ (proj₂ x) ++ [])) → proof (dcondition θ (⟦ c ⟧ᶜ (proj₂ x)))
    dc-++-[] {_} {c} {x} h rewrite (aux {_} {⟦ c ⟧ᶜ (proj₂ x)}) = h

    trueIsNotEqToFalse : (true ≡ false) → ⊥ᶠ
    trueIsNotEqToFalse ()

    -- Show that the interpretation of Expr and AExprₕ are equivalent.
    itr-are-equal : (a : AExprₕ) → ⟦ toExprₚ a ⟧ₑ ≡ ⟦ a ⟧ᵃ
    itr-are-equal (Int x) = refl
    itr-are-equal (Loc x) = refl
    itr-are-equal (-' a) = cong ((λ e Γ → - e Γ )) (itr-are-equal a)
    itr-are-equal (a₁ +' a₂) = cong₂ (λ e₁ e₂ Γ → e₁ Γ + e₂ Γ) (itr-are-equal a₁) (itr-are-equal a₂)

    -- Relate how the boolean expressions are interpreted in WHILE language and how they are interpreted in the
    -- PQ logic.

    interleaved mutual

      -- If `b` evaluates to true, then there exist a witness of `⟦ toFormulaₚ b ⟧ s`.
      bIsTrueFollows  : {s : State} → {b : BExprₕ} → (⟦ b ⟧ᵇ s ≡ true) → (proof (⟦ toFormulaₚ b ⟧ s))
      -- If `b` evaluates to false, then there does NOT exist a witness of `⟦ toFormulaₚ b ⟧ s`.
      bIsFalseFollows : {s : State} → {b : BExprₕ} → (⟦ b ⟧ᵇ s ≡ false) → ¬ᶠ (proof (⟦ toFormulaₚ b ⟧ s))
      bIsTrueFollows  {s} {True} p = tt
      bIsFalseFollows {s} {True} ()
      bIsTrueFollows  {s} {¬' b} p x with ⟦ b ⟧ᵇ s | inspect ⟦ b ⟧ᵇ s
      ... | false | Eq.[ eq ] = bIsFalseFollows {s} {b} eq  x
      bIsFalseFollows {s} {¬' b} p x with ⟦ b ⟧ᵇ s | inspect ⟦ b ⟧ᵇ s
      ... | true  | Eq.[ eq ] = x (bIsTrueFollows {s} {b} eq)
      bIsTrueFollows  {s} {b₁ ∧' b₂} x with ⟦ b₁ ⟧ᵇ s | ⟦ b₂ ⟧ᵇ s |  inspect ⟦ b₁ ⟧ᵇ s | inspect ⟦ b₂ ⟧ᵇ s
      ... | true  | true  | Eq.[ eq₁ ] | Eq.[ eq₂ ] = bIsTrueFollows {s} {b₁} eq₁ , bIsTrueFollows {s} {b₂} eq₂
      bIsFalseFollows {s} {b₁ ∧' b₂} x x' with ⟦ b₁ ⟧ᵇ s | ⟦ b₂ ⟧ᵇ s |  inspect ⟦ b₁ ⟧ᵇ s | inspect ⟦ b₂ ⟧ᵇ s
      ... | false | false | Eq.[ eq₁ ] | _          = bIsFalseFollows {s} {b₁} eq₁ (proj₁ x')
      ... | false | true  | Eq.[ eq₁ ] | _          = bIsFalseFollows {s} {b₁} eq₁ (proj₁ x')
      ... | true  | false | _          | Eq.[ eq₂ ] = bIsFalseFollows {s} {b₂} eq₂ (proj₂ x')
      bIsTrueFollows  {s} {b₁ ∨' b₂} x with ⟦ b₁ ⟧ᵇ s | ⟦ b₂ ⟧ᵇ s |  inspect ⟦ b₁ ⟧ᵇ s | inspect ⟦ b₂ ⟧ᵇ s
      ... | false | true  | _          | Eq.[ eq₂ ] = ∣ inj₂ (bIsTrueFollows {s} {b₂} eq₂) ∣
      ... | true  | false | Eq.[ eq₁ ] | _          = ∣ inj₁ (bIsTrueFollows {s} {b₁} eq₁) ∣
      ... | true  | true  | Eq.[ eq₁ ] | _          = ∣ inj₁ (bIsTrueFollows {s} {b₁} eq₁) ∣
      bIsFalseFollows {s} {b₁ ∨' b₂} x x' with ⟦ b₁ ⟧ᵇ s | ⟦ b₂ ⟧ᵇ s |  inspect ⟦ b₁ ⟧ᵇ s | inspect ⟦ b₂ ⟧ᵇ s
      ... | false | false | Eq.[ eq₁ ] | Eq.[ eq₂ ] =
        ∥∥-elim (λ x ())
          (λ { (inj₁ y) → bIsFalseFollows {s} {b₁} eq₁ y
             ; (inj₂ y) →  bIsFalseFollows {s} {b₂} eq₂ y } ) x'
      bIsTrueFollows  {S} {x₁ ≤' x₂} x rewrite itr-are-equal x₁ rewrite itr-are-equal x₂ = x
      bIsFalseFollows {S} {x₁ ≤' x₂} x x' rewrite itr-are-equal x₁ rewrite itr-are-equal x₂
        rewrite x = trueIsNotEqToFalse (sym x')

    -- Show how is substitution related to a state.

    -- subR2StateA : {a : Expr} → {b : Expr} → {l : ℕ} → {s : state}
    --      →  (⟦ a [ b / l ]ᵃ ⟧ₑ s) ≡ (⟦ a ⟧ₑ (toSt l (⟦ b ⟧ₑ s) s))
    subR2StateA : {a : Expr} → {b : AExprₕ} → {l : ℕ} → {s : state}
         →  (⟦ a [ (toExprₚ b) / l ]ᵃ ⟧ₑ s) ≡ (⟦ a ⟧ₑ (toSt l (⟦ b ⟧ᵃ s) s))
    subR2StateA {int x} {b} {l} {s} = refl
    subR2StateA {loc l'} {b} {l} {s} with (l ≡ᵇ l')
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
    
    --
    -- Demonic soundness
    --

    -- More general definition of soundness
    gdsoundness : {P Q : Formula} {C : Cmdₕ}
              → ⟪ P ⟫ C ⟪ Q ⟫
              → ∀ (ls : List (⊤ᶠ × State))
                → proof (dcondition P ls)
                → proof (dcondition Q (apply-and-fold C ls))

    gdsoundness {P} {Q} {_ ； _} (composition {_} {_} {_} {c₁} {c₂} h₁ h₂) [] pPs = tt
    gdsoundness {P} {Q} {_ ； _} (composition {_} {_} {_} {c₁} {c₂} h₁ h₂) (x ∷ ls) pPs =
      dc-++-eq-∧ʰ {⊤ᶠ} {Q} {foldr _++_ [] (map (λ { (_ , s') → ⟦ c₂ ⟧ᶜ s' }) (⟦ c₁ ⟧ᶜ (proj₂ x)))} 
         (gdsoundness h₂ (⟦ c₁ ⟧ᶜ (proj₂ x)) (dc-++-[]  {_} {c₁} {x} (gdsoundness h₁ (x ∷ []) ((proj₁ pPs) , tt))) ,
          gdsoundness (composition h₁ h₂) ls (proj₂ pPs))

    gdsoundness {.(Q [ _ / _ ]ᶠ)} {Q} {_ ≔ _} assignment [] pPs = tt
    gdsoundness {.(Q [ _ / _ ]ᶠ)} {Q} {l ≔ a} (assignment {P} {a}) (x ∷ ls) pPs =
      subR2State {Q} {a} {l} {proj₂ x} ((proj₁ pPs)) ,
      gdsoundness (assignment {P} {a}) ls (proj₂ pPs)

    gdsoundness {P} {Q} {If b Then _ Else _} (if-statement {_} {_} {b} {c₁} {c₂} h₁ h₂) [] pPs = tt
    gdsoundness {P} {Q} {If b Then _ Else _} (if-statement {_} {_} {b} {c₁} {c₂} h₁ h₂) (x ∷ ls) pPs =
      dc-++-eq-∧ʰ {⊤ᶠ} {Q} {(⟦ If b Then _ Else _ ⟧ᶜ (proj₂ x))}
        (cases-b ,
         gdsoundness (if-statement {_} {_} {b} h₁ h₂) ls (proj₂ pPs))

      where

        cases-b : proof (dcondition Q (⟦ If b Then c₁ Else c₂ ⟧ᶜ (proj₂ x)))
        cases-b with (⟦ b ⟧ᵇ (proj₂ x)) | inspect ⟦ b ⟧ᵇ (proj₂ x)
        ... | false | Eq.[ eq ] =
          dc-++-[] {Q} {c₂} (gdsoundness h₂ (x ∷ []) (((proj₁ pPs) , bIsFalseFollows {proj₂ x} {b} eq) , tt))
        ... | true | Eq.[ eq ] =
          dc-++-[] {Q} {c₁} (gdsoundness h₁ (x ∷ []) (((proj₁ pPs) , bIsTrueFollows {proj₂ x} {b} eq) , tt))

    gdsoundness {P} {P} {For _ Do _} (for-statement h) [] pPs = tt
    gdsoundness {P} {P} {For _ Do _} (for-statement {_} {a} {c} h) (x ∷ ls) pPs = 
      dc-++-eq-∧ʰ {⊤ᶠ} {P} {forDooAux (abs (⟦ a ⟧ᵃ (proj₂ x))) ⟦ c ⟧ᶜ (proj₂ x)}
        ( cases-m (abs (⟦ a ⟧ᵃ (proj₂ x))) x (proj₁ pPs) ,
          gdsoundness (for-statement {P} {a} {c} h) ls (proj₂ pPs))

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
                (dc-++-[] {P} {c} (gdsoundness h  (( tt , x' ) ∷ []) (pPs , tt)))

              where 

                -- Needed so that we able to recuse on (⟦ c ⟧ᶜ x').
                cases-ls : (ls : List (⊤ᶠ × State)) → (pPls : proof (dcondition P ls)) → 
                  proof (dcondition P (foldr _++_ [] (map (λ { (a , s') → forDooAux n ⟦ c ⟧ᶜ s' }) ls)))
                cases-ls [] pPls = tt
                cases-ls (x'' ∷ ls'') pPls = dc-++-eq-∧ʰ {_} {P} {forDooAux n ⟦ c ⟧ᶜ (proj₂ x'')}
                  (cases-m n x'' (proj₁ pPls) ,
                   (cases-ls ls'' (proj₂ pPls)))

    gdsoundness {P} {Q} {C} (implied _ _ _) [] pPs = tt
    gdsoundness {P'} {Q'} {C} (implied {P} {P'} {Q} {Q'} P'⇒P Q⇒Q' h) (x ∷ ls) pPs = 
      dc-++-eq-∧ʰ {⊤ᶠ} {Q'} {⟦ C ⟧ᶜ (proj₂ x)}
        (auxAppToCond {⟦ C ⟧ᶜ (proj₂ x)} Q⇒Q'
            (dc-++-[] {Q} {C} (gdsoundness h (x ∷ [])
              ((⟦ P'⇒P ⟧ₓ {proj₂ x} tt ((proj₁ pPs))) , tt))) ,
         (gdsoundness (implied {P} {P'} {Q} {Q'} P'⇒P Q⇒Q' h) ls ((proj₂ pPs))))

        where

          auxAppToCond : {ls' : List (⊤ᶠ × State)} → ([] ⊢ Q ⇒ Q')
            → proof (dcondition Q ls') → proof (dcondition Q' ls')
          auxAppToCond {[]} iQ h = tt
          auxAppToCond {x' ∷ ls'} iQ h = (⟦ iQ ⟧ₓ tt ((proj₁ h))) , (auxAppToCond {ls'} iQ (proj₂ h))

    gdsoundness {.(Pₗ ∧ Pᵣ)} {Q} {.(cₗ Or cᵣ)} (or-statement {Pₗ} {Pᵣ} {Q} {cₗ} {cᵣ} h₁ h₂) [] pPs = tt
    gdsoundness {.(Pₗ ∧ Pᵣ)} {Q} {.(cₗ Or cᵣ)} (or-statement {Pₗ} {Pᵣ} {Q} {cₗ} {cᵣ} h₁ h₂) (x ∷ ls) pPs =
      dc-++-eq-∧ʰ {⊤ᶠ} {Q} {(⟦ cₗ ⟧ᶜ (proj₂ x) ++ ⟦ cᵣ ⟧ᶜ (proj₂ x))}
        (dc-++-eq-∧ʰ {⊤ᶠ} {Q}  {⟦ cₗ ⟧ᶜ (proj₂ x)}
          (dc-++-[] {Q} {cₗ} (gdsoundness h₁ (x ∷ []) ((proj₁ (proj₁ pPs) , tt))) ,
           dc-++-[] {Q} {cᵣ} (gdsoundness h₂ (x ∷ []) (proj₂ (proj₁ pPs) , tt))) ,
         gdsoundness (or-statement {Pₗ} {Pᵣ} {Q} {cₗ} {cᵣ} h₁ h₂) ls ((proj₂ pPs)))
    
    gdsoundness {P} {.P} {Skip} skip [] pPs = tt
    gdsoundness {P} {.P} {Skip} skip (x ∷ ls) pPs =
      (proj₁ pPs) ,
      (gdsoundness skip ls ((proj₂ pPs)))

    -- Soundness
    dsoundness : {P Q : Formula} {C : Cmdₕ}
              → ⟪ P ⟫ C ⟪ Q ⟫
              → ∀ (s : State)
                → proof (⟦ P ⟧ s)
                → proof (dcondition Q (⟦ C ⟧ᶜ s))
    dsoundness {P} {Q} {C} h s pPs = dc-++-[] {_} {C} {tt , s} (gdsoundness {P} {Q} {C} h ((tt , s) ∷ []) (pPs , tt)) 
   