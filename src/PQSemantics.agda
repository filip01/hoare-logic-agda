open import HProp

open import Relation.Binary.Definitions using (Decidable)
open import Relation.Nullary using (Dec)
open import Agda.Builtin.Equality using (_≡_)

open import Data.Product

import Relation.Binary.PropositionalEquality as Eq
open Eq using (refl; sym; trans; cong; cong₂; subst; inspect) renaming ([_] to [|_|])
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; step-≡˘; _∎)

open import Data.Nat using (ℕ ; suc) renaming (_<ᵇ_ to _ℕ<ᵇ_)
open import Data.Integer using (ℤ; _+_; +_; _-_; -_; _≤ᵇ_; _≤_) renaming (∣_∣ to abs; _≟_ to _≟ℤ_; suc to ℤ-suc)
open import Data.Integer.Properties
open import Data.Bool using (Bool; true; false; T) renaming (_<_ to _<b_)
open import Data.List using (List; []; _∷_; [_]; _++_)

open import Data.Sum
open import Data.Empty renaming (⊥ to ⊥ₜ)
open import Data.Unit using (⊤; tt)


--
-- Interpretation of PQ logic
--

module PQSemantics (L : Set) (_==_ : L → L → Bool) where

   open import PQSyntax L renaming (⊥ to ⊥ᶠ;  ⊤ to ⊤ᶠ)

   open import PQDeduction L _==_ renaming (⊥-elim to ⊥-elimᵣ) hiding (_∈_)

   open import PQSubstitution L _==_


   ℙ = HProp   -- unicode \bP


   State = L → ℤ


   _=ₑₕ_ : ℤ → ℤ → HProp
   x =ₑₕ y = ⟨ x ≡ y , (λ {refl refl → refl}) ⟩

   _≤ₑₕ_ : ℤ → ℤ → HProp
   x ≤ₑₕ y = ⟨ (x ≤ᵇ y) ≡ true , ≤ᵇ≡true-is-prop x y ⟩
      where
         ≤ᵇ≡true-is-prop : (x y : ℤ) → is-proposition ((x ≤ᵇ y) ≡ true)
         ≤ᵇ≡true-is-prop x y p q with x ≤ᵇ y
         ≤ᵇ≡true-is-prop x y refl refl | true = refl

   --
   -- The recursively defined interpretation function for expressions.
   --

   ⟦_⟧ₑ : Expr → State → ℤ
   ⟦ int x ⟧ₑ Γ = x
   ⟦ loc l ⟧ₑ Γ = Γ l
   ⟦ suc a ⟧ₑ Γ = ℤ-suc (⟦ a ⟧ₑ Γ)
   ⟦ -ₑ a ⟧ₑ Γ = - (⟦ a ⟧ₑ Γ)
   ⟦ a₁ +ₑ a₂ ⟧ₑ Γ = (⟦ a₁ ⟧ₑ Γ) + (⟦ a₂ ⟧ₑ Γ) 

   --
   -- Some useful lemmas.
   --

   n-≤ᵇ-n : {n : ℕ} → (n Data.Nat.≤ᵇ n) ≡ true
   n-≤ᵇ-n {ℕ.zero} = refl
   n-≤ᵇ-n {suc n} = m-ℕ<ᵇ-suc-m {n}
      where
         m-ℕ<ᵇ-suc-m : {m : ℕ} → (m ℕ<ᵇ suc m) ≡ true
         m-ℕ<ᵇ-suc-m {ℕ.zero} = refl
         m-ℕ<ᵇ-suc-m {suc m} = m-ℕ<ᵇ-suc-m {m}

   n-≤ᵇ-suc-n : {n : ℕ} → (n Data.Nat.≤ᵇ (suc n)) ≡ true
   n-≤ᵇ-suc-n {ℕ.zero} = refl
   n-≤ᵇ-suc-n {suc n} = m-ℕ<ᵇ-suc-suc-m {n}
      where
         m-ℕ<ᵇ-suc-suc-m : {m : ℕ} → (m ℕ<ᵇ suc (suc m)) ≡ true
         m-ℕ<ᵇ-suc-suc-m {ℕ.zero} = refl
         m-ℕ<ᵇ-suc-suc-m {suc m} = m-ℕ<ᵇ-suc-suc-m {m}
   
   negsuc-n-≤ᵇ-1-⊖-n : {n : ℕ} → (ℤ.negsuc n ≤ᵇ 1 Data.Integer.⊖ suc n) ≡ true
   negsuc-n-≤ᵇ-1-⊖-n {ℕ.zero} = refl
   negsuc-n-≤ᵇ-1-⊖-n {suc n} = n-≤ᵇ-suc-n {n}

   ≡true-T : {a : Bool} → a ≡ true → T a
   ≡true-T {true} _ = tt

   T-≡true : {a : Bool} → T a → a ≡ true
   T-≡true {true} _ = refl

   --
   -- The recursively defined interpretation function for formulae.
   --

   ⟦_⟧ : Formula → State → ℙ
   ⟦ ⊤ᶠ ⟧ s = ⊤ʰ
   ⟦ ⊥ᶠ ⟧ s = ⊥ʰ
   ⟦ P₁ ∧ P₂ ⟧ S = ⟦ P₁ ⟧ S ∧ʰ ⟦ P₂ ⟧ S
   ⟦ P₁ ∨ P₂ ⟧ S = ⟦ P₁ ⟧ S ∨ʰ ⟦ P₂ ⟧ S
   ⟦ P₁ ⇒ P₂ ⟧ S = ⟦ P₁ ⟧ S ⇒ʰ ⟦ P₂ ⟧ S
   ⟦ x₁ =ₑ x₂ ⟧ S = (⟦ x₁ ⟧ₑ S) =ₑₕ (⟦ x₂ ⟧ₑ S)
   ⟦ x₁ ≤ₑ x₂ ⟧ S = (⟦ x₁ ⟧ₑ S) ≤ₑₕ (⟦ x₂ ⟧ₑ S)


   --
   -- The interpretation function is also extended to hypotheses.
   --

   ⟦_⟧ₕ : Hypotheses → State → ℙ
   ⟦ [] ⟧ₕ s = ⊤ʰ
   ⟦ P ∷ Δ ⟧ₕ s = ⟦ P ⟧ s ∧ʰ ⟦ Δ ⟧ₕ s


   ⟦⟧ₕ-++ : (Δ₁ Δ₂ : Hypotheses) → {s : State}
         → proof (⟦ Δ₁ ++ Δ₂ ⟧ₕ s) → proof (⟦ Δ₁ ⟧ₕ s ∧ʰ ⟦ Δ₂ ⟧ₕ s)

   ⟦⟧ₕ-++ [] Δ₂ p = tt , p
   ⟦⟧ₕ-++ (x ∷ Δ₁) Δ₂ {s} p with ⟦⟧ₕ-++ Δ₁ Δ₂ (∧ʰ-proj₂ (⟦ x ⟧ s) (⟦ Δ₁ ++ Δ₂ ⟧ₕ s) p)
   ... | i , j = (∧ʰ-proj₁ (⟦ x ⟧ s) (⟦ Δ₁ ++ Δ₂ ⟧ₕ s) p , i) , j


   sym⟦⟧ₕ-++ : (Δ₁ Δ₂ : Hypotheses) → {s : State}
            → proof (⟦ Δ₁ ⟧ₕ s ∧ʰ ⟦ Δ₂ ⟧ₕ s) → proof (⟦ Δ₁ ++ Δ₂ ⟧ₕ s)

   sym⟦⟧ₕ-++ [] Δ₂ {s} (_ , p) = p
   sym⟦⟧ₕ-++ (x ∷ Δ₁) Δ₂ {s} ((pₓ , p₁) , p₂) = pₓ , sym⟦⟧ₕ-++ Δ₁ Δ₂ {s} (p₁ , p₂)

   ---
   --- Soundness of PQ logic
   ---

   ⟦_⟧ₓ : {Δ : Hypotheses} → {φ : Formula} → (Δ ⊢ φ) → 
         ∀ {s : State} → proof (⟦ Δ ⟧ₕ s) -> proof (⟦ φ ⟧ s)

   ⟦ weaken {Δ₁} {Δ₂} φ {ψ} h ⟧ₓ p with ⟦⟧ₕ-++ Δ₁ (φ ∷ Δ₂) p
   ... | p₁ , _ , p₂ = ⟦ h ⟧ₓ (sym⟦⟧ₕ-++ Δ₁ Δ₂ (p₁ , p₂))

   ⟦ contract {Δ₁} {Δ₂} φ {ψ} h ⟧ₓ p with ⟦⟧ₕ-++ Δ₁ (φ ∷ Δ₂) p
   ... | p₁ , p-φ , p₂ = ⟦ h ⟧ₓ (sym⟦⟧ₕ-++ Δ₁ (φ ∷ φ ∷ Δ₂) (p₁ , (p-φ , p-φ , p₂)))

   ⟦ exchange {Δ₁} {Δ₂} φ₁ φ₂ {ψ} h ⟧ₓ p with ⟦⟧ₕ-++ Δ₁ (φ₂ ∷ φ₁ ∷ Δ₂) p
   ... | p₁ , p-φ₂ , p-φ₁ , p₂ = ⟦ h ⟧ₓ (sym⟦⟧ₕ-++ Δ₁ (φ₁ ∷ φ₂ ∷ Δ₂) (p₁ , (p-φ₁ , (p-φ₂ , p₂))))

   ⟦ hyp {φ ∷ Δ} φ ⦃ ∈-here ⦄ ⟧ₓ {s} p = ∧ʰ-proj₁ (⟦ φ ⟧ s) (⟦ Δ ⟧ₕ s) p

   ⟦ hyp {ψ ∷ Δ} φ {{∈-there {{e}}}}  ⟧ₓ {s} p = 
      ⟦ hyp φ ⟧ₓ {s} (∧ʰ-proj₂ (⟦ ψ ⟧ s) (⟦ Δ ⟧ₕ s) p)
      
   ⟦ ⊤-intro ⟧ₓ p = tt

   ⟦ ⊥-elimᵣ h ⟧ₓ p = ⊥-elim  (⟦ h ⟧ₓ p)

   ⟦ ∧-intro h₁ h₂ ⟧ₓ p = (⟦ h₁ ⟧ₓ p) , (⟦ h₂ ⟧ₓ p)

   ⟦ ∧-elim₁ {Δ} {φ} {ψ} h ⟧ₓ {s} p = ∧ʰ-proj₁ (⟦ φ ⟧ s) (⟦ ψ ⟧ s) (⟦ h ⟧ₓ p)

   ⟦ ∧-elim₂ {Δ} {φ} {ψ} h ⟧ₓ {s} p = ∧ʰ-proj₂ (⟦ φ ⟧ s) (⟦ ψ ⟧ s) (⟦ h ⟧ₓ p)

   ⟦ ∨-intro₁ {Δ} {φ} {ψ} h ⟧ₓ {s} p = ∨ʰ-inj₁ (⟦ φ ⟧ s) (⟦ ψ ⟧ s) (⟦ h ⟧ₓ p) 

   ⟦ ∨-intro₂ {Δ} {φ} {ψ} h ⟧ₓ {s} p = ∨ʰ-inj₂ (⟦ φ ⟧ s) (⟦ ψ ⟧ s) (⟦ h ⟧ₓ p)

   ⟦ ∨-elim {Δ} {φ₁} {φ₂} {ψ} h₁₂ h₁ h₂ ⟧ₓ {s} p = ∨ʰ-idem {⟦ ψ ⟧ s} pψ∨ψ
      where
         pΔ∨ : proof (⟦ Δ ⟧ₕ s ∧ʰ (⟦ φ₁ ⟧ s ∨ʰ ⟦ φ₂ ⟧ s))
         pΔ∨ = p , (⟦ h₁₂ ⟧ₓ p)

         p∧∨∧ : proof ((⟦ Δ ⟧ₕ s ∧ʰ ⟦ φ₁ ⟧ s) ∨ʰ (⟦ Δ ⟧ₕ s ∧ʰ ⟦ φ₂ ⟧ s))
         p∧∨∧ = ∧ʰ-distribˡ (⟦ Δ ⟧ₕ s) (⟦ φ₁ ⟧ s) (⟦ φ₂ ⟧ s) pΔ∨

         aux₁ : (a b : HProp) → proof (a ∧ʰ b) → proof (a ∧ʰ (b ∧ʰ ⊤ʰ))
         aux₁ _ _ (x , y) = x , y , tt

         p++∨++ : proof ((⟦ Δ ++ [ φ₁ ] ⟧ₕ s) ∨ʰ (⟦ Δ ++ [ φ₂ ] ⟧ₕ s))
         p++∨++ = ∨ʰ-cong (⟦ Δ ⟧ₕ s ∧ʰ ⟦ φ₁ ⟧ s) (⟦ Δ ⟧ₕ s ∧ʰ ⟦ φ₂ ⟧ s) {⟦ Δ ++ [ φ₁ ] ⟧ₕ s} {(⟦ Δ ++ [ φ₂ ] ⟧ₕ s)}
                        (λ x → (sym⟦⟧ₕ-++ Δ [ φ₁ ]) (aux₁ (⟦ Δ ⟧ₕ s) (⟦ φ₁ ⟧ s)  x)) 
                        (λ x → (sym⟦⟧ₕ-++ Δ [ φ₂ ]) (aux₁ (⟦ Δ ⟧ₕ s) (⟦ φ₂ ⟧ s) x)) p∧∨∧

         pψ∨ψ : proof ( ⟦ ψ ⟧ s ∨ʰ ⟦ ψ ⟧ s)
         pψ∨ψ = ∨ʰ-cong  (⟦ Δ ++ [ φ₁ ] ⟧ₕ s) (⟦ Δ ++ [ φ₂ ] ⟧ₕ s) {⟦ ψ ⟧ s} {⟦ ψ ⟧ s} 
                     ⟦ h₁ ⟧ₓ ⟦ h₂ ⟧ₓ p++∨++

   ⟦ ⇒-intro {Δ} {φ} {ψ} h ⟧ₓ {s} p = λ x → ⟦ h ⟧ₓ (sym⟦⟧ₕ-++ Δ [ φ ] (p , (x , tt)))

   ⟦ ⇒-elim {Δ} {φ} {ψ} h₁ h₂ ⟧ₓ {s} p = ⟦ h₁ ⟧ₓ p (⟦ h₂ ⟧ₓ p)

   ⟦ =ₑ-intro ⟧ₓ {s} p = refl

   ⟦ =ₑ-refl h ⟧ₓ {s} p = sym (⟦ h ⟧ₓ p)

   ⟦ =ₑ-trans h₁ h₂ ⟧ₓ {s} p = trans (⟦ h₁ ⟧ₓ p) (⟦ h₂ ⟧ₓ p)

   ⟦ ≤ₑ-add {Δ} {x} {y} {z} h ⟧ₓ {s} p = 
      T-≡true (≤⇒≤ᵇ (
         +-monoˡ-≤ (⟦ z ⟧ₑ s)
            (≤ᵇ⇒≤ {⟦ x ⟧ₑ s } (≡true-T (⟦ h ⟧ₓ p)))))

   ⟦ +ₚ-zero {Δ} {x} ⟧ₓ {s} p = +-identityʳ (⟦ x ⟧ₑ s)

   ⟦ +ₚ-comm {Δ} {x} {y} ⟧ₓ {s} p = +-comm (⟦ x ⟧ₑ s) (⟦ y ⟧ₑ s)

   ⟦ =ₑ-subst {Δ} {P} {l} {x} {y} x=y h ⟧ₓ {s} p = aux-=ₑ-subst P {x} {y} (⟦ x=y ⟧ₓ p) (⟦ h ⟧ₓ p)

      where 

         -- Substitution over expressions.
         aux-=ₑ-subst-expr : (e : Expr) →
            {x y : Expr} →
            (proof (⟦ x ⟧ₑ s =ₑₕ ⟦ y ⟧ₑ s)) →
            ⟦ e [ x / l ]ᵃ ⟧ₑ s ≡ ⟦ e [ y / l ]ᵃ ⟧ₑ s

         aux-=ₑ-subst-expr (int i) h = refl
         aux-=ₑ-subst-expr (loc l') {x} {y} h with l == l'
         ... | false = refl
         ... | true = h
         aux-=ₑ-subst-expr (suc e) h = cong ℤ-suc (aux-=ₑ-subst-expr e h)
         aux-=ₑ-subst-expr (-ₑ e) h = cong -_  ((aux-=ₑ-subst-expr e h))
         aux-=ₑ-subst-expr (e₁ +ₑ e₂) h =
            cong₂ _+_
               ((aux-=ₑ-subst-expr e₁ h))
               ((aux-=ₑ-subst-expr e₂ h))
      
         -- Substitution over formulas.
         aux-=ₑ-subst : (P : Formula) →
            {x y : Expr} →
            (proof (⟦ x ⟧ₑ s =ₑₕ ⟦ y ⟧ₑ s)) →
            (proof (⟦ P [ x / l ]ᶠ ⟧ s)) →
               proof (⟦ (P [ y / l ]ᶠ) ⟧ s)

         aux-=ₑ-subst ⊤ᶠ x=y h = tt
         aux-=ₑ-subst ⊥ᶠ x=y h = h
         aux-=ₑ-subst (P₁ ∧ P₂) x=y h =
            aux-=ₑ-subst P₁ x=y (proj₁ h) ,
            aux-=ₑ-subst P₂ x=y (proj₂ h)
         aux-=ₑ-subst (P₁ ∨ P₂) {x} {y} x=y  h = ∨ʰ-cong
            (⟦ P₁ [ x / l ]ᶠ ⟧ s) (⟦ P₂ [ x / l ]ᶠ ⟧ s)
            {⟦ P₁ [ y / l ]ᶠ ⟧ s} {⟦ P₂ [ y / l ]ᶠ ⟧ s}
            (λ h → aux-=ₑ-subst P₁ {x} {y} x=y h)
            (λ h → aux-=ₑ-subst P₂ {x} {y} x=y h)
            h
         aux-=ₑ-subst (P₁ ⇒ P₂) {x} {y} x=y h =
            λ h' → aux-=ₑ-subst P₂ x=y (h
               (aux-=ₑ-subst P₁ {y} {x} (sym x=y) h'))
         aux-=ₑ-subst (e₁ =ₑ e₂) {x} {y} x=y h =
            trans
               (sym (aux-=ₑ-subst-expr e₁ {x} {y} (x=y)))
               (trans h (sym (aux-=ₑ-subst-expr e₂ (sym x=y))))
         aux-=ₑ-subst (e₁ ≤ₑ e₂) {x} {y} x=y h =
            T-≡true ( ≤⇒≤ᵇ (subst (λ x → x) (sym e₁-sub-y-≤-e₁-sub-x) (≤ᵇ⇒≤ (≡true-T h))))

            where 

               e₁-sub-y-≤-e₁-sub-x :
                  (⟦ e₁ [ y / l ]ᵃ ⟧ₑ s ≤ ⟦ e₂ [ y / l ]ᵃ ⟧ₑ s) ≡
                     (⟦ e₁ [ x / l ]ᵃ ⟧ₑ s ≤ ⟦ e₂ [ x / l ]ᵃ ⟧ₑ s)
               e₁-sub-y-≤-e₁-sub-x =
                  cong₂ _≤_
                     (aux-=ₑ-subst-expr e₁ {y} {x} (sym x=y))
                     (aux-=ₑ-subst-expr e₂ {y} {x} (sym x=y))

   ⟦ suc-ℤ ⟧ₓ p = refl

   ⟦ ≤ₑ-intro {_} {x} ⟧ₓ {s} p with (⟦ x ⟧ₑ s)
   ⟦ ≤ₑ-intro {_} {x} ⟧ₓ {s} p | +_ n = n-≤ᵇ-n {n}
   ⟦ ≤ₑ-intro {_} {x} ⟧ₓ {s} p | ℤ.negsuc n = n-≤ᵇ-n {n}

   ⟦ ≤ₑ-suc {_} {x} ⟧ₓ {s} p with (⟦ x ⟧ₑ s)
   ... | +_ n = n-≤ᵇ-suc-n {n}
   ... | ℤ.negsuc n = negsuc-n-≤ᵇ-1-⊖-n {n}
 
   ⟦ ≤ₑ-trans {_} {x} {y} {z} a₁ a₂ ⟧ₓ {s} p =
      T-≡true ( ≤⇒≤ᵇ {⟦ x ⟧ₑ s} {⟦ z ⟧ₑ s}
         (≤-trans
            (≤ᵇ⇒≤ (≡true-T (⟦ a₁ ⟧ₓ p)))
            ((≤ᵇ⇒≤ (≡true-T (⟦ a₂ ⟧ₓ p))))))
   
   ⟦ +ₚ-carry  {_} {x} {y} ⟧ₓ {s} p =
      begin
         ⟦ x ⟧ₑ s + (+ 1 + ⟦ y ⟧ₑ s)
      ≡⟨ sym (+-assoc (⟦ x ⟧ₑ s) (+ 1) (⟦ y ⟧ₑ s)) ⟩
         (⟦ x ⟧ₑ s + (+ 1)) + ⟦ y ⟧ₑ s
      ≡⟨ cong (λ x → x + ⟦ y ⟧ₑ s) {⟦ x ⟧ₑ s + (+ 1)} {(+ 1) + ⟦ x ⟧ₑ s} (+-comm (⟦ x ⟧ₑ s) ((+ 1))) ⟩
         ((+ 1) + ⟦ x ⟧ₑ s) + ⟦ y ⟧ₑ s
      ≡⟨ +-assoc (+ 1) (⟦ x ⟧ₑ s) (⟦ y ⟧ₑ s) ⟩
         ℤ-suc (⟦ x ⟧ₑ s + ⟦ y ⟧ₑ s)
      ∎             

   ⟦ neg-ℤ ⟧ₓ {s} p = refl
   
   ⟦ +ₚ-inverse {_} {x} ⟧ₓ {s} p = +-inverseˡ (⟦ x ⟧ₑ s)