{-# OPTIONS --overlapping-instances #-}

{-# OPTIONS --allow-unsolved-metas #-}

module PQSemantics where

{-
   Imports from the standard library.
-}

open import Data.Product

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong; cong₂; subst; inspect) renaming ([_] to [|_|])
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; step-≡˘; _∎)

open import Data.Nat using (ℕ ; suc ; _≟_) renaming (_<ᵇ_ to _ℕ<ᵇ_)
open import Data.Integer using (ℤ; _+_; +_; _-_; -_; _≤ᵇ_) renaming (∣_∣ to abs; _≟_ to _≟ℤ_)
open import Data.Bool

open import Data.Sum
open import Data.Empty renaming (⊥ to ⊥ₜ)
open import Data.Unit

{-
   Importing the deeply embedded propositional logic together with its
   natural dediction proof system, parametrised by location L.
-}

open import HProp
open import WhileSemantics using (⟦_⟧ₐ; L)

import PQDeduction
open module ND = PQDeduction L renaming (⊥ to ⊥ᶠ; ⊥-elim to ⊥-elimᵣ; ⊤ to ⊤ᶠ)

ℙ = HProp   -- unicode \bP

State = L → ℤ

_=ₑₕ_ : ℤ → ℤ → HProp
x =ₑₕ y = ⟨ x ≡ y , (λ {refl refl → refl}) ⟩

_<ₑₕ_ : ℤ → ℤ → HProp
x <ₑₕ y = ⟨ (x ≤ᵇ y) ≡ true , ≤ᵇ≡true-is-prop x y ⟩
   where
      ≤ᵇ≡true-is-prop : (x y : ℤ) → is-proposition ((x ≤ᵇ y) ≡ true)
      ≤ᵇ≡true-is-prop x y p q with x ≤ᵇ y
      ≤ᵇ≡true-is-prop x y refl refl | true = refl
{-
x <ₑₕ y with x ≤ᵇ y
... | b = ⟨ (x ≤ᵇ y) ≡ true , (λ p q → {!   !}) ⟩
-}

{-
   The recursively defined interpretation function for formulae.
-}

⟦_⟧ : Formula → State → ℙ
⟦ ⊤ᶠ ⟧ s = ⊤ʰ
⟦ ⊥ᶠ ⟧ s = ⊥ʰ
⟦ P₁ ∧ P₂ ⟧ S = ⟦ P₁ ⟧ S ∧ʰ ⟦ P₂ ⟧ S
⟦ P₁ ∨ P₂ ⟧ S = ⟦ P₁ ⟧ S ∨ʰ ⟦ P₂ ⟧ S
⟦ P₁ ⇒ P₂ ⟧ S = ⟦ P₁ ⟧ S ⇒ʰ ⟦ P₂ ⟧ S
⟦ x₁ =ₑ x₂ ⟧ S = (⟦ x₁ ⟧ₐ S) =ₑₕ (⟦ x₂ ⟧ₐ S)
⟦ x₁ <ₑ x₂ ⟧ S = (⟦ x₁ ⟧ₐ S) <ₑₕ (⟦ x₂ ⟧ₐ S)

{-
   The interpretation function is also extended to hypotheses.
-}

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

⟦ ⇒-intro {Δ} {φ} {ψ} h ⟧ₓ {s} p 
   = λ x → ⟦ h ⟧ₓ (sym⟦⟧ₕ-++ Δ [ φ ] (p , (x , tt)))

⟦ ⇒-elim {Δ} {φ} {ψ} h₁ h₂ ⟧ₓ {s} p = ⟦ h₁ ⟧ₓ p (⟦ h₂ ⟧ₓ p)

⟦ =ₑ-intro ⟧ₓ {s} p = refl

⟦ =ₑ-refl h ⟧ₓ {s} p = sym (⟦ h ⟧ₓ p)

⟦ =ₑ-trans h₁ h₂ ⟧ₓ {s} p = trans (⟦ h₁ ⟧ₓ p) (⟦ h₂ ⟧ₓ p)

⟦ <ₑ-add {Δ} {x} {y} {z} h ⟧ₓ {s} p = 
   begin
      {!   !}
   ≡⟨ {!   !} ⟩
      {!   !}
   ≡⟨ ⟦ h ⟧ₓ p ⟩
      true
   ∎

⟦ +ₚ-zero {Δ} {x} ⟧ₓ {s} p = {!   !}

⟦ +ₚ-comm ⟧ₓ {s} p = {!   !}
