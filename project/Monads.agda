open import Level        renaming (zero to lzero; suc to lsuc)

open import Data.List
open import Data.Nat
open import Data.Integer using (ℤ)

import Relation.Binary.PropositionalEquality as Eq
open Eq                  using (_≡_; refl; sym; trans; cong; cong₂; subst; [_]; inspect)
open Eq.≡-Reasoning      using (begin_; _≡⟨⟩_; step-≡; _∎)

open import Axiom.Extensionality.Propositional

open import Function     using (id; _∘_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Unit

open import MonadDef

open import Axiom.Extensionality.Propositional using (Extensionality)

module Monads where
    postulate fun-ext : ∀ {a b} → Extensionality a b
    --State = ℕ → ℤ
    module StateTransformer where
        StateT : {l : Level} → (State : Set) → Monad l → Monad l
        StateT {l} S M = record
            { T = λ A → S → T (A × S)
            ; η = λ a s → η (a , s)
            ; _>>=_ = λ m f s → (m s) >>= (λ {(a , s') → f a s'})

            ; η-left = λ a f → 
                begin 
                    (λ s → (η (a , s) >>= (λ { (a , s') → f a s' })))
                ≡⟨ fun-ext (λ s → η-left (a , s) (λ { (a , s') → f a s' })) ⟩
                    f a
                ∎
            ; η-right = λ c → 
                begin
                    (λ s → (c s >>= (λ { (a , s') → η (a , s') })))
                ≡⟨ fun-ext (λ s → η-right (c s)) ⟩
                    c
                ∎
            ; >>=-assoc = λ c f g → 
                begin
                    (λ s → (c s >>= (λ { (a , s') → f a s' })) >>= (λ { (x , y) → g x y}))
                ≡⟨ fun-ext (λ s → >>=-assoc (c s) (λ { (a , s') → f a s' }) λ { (x , y) → g x y })⟩
                    (λ s → c s >>= λ { (a , s') → f a s' >>= λ {(x , y) → g x y} })
                ∎
            }
            where 
                open Monad M

        liftₛₜ : {l : Level} → {A : Set l} → {M : Monad l} → {State : Set}
             → (Monad.T M) A → (Monad.T (StateT State M)) A
        liftₛₜ {M = M} = λ t s → t >>= λ a → η (a , s)
            where open Monad M

    module ListMonad where
        Monad-List : (l : Level) → Monad l
        Monad-List l =
            record
            { T = List
            ; η = _∷ []
            ; _>>=_ = λ xs f → concat (map f xs) -- add deduplicate ?
            ; η-left = λ xs f → ++-identityʳ (f xs)
            ; η-right = concat-[-]
            ; >>=-assoc = λ xs f g →
                    begin
                        concat (map g (concat (map f xs)))
                            ≡⟨ cong concat (sym (concat-map {f = g} (map f xs))) ⟩
                        concat (concat (map (map g) (map f xs)))
                            ≡⟨ cong (concat ∘ concat) (sym (map-∘ (map g) f xs)) ⟩
                        concat (concat (map (map g ∘ f) xs))
                            ≡⟨  sym (concat-concat (map (map g  ∘ f) xs)) ⟩
                        concat (map concat (map (map g ∘ f) xs))
                            ≡⟨  cong concat (sym (map-∘ concat (map g ∘ f) xs))  ⟩
                        concat (map (concat ∘ (map g ∘ f)) xs)
                    ∎
                }
            where
                open import Data.List.Properties

                -- map is functorial
                map-∘ : {X Y Z : Set l} (g : Y → Z) (f : X → Y) (xs : List X) →
                    map (g ∘ f) xs ≡ map g (map f xs)
                map-∘ g f [] = refl
                map-∘ g f (x ∷ xs) = cong (g (f x) ∷_) (map-∘ g f xs)    