open import Level        renaming (zero to lzero; suc to lsuc)

open import Data.List
open import Data.Nat

import Relation.Binary.PropositionalEquality as Eq
open Eq                  using (_≡_; refl; sym; trans; cong; cong₂; subst; [_]; inspect)
open Eq.≡-Reasoning      using (begin_; _≡⟨⟩_; step-≡; _∎)

open import Function     using (id; _∘_)

module ListMonad where

    record Monad (l : Level) : Set (lsuc l) where
        field
            T       : Set l → Set l         -- carrier type
            η       : {X : Set l} → X → T X -- unit
            _>>=_   : {X Y : Set l} → T X → (X → T Y) → T Y -- bind
            -- monad laws
            η-left  : {X Y : Set l} (x : X) (f : X → T Y) → η x >>= f ≡ f x
            η-right : {X : Set l} (c : T X) → c >>= η ≡ c
            >>=-assoc : {X Y Z : Set l} (c : T X) (f : X → T Y) (g : Y → T Z)
                → ((c >>= f) >>= g) ≡ c >>= (λ x → f x >>= g)

        -- the derived operation _>>_ is needed to make Agda do notation work
        _>>_ : {X Y : Set l} → T X → T Y → T Y
        m >> k = ( m >>= λ _ → k)

        -- programers call η return, so we alias it
        return = η

    Monad-List : (l : Level) → Monad l
    Monad-List l =
        record
        { T = List
        ; η = _∷ []
        ; _>>=_ = λ xs f → concat (map f xs)
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
 

    module _ where

        demo₂ : Monad.T (Monad-List lzero) ℕ
        demo₂ =
            do
                x ← 1 ∷ 2 ∷ 3 ∷ []
                y ← 4 ∷ 5 ∷ []
                return (10 * x + y)
            where open Monad (Monad-List lzero)