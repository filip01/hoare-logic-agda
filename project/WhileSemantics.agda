open import Level renaming (zero to lzero; suc to lsuc)

open import Data.Nat using (ℕ ; suc ; _≟_) renaming (_<ᵇ_ to _ℕ<ᵇ_)
open import Data.Integer using (ℤ; _+_; +_; _-_; -_; _≤ᵇ_) renaming (∣_∣ to abs)
open import Data.Bool using (Bool; true; false; not; _∧_; _∨_)
open import Data.List using (List; _∷_; []; _++_; map; foldr)
open import Relation.Nullary using (Dec)

open import Data.Unit using (⊤; tt)
open import Data.Product using (_,_; _×_)

import WhileSyntax

open import MonadDef
open import Monads
open ListMonad
open StateTransformer

open import Agda.Builtin.Maybe

module WhileSemantics where


    -- Define location type
    L = ℕ

    -- Introduce WHILE syntax that uses natural numbers as location.
    module WhileSyntaxNat = WhileSyntax L

    open WhileSyntaxNat

    -- Define state
    state = L → ℤ

    -- TODO: Value of all the locaitons might not be defined.

    -- Define how arithmetic expressions should be interpreted.

    infix 4 ⟦_⟧ₐ

    NDS-Monad = StateT state (Monad-List lzero)



    ⟦_⟧ₐ : AExprₕ → state → ℤ
    ⟦ intʷ x ⟧ₐ Γ = x
    ⟦ locʷ l ⟧ₐ Γ = Γ l
    ⟦ -ʷ a ⟧ₐ Γ = - (⟦ a ⟧ₐ Γ)
    ⟦ a₁ +ʷ a₂ ⟧ₐ Γ = (⟦ a₁ ⟧ₐ Γ) + (⟦ a₂ ⟧ₐ Γ) 

    -- Define how boolean expressions should be interpreted.

    infix 5 ⟦_⟧ₒ

    ⟦_⟧ₒ : BExprₕ → state → Bool
    ⟦ trueʷ ⟧ₒ _ = true
    ⟦ falseʷ ⟧ₒ _ = false
    ⟦ ¬ʷ b ⟧ₒ Γ = not (⟦ b ⟧ₒ Γ)
    ⟦ b₁ ∧ʷ b₂ ⟧ₒ Γ = ⟦ b₁ ⟧ₒ Γ ∧ ⟦ b₂ ⟧ₒ Γ
    ⟦ b₁ ∨ʷ b₂ ⟧ₒ Γ = ⟦ b₁ ⟧ₒ Γ ∨ ⟦ b₂ ⟧ₒ Γ
    ⟦ a₁ ≤ʷ a₂ ⟧ₒ Γ = (⟦ a₁ ⟧ₐ Γ) ≤ᵇ (⟦ a₂ ⟧ₐ Γ)

    bool_expr_test = ⟦ (intʷ (+ 10) ≤ʷ intʷ (+ 9)) ∧ʷ trueʷ ⟧ₒ (λ _ → (+ 0))


    -- TODO: Explain
    forDooAux : ℕ  → Cmdₕ → (state → state) → state → state
    forDooAux ℕ.zero c stm s = s
    forDooAux (suc n) c stm s = forDooAux n c stm (stm s)

    toSt : L → ℤ → state → state
    toSt l a' Γ l' with (Dec.does (l ≟ l'))
    ... | false = Γ l'
    ... | true = a'
{-
    -- Define how commands should be interpreted (only state).

    ListMonad = (Monad.T (Monad-List lzero) state)
    
    ⟦_⟧ : Cmdₕ → state → state
    ⟦ passʷ ⟧ Γ = (λ _ → (+ 0))
    ⟦ c₁ |ʷ c₂ ⟧ Γ = ⟦ c₂ ⟧ (⟦ c₁ ⟧ Γ)
    ⟦ l :=ʷ a ⟧ Γ = toSt l (⟦ a ⟧ₐ Γ) Γ
    ⟦ ifʷ b then c₁ else c₂ ⟧ Γ with ⟦ b ⟧ₒ Γ
    ... | false = (⟦ c₂ ⟧ Γ)
    ... | true = (⟦ c₁ ⟧ Γ)
    -- TODO: Change the for loop to "for to do" form.
    ⟦ forʷ a doo c ⟧ Γ = (forDooAux ( abs (⟦ a ⟧ₐ Γ) ) c ⟦ c ⟧ Γ)

    -- (⟦ c₁ orʷ c₂ ⟧ Γ = ⟦ c₁ ⟧ Γ) ++ (⟦ c₂ ⟧ Γ)

    cmd-test = ⟦ (7 :=ʷ intʷ (+ 10)) ⟧ (λ _ → (+ 0))
    cmd-test' = ⟦ 7 :=ʷ intʷ (+ 10) |ʷ 8 :=ʷ ((locʷ 7) +ʷ (intʷ (+ 13))) ⟧ (λ _ → (+ 0)) 8

-}

    -- Define how commands should be interpreted (state + nondeterminism).

    open Monad NDS-Monad

    ⟦_⟧ : Cmdₕ → (Monad.T NDS-Monad) ⊤
    ⟦ passʷ ⟧ = η tt
    ⟦ c₁ |ʷ c₂ ⟧ = ⟦ c₁ ⟧ >> ⟦ c₂ ⟧
    ⟦ l :=ʷ a ⟧ s = η tt (aux l a' s)
         where
             a' = (⟦ a ⟧ₐ s)
             aux : L → ℤ → state → state
             aux l a' Γ l' with (Dec.does (l ≟ l'))
             ... | false = Γ l
             ... | true = a'
    ⟦ ifʷ b then c₁ else c₂ ⟧ s with ⟦ b ⟧ₒ s
    ... | true = (⟦ c₁ ⟧ s)
    ... | false = (⟦ c₂ ⟧ s)
    ⟦ forʷ a doo c ⟧ s = aux (abs (⟦ a ⟧ₐ s)) c s
         where
             aux : ℕ → Cmdₕ → (Monad.T NDS-Monad) ⊤
             aux ℕ.zero c = η tt
             aux (suc n) c = ⟦ c ⟧ >> (aux n c) 
    ⟦ c₁ orʷ c₂ ⟧ s = ⟦ c₁ ⟧ s ++ ⟦ c₂ ⟧ s
    {-
    ⟦ c₁ orʷ c₂ ⟧ s = (⟦ c₁ ⟧ s) >>ᴺᴰ (⟦ c₂ ⟧ s)
        where open Monad (Monad-List lzero) renaming (_>>_ to _>>ᴺᴰ_)
    -}

    -- ⟦_⟧ : Cmdₕ → state → ListMonad
    -- ⟦ passʷ ⟧ Γ = (λ _ → (+ 0)) ∷ []
    -- ⟦ c₁ |ʷ c₂ ⟧ Γ = foldr _++_ [] (map (λ s → (⟦ c₂ ⟧ s)) (⟦ c₁ ⟧ Γ))
    -- ⟦ l :=ʷ a ⟧ Γ = aux l a' Γ ∷ []
    --     where
    --         a' = (⟦ a ⟧ₐ Γ)
    --         aux : L → ℤ → state → state
    --         aux l a' Γ l' with (Dec.does (l ≟ l'))
    --         ... | false = Γ l
    --         ... | true = a'
    -- ⟦ ifʷ b then c₁ else c₂ ⟧ Γ with ⟦ b ⟧ₒ Γ
    -- ... | false = (⟦ c₂ ⟧ Γ)
    -- ... | true = (⟦ c₁ ⟧ Γ)

    -- -- TODO: Change the for loop to "for to do" form.
    -- ⟦ forʷ a doo c ⟧ Γ = (aux ( abs (⟦ a ⟧ₐ Γ) ) c Γ)
    --     where
    --         aux : ℕ  → Cmdₕ → state → ListMonad
    --         aux ℕ.zero c s = s ∷ []
    --         aux (suc a') c s = foldr _++_ [] (map (λ s' → aux a' c s') (⟦ c ⟧ Γ))

    -- ⟦ c₁ orʷ c₂ ⟧ Γ = (⟦ c₁ ⟧ Γ) ++ (⟦ c₂ ⟧ Γ)   