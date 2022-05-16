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

    -- Define a monad that captures nondeterminism and state effets.
    
    NDS-Monad = StateT state (Monad-List lzero)

    -- Define how arithmetic expressions should be interpreted.

    infix 4 ⟦_⟧ₐ

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

    -- Define how commands should be interpreted (state + nondeterminism).

    open Monad NDS-Monad

    -- Useful definitions (need to be externally visible)
    toSt : L → ℤ → state → state
    toSt l a' Γ l' with (Dec.does (l ≟ l'))
    ... | false = Γ l'
    ... | true = a'

    forDooAux : ℕ → ((Monad.T NDS-Monad) ⊤) → (Monad.T NDS-Monad) ⊤
    forDooAux ℕ.zero c = η tt
    forDooAux (suc n) c = (c >> (forDooAux n c))

    ⟦_⟧ : Cmdₕ → (Monad.T NDS-Monad) ⊤
    ⟦ passʷ ⟧ = η tt
    ⟦ c₁ |ʷ c₂ ⟧ = ⟦ c₁ ⟧ >> ⟦ c₂ ⟧
    ⟦ l :=ʷ a ⟧ s = η tt (toSt l a' s)
         where
             a' = (⟦ a ⟧ₐ s)
    ⟦ ifʷ b then c₁ else c₂ ⟧ s with ⟦ b ⟧ₒ s
    ... | true = (⟦ c₁ ⟧ s)
    ... | false = (⟦ c₂ ⟧ s)
    ⟦ forʷ a doo c ⟧ s = forDooAux (abs (⟦ a ⟧ₐ s)) ⟦ c ⟧ s
         where
             aux : ℕ → Cmdₕ → (Monad.T NDS-Monad) ⊤
             aux ℕ.zero c = η tt
             aux (suc n) c = ⟦ c ⟧ >> (aux n c) 
    ⟦ c₁ orʷ c₂ ⟧ s = ⟦ c₁ ⟧ s ++ ⟦ c₂ ⟧ s

    {-
    ⟦ c₁ orʷ c₂ ⟧ s = (⟦ c₁ ⟧ s) >>ᴺᴰ (⟦ c₂ ⟧ s)
        where open Monad (Monad-List lzero) renaming (_>>_ to _>>ᴺᴰ_)
    -} 