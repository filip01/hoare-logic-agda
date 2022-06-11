open import Monads
open ListMonad
open StateTransformer

open import Level renaming (zero to lzero; suc to lsuc)

open import Data.Nat using (ℕ ; suc) renaming (_<ᵇ_ to _ℕ<ᵇ_)
open import Data.Integer using (ℤ; _+_; +_; _-_; -_; _≤ᵇ_) renaming (∣_∣ to abs)
open import Data.Bool using (Bool; true; false; not; _∧_; _∨_)
open import Data.List using (List; _∷_; []; _++_; map; foldr)
open import Relation.Nullary using (Dec)

open import Data.Unit using (⊤; tt)
open import Data.Product using (_,_; _×_)


--
-- Semantics of WHILE language with state and nondeterminism
--

module WhileSemantics (L : Set) (_==_ : L → L → Bool) where

    open import WhileSyntax L

    -- State
    state = L → ℤ

    -- Monad that captures nondeterminism and state effets.
    NDS-Monad = StateT state (Monad-List lzero)

    -- Interpretation of arithmetic expressions

    infix 4 ⟦_⟧ᵃ

    ⟦_⟧ᵃ : AExprₕ → state → ℤ
    ⟦ Int x ⟧ᵃ Γ = x
    ⟦ Loc l ⟧ᵃ Γ = Γ l
    ⟦ -' a ⟧ᵃ Γ = - (⟦ a ⟧ᵃ Γ)
    ⟦ a₁ +' a₂ ⟧ᵃ Γ = (⟦ a₁ ⟧ᵃ Γ) + (⟦ a₂ ⟧ᵃ Γ) 

    -- Interpretation of Boolean expressions

    infix 5 ⟦_⟧ᵇ

    ⟦_⟧ᵇ : BExprₕ → state → Bool
    ⟦ True ⟧ᵇ _ = true
    ⟦ False ⟧ᵇ _ = false
    ⟦ ¬' b ⟧ᵇ Γ = not (⟦ b ⟧ᵇ Γ)
    ⟦ b₁ ∧' b₂ ⟧ᵇ Γ = ⟦ b₁ ⟧ᵇ Γ ∧ ⟦ b₂ ⟧ᵇ Γ
    ⟦ b₁ ∨' b₂ ⟧ᵇ Γ = ⟦ b₁ ⟧ᵇ Γ ∨ ⟦ b₂ ⟧ᵇ Γ
    ⟦ a₁ ≤' a₂ ⟧ᵇ Γ = (⟦ a₁ ⟧ᵃ Γ) ≤ᵇ (⟦ a₂ ⟧ᵃ Γ)


    open Monad NDS-Monad

    toSt : L → ℤ → state → state
    toSt l a' Γ l' with l == l'
    ... | false = Γ l'
    ... | true = a'

    forDooAux : ℕ → ((Monad.T NDS-Monad) ⊤) → (Monad.T NDS-Monad) ⊤
    forDooAux ℕ.zero c = η tt
    forDooAux (suc n) c = (c >> (forDooAux n c))

    -- Interpretation of commands

    ⟦_⟧ : Cmdₕ → (Monad.T NDS-Monad) ⊤
    ⟦ Skip ⟧ = η tt
    ⟦ c₁ ； c₂ ⟧ = ⟦ c₁ ⟧ >> ⟦ c₂ ⟧
    ⟦ l ≔ a ⟧ s = η tt (toSt l a' s)
        where a' = (⟦ a ⟧ᵃ s)
    ⟦ If b Then c₁ Else c₂ ⟧ s with ⟦ b ⟧ᵇ s
    ... | true = (⟦ c₁ ⟧ s)
    ... | false = (⟦ c₂ ⟧ s)
    ⟦ For a Do c ⟧ s = forDooAux (abs (⟦ a ⟧ᵃ s)) ⟦ c ⟧ s
    ⟦ c₁ Or c₂ ⟧ s = ⟦ c₁ ⟧ s ++ ⟦ c₂ ⟧ s 
