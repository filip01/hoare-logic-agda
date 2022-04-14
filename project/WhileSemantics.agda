open import Level renaming (zero to lzero; suc to lsuc)

open import Data.Nat using (ℕ ; suc ; _≟_) renaming (_<ᵇ_ to _ℕ<ᵇ_)
open import Data.Integer using (ℤ; _+_; +_; _-_; -_; _≤ᵇ_) renaming (∣_∣ to abs)
open import Data.Bool using (Bool; true; false; not; _∧_; _∨_)
open import Data.List using (List; _∷_; []; _++_; map; foldr)
open import Relation.Nullary using (Dec)


import WhileSyntax

open import ListMonad
open Monad

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

    ⟦_⟧ₐ : AExprₕ → state → ℤ
    ⟦ intₕ x ⟧ₐ Γ = x
    ⟦ locₕ l ⟧ₐ Γ = Γ l
    ⟦ -ₕ a ⟧ₐ Γ = - (⟦ a ⟧ₐ Γ)
    ⟦ a₁ +ₕ a₂ ⟧ₐ Γ = (⟦ a₁ ⟧ₐ Γ) + (⟦ a₂ ⟧ₐ Γ) 

    -- Define how boolean expressions should be interpreted.

    infix 5 ⟦_⟧ₒ

    ⟦_⟧ₒ : BExprₕ → state → Bool
    ⟦ trueₕ ⟧ₒ _ = true
    ⟦ falseₕ ⟧ₒ _ = false
    ⟦ ¬ₕ b ⟧ₒ Γ = not (⟦ b ⟧ₒ Γ)
    ⟦ b₁ ∧ₕ b₂ ⟧ₒ Γ = ⟦ b₁ ⟧ₒ Γ ∧ ⟦ b₂ ⟧ₒ Γ
    ⟦ b₁ ∨ₕ b₂ ⟧ₒ Γ = ⟦ b₁ ⟧ₒ Γ ∨ ⟦ b₂ ⟧ₒ Γ
    ⟦ a₁ ≤ₕ a₂ ⟧ₒ Γ = (⟦ a₁ ⟧ₐ Γ) ≤ᵇ (⟦ a₂ ⟧ₐ Γ)

    bool_expr_test = ⟦ (intₕ (+ 10) ≤ₕ intₕ (+ 9)) ∧ₕ trueₕ ⟧ₒ (λ _ → (+ 0))

    -- TODO: Explain
    forDooAux : ℕ  → Cmdₕ → (state → state) → state → state
    forDooAux ℕ.zero c stm s = s
    forDooAux (suc n) c stm s = forDooAux n c stm (stm s)

    toSt : L → ℤ → state → state
    toSt l a' Γ l' with (Dec.does (l ≟ l'))
    ... | false = Γ l
    ... | true = a'

    -- Define how commands should be interpreted (only state).

    ListMonad = (Monad.T (Monad-List lzero) state)
    
    ⟦_⟧ : Cmdₕ → state → state
    ⟦ passₕ ⟧ Γ = (λ _ → (+ 0))
    ⟦ c₁ |ₕ c₂ ⟧ Γ = ⟦ c₂ ⟧ (⟦ c₁ ⟧ Γ)
    ⟦ l :=ₕ a ⟧ Γ = toSt l (⟦ a ⟧ₐ Γ) Γ
    ⟦ ifₕ b then c₁ else c₂ ⟧ Γ with ⟦ b ⟧ₒ Γ
    ... | false = (⟦ c₂ ⟧ Γ)
    ... | true = (⟦ c₁ ⟧ Γ)
    -- TODO: Change the for loop to "for to do" form.
    ⟦ forₕ a doo c ⟧ Γ = (forDooAux ( abs (⟦ a ⟧ₐ Γ) ) c ⟦ c ⟧ Γ)

    -- ⟦ c₁ orₕ c₂ ⟧ Γ = ⟦ c₁ ⟧ Γ) ++ (⟦ c₂ ⟧ Γ)

    cmd-test = ⟦ (7 :=ₕ intₕ (+ 10)) ⟧ (λ _ → (+ 0))
    cmd-test' = ⟦ 7 :=ₕ intₕ (+ 10) |ₕ 8 :=ₕ ((locₕ 7) +ₕ (intₕ (+ 13))) ⟧ (λ _ → (+ 0)) 8


    -- Define how commands should be interpreted (state + nondeterminism).

    -- ⟦_⟧ : Cmdₕ → state → ListMonad
    -- ⟦ passₕ ⟧ Γ = (λ _ → (+ 0)) ∷ []
    -- ⟦ c₁ |ₕ c₂ ⟧ Γ = foldr _++_ [] (map (λ s → (⟦ c₂ ⟧ s)) (⟦ c₁ ⟧ Γ))
    -- ⟦ l :=ₕ a ⟧ Γ = aux l a' Γ ∷ []
    --     where
    --         a' = (⟦ a ⟧ₐ Γ)
    --         aux : L → ℤ → state → state
    --         aux l a' Γ l' with (Dec.does (l ≟ l'))
    --         ... | false = Γ l
    --         ... | true = a'
    -- ⟦ ifₕ b then c₁ else c₂ ⟧ Γ with ⟦ b ⟧ₒ Γ
    -- ... | false = (⟦ c₂ ⟧ Γ)
    -- ... | true = (⟦ c₁ ⟧ Γ)

    -- -- TODO: Change the for loop to "for to do" form.
    -- ⟦ forₕ a doo c ⟧ Γ = (aux ( abs (⟦ a ⟧ₐ Γ) ) c Γ)
    --     where
    --         aux : ℕ  → Cmdₕ → state → ListMonad
    --         aux ℕ.zero c s = s ∷ []
    --         aux (suc a') c s = foldr _++_ [] (map (λ s' → aux a' c s') (⟦ c ⟧ Γ))

    -- ⟦ c₁ orₕ c₂ ⟧ Γ = (⟦ c₁ ⟧ Γ) ++ (⟦ c₂ ⟧ Γ) 