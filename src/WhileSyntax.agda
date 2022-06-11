open import Data.Nat using (ℕ)
open import Data.Integer using (ℤ; +_)


--
-- Syntax of WHILE language with state and nondeterminism
--

module WhileSyntax (L : Set) where

    -- arithmetic expressions

    infixl 10 -'_
    infix 8 Int
    infix 8 Loc
    infixl 5 _+'_

    data AExprₕ : Set where
        Int : ℤ → AExprₕ
        Loc : L → AExprₕ
        -'_ : AExprₕ → AExprₕ
        _+'_ : AExprₕ → AExprₕ → AExprₕ

    -- boolean expressions

    infixl 10 ¬'_
    infixl 5 _∧'_
    infixl 4 _∨'_

    data BExprₕ : Set where
        True : BExprₕ
        False : BExprₕ
        ¬'_ : BExprₕ → BExprₕ
        _∧'_ : BExprₕ → BExprₕ → BExprₕ
        _∨'_ : BExprₕ → BExprₕ → BExprₕ
        _≤'_ : AExprₕ → AExprₕ → BExprₕ

    -- commands

    infix  10 _≔_
    infixl 6 _Or_
    infixl 2 _；_

    data Cmdₕ : Set where
        Skip : Cmdₕ
        _；_ : Cmdₕ → Cmdₕ → Cmdₕ
        _≔_ : L → AExprₕ → Cmdₕ
        If_Then_Else_ : BExprₕ → Cmdₕ → Cmdₕ → Cmdₕ
        For_Do_ : AExprₕ → Cmdₕ → Cmdₕ
        _Or_ : Cmdₕ → Cmdₕ → Cmdₕ  
