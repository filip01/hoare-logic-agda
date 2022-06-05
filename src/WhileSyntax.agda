open import Data.Integer using (ℤ; +_)

--
-- Syntax of a WHILE language with state and nondeterminism
--

module WhileSyntax (L : Set) where

    -- arithmetic expressions

    infixl 4 -ʷ_
    infix 3 intʷ
    infix 3 locʷ
    infixl 5 _+ʷ_

    data AExprₕ : Set where
        intʷ : ℤ → AExprₕ
        locʷ : L → AExprₕ
        -ʷ_ : AExprₕ → AExprₕ
        _+ʷ_ : AExprₕ → AExprₕ → AExprₕ

    -- boolean expressions

    infixl 4 ¬ʷ_
    infixl 5 _∧ʷ_
    infixl 6 _∨ʷ_
    -- ∨ʷ

    data BExprₕ : Set where
        trueʷ : BExprₕ
        falseʷ : BExprₕ
        ¬ʷ_ : BExprₕ → BExprₕ
        _∧ʷ_ : BExprₕ → BExprₕ → BExprₕ
        _∨ʷ_ : BExprₕ → BExprₕ → BExprₕ
        _≤ʷ_ : AExprₕ → AExprₕ → BExprₕ

    -- commands

    infixl 10 _|ʷ_
    infixl 11 _:=ʷ_

    data Cmdₕ : Set where
        passʷ : Cmdₕ
        _|ʷ_ : Cmdₕ → Cmdₕ → Cmdₕ
        _:=ʷ_ : L → AExprₕ → Cmdₕ
        ifʷ_then_else_ : BExprₕ → Cmdₕ → Cmdₕ → Cmdₕ
        forʷ_doo_ : AExprₕ → Cmdₕ → Cmdₕ
        _orʷ_ : Cmdₕ → Cmdₕ → Cmdₕ  
