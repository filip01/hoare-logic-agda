module WhileSyntax (L : Set) where

open import Data.Nat

infixl 4 -ₚ_
infix 3 Intₚ
infix 3 Locₚ
infixl 5 _+ₚ_

-- Arithemtic expressions
data AExprₚ : Set where
    Intₚ : ℕ → AExprₚ
    Locₚ : L → AExprₚ
    -ₚ_ : AExprₚ → AExprₚ
    _+ₚ_ : AExprₚ → AExprₚ → AExprₚ

test = (Intₚ 10) +ₚ (Intₚ 20)

infixl 4 ¬ₚ_ 
infixl 5 _∧ₚ_
infixl 6 _∨ₚ_

data BExprₚ : Set where
    Trueₚ : BExprₚ
    Falseₚ : BExprₚ
    ¬ₚ_ : BExprₚ → BExprₚ
    _∧ₚ_ : BExprₚ → BExprₚ → BExprₚ
    _∨ₚ_ : BExprₚ → BExprₚ → BExprₚ
    _<ₚ_ : AExprₚ → AExprₚ → BExprₚ

data Cmdₚ : Set where
    Passₚ : Cmdₚ
    _|ₚ_ : Cmdₚ → Cmdₚ → Cmdₚ
    Ifₚ_Then_Else_ : BExprₚ → Cmdₚ → Cmdₚ → Cmdₚ

test' = Passₚ |ₚ Passₚ
test'' = Ifₚ Trueₚ Then Passₚ Else Passₚ

