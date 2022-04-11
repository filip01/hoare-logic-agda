open import Data.Integer

module WhileSyntax (L : Set) where

-- Arithemtic expressions

infixl 4 -ₕ_
infix 3 intₕ
infix 3 locₕ
infixl 5 _+ₕ_

data AExprₕ : Set where
    intₕ : ℤ → AExprₕ
    locₕ : L → AExprₕ
    -ₕ_ : AExprₕ → AExprₕ
    _+ₕ_ : AExprₕ → AExprₕ → AExprₕ

test = (intₕ (+ 10)) +ₕ (intₕ (+ 20))

-- Boolean expressions

infixl 4 ¬ₕ_ 
infixl 5 _∧ₕ_
infixl 6 _∨ₕ_

data BExprₕ : Set where
    trueₕ : BExprₕ
    falseₕ : BExprₕ
    ¬ₕ_ : BExprₕ → BExprₕ
    _∧ₕ_ : BExprₕ → BExprₕ → BExprₕ
    _∨ₕ_ : BExprₕ → BExprₕ → BExprₕ
    _≤ₕ_ : AExprₕ → AExprₕ → BExprₕ

-- Commands

infixl 10 _|ₕ_
infixl 11 _:=ₕ_

data Cmdₕ : Set where
    passₕ : Cmdₕ
    _|ₕ_ : Cmdₕ → Cmdₕ → Cmdₕ
    _:=ₕ_ : L → AExprₕ → Cmdₕ
    ifₕ_then_else_ : BExprₕ → Cmdₕ → Cmdₕ → Cmdₕ
    forₕ_doo_ : AExprₕ → Cmdₕ → Cmdₕ
    -- TODO: Add to model nondeterminism.
    -- _orₕ_ : Cmdₕ → Cmdₕ → Cmdₕ  

test' = passₕ |ₕ passₕ
test'' = ifₕ trueₕ then passₕ else passₕ 
