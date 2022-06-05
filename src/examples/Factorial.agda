open import DemonicHoareLogic
open import WhileSyntax
open import PQDeduction

open import Data.Integer

module Factorial where

    factorial :
        ⟪ locʷ 1 =ₑ intʷ (+ 3) ⟫
            1 :=ʷ intʷ (+ 0)
        ⟪ locʷ 2 =ₑ intʷ (+ 3) +ʷ intʷ (+ 2) +ʷ intʷ (+ 1)  ⟫
    factorial = {!   !}