module Test where

open import Data.Nat

foo : ℕ
foo = 42

open import Level renaming (zero to lzero; suc to lsuc)
open import Categories.Category
open import Categories.Category.Instance.Sets

Sets0 : Category (lsuc lzero) lzero lzero
Sets0 = Sets lzero
