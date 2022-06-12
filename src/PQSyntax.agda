open import Data.Nat using (ℕ)
open import Data.Integer using (ℤ; +_; _+_) renaming (suc to ℤ-suc)


--
-- Syntax of PQ logic
--
-- PQ logic is a propositional logic extended with basic arithmetic operations.
--

module PQSyntax (L : Set) where

   --
   -- Expressions of propositional logic.
   --
 
   infix 10 int
   infix 10 loc
   infixl 9 suc
   infixl 8 -ₑ_
   infixl 7 _+ₑ_
      
   data Expr : Set where
      int : ℤ → Expr
      loc : L → Expr
      suc : Expr → Expr
      -ₑ_ : Expr → Expr
      _+ₑ_ : Expr → Expr → Expr

   --
   -- Formulae of propositional logic.
   --

   infixr 6 _∧_
   infixr 5 _∨_
   infixr 4 _⇒_
   infix 3 _=ₑ_

   data Formula : Set where
      ⊤   : Formula                        -- truth (unicode \top)
      ⊥   : Formula                        -- falsehood (unicode \bot)
      _∧_ : Formula → Formula → Formula    -- conjunction (unicode \wedge)
      _∨_ : Formula → Formula → Formula    -- disjunction (unicode \vee)
      _⇒_ : Formula → Formula → Formula    -- implication (unicode \=>)
      _=ₑ_ : Expr → Expr → Formula         -- equality
      _≤ₑ_ : Expr → Expr → Formula         -- less than
