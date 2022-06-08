open import Data.List using (List; []; _∷_; [_]; _++_)
open import Data.Nat using (ℕ)
open import Data.Integer using (ℤ; +_; _+_) renaming (suc to ℤ-suc)

open import HProp

--
-- PQ logic - Predicate logic extended with basic arithmetic operations.
--

module PQDeduction (L : Set) where
 
   open import WhileSyntax L

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

   data Formula : Set where
      ⊤   : Formula                           -- truth (unicode \top)
      ⊥   : Formula                           -- falsehood (unicode \bot)
      _∧_ : Formula → Formula → Formula       -- conjunction (unicode \wedge)
      _∨_ : Formula → Formula → Formula       -- disjunction (unicode \vee)
      _⇒_ : Formula → Formula → Formula       -- implication (unicode \=>)
      _=ₑ_ : Expr → Expr → Formula         -- equality
      _≤ₑ_ : Expr → Expr → Formula         -- less than

   infixr 6 _∧_
   infixr 5 _∨_
   infixr 4 _⇒_
   infix 3 _=ₑ_

   -- Hypotheses are represented as a list of formulae.

   Hypotheses = List (Formula)

   infix 3 _∈_
   data _∈_ {A : Set} : A → List A → Set where
      instance
         ∈-here  : {x : A} → {xs : List A} → x ∈ (x ∷ xs)
         ∈-there : {x y : A} {xs : List A} → {{x ∈ xs}} → x ∈ (y ∷ xs)
   --
   -- Below is a natural deduction style proof calculus for **intuitionistic**
   --  propositional logic, formalised as an inductive relation.
   --

   infixl 2 _⊢_
   data _⊢_ : (Δ : Hypotheses) → (φ : Formula) → Set where    -- unicode \vdash

      -- structural rules

      weaken   : {Δ₁ Δ₂ : Hypotheses}
               → (φ : Formula)
               → {ψ : Formula}
               → Δ₁ ++ Δ₂ ⊢ ψ
               -----------------------
               → Δ₁ ++ [ φ ] ++ Δ₂ ⊢ ψ

      contract : {Δ₁ Δ₂ : Hypotheses}
               → (φ : Formula)
               → {ψ : Formula}
               → Δ₁ ++ [ φ ] ++ [ φ ] ++ Δ₂ ⊢ ψ
               --------------------------------
               → Δ₁ ++ [ φ ] ++ Δ₂ ⊢ ψ

      exchange : {Δ₁ Δ₂ : Hypotheses}
               → (φ₁ φ₂ : Formula)
               → {ψ : Formula}
               → Δ₁ ++ [ φ₁ ] ++ [ φ₂ ] ++ Δ₂ ⊢ ψ
               -----------------------------------------
               → Δ₁ ++ [ φ₂ ] ++ [ φ₁ ] ++ Δ₂ ⊢ ψ

      -- hypotheses

      hyp      : {Δ : Hypotheses}
               → (φ : Formula)
               → {{φ ∈ Δ}}
               -----------------
               → Δ ⊢ φ

      -- truth

      ⊤-intro  : {Δ : Hypotheses}
               ------------------
               → Δ ⊢ ⊤

      -- falsehood

      ⊥-elim   : {Δ : Hypotheses}
               → {φ : Formula}
               → Δ ⊢ ⊥
               -------------------
               → Δ ⊢ φ

      -- conjunction

      ∧-intro  : {Δ : Hypotheses}
               → {φ ψ : Formula}
               → Δ ⊢ φ
               → Δ ⊢ ψ
               -------------------
               → Δ ⊢ φ ∧ ψ
               
      ∧-elim₁  : {Δ : Hypotheses}
               → {φ ψ : Formula}
               → Δ ⊢ φ ∧ ψ
               -------------------
               → Δ ⊢ φ

      ∧-elim₂  : {Δ : Hypotheses}
               → {φ ψ : Formula}
               → Δ ⊢ φ ∧ ψ
               -------------------
               → Δ ⊢ ψ

      -- disjunction

      ∨-intro₁ : {Δ : Hypotheses}
               → {φ ψ : Formula}
               → Δ ⊢ φ
               ------------------
               → Δ ⊢ φ ∨ ψ

      ∨-intro₂ : {Δ : Hypotheses}
               → {φ ψ : Formula}
               → Δ ⊢ ψ
               -------------------
               → Δ ⊢ φ ∨ ψ

      ∨-elim   : {Δ : Hypotheses}
               → {φ₁ φ₂ ψ : Formula}
               → Δ ⊢ φ₁ ∨ φ₂
               → Δ ++ [ φ₁ ] ⊢ ψ
               → Δ ++ [ φ₂ ] ⊢ ψ
               ---------------------
               → Δ ⊢ ψ

      -- implication

      ⇒-intro  : {Δ : Hypotheses}
               → {φ ψ : Formula}
               → Δ ++ [ φ ] ⊢ ψ
               --------------------
               → Δ ⊢ φ ⇒ ψ

      ⇒-elim   : {Δ : Hypotheses}
               → {φ ψ : Formula}
               → Δ ⊢ φ ⇒ ψ
               → Δ ⊢ φ
               -------------------
               → Δ ⊢ ψ

      -- equality

      =ₑ-intro : {Δ : Hypotheses}
               → {x : Expr}
               ------------------
               → Δ ⊢ x =ₑ x

      =ₑ-refl : {Δ : Hypotheses}
            → {x y : Expr}
            → Δ ⊢ x =ₑ y
            -----------------
            → Δ ⊢ y =ₑ x

      =ₑ-trans : {Δ : Hypotheses}
               → {x y z : Expr}
               → Δ ⊢ x =ₑ y
               → Δ ⊢ y =ₑ z
               -----------------
               → Δ ⊢ x =ₑ z 

      =ₑ-cong : {Δ : Hypotheses}
            → (f : Expr → Expr)
            → {x y : Expr}
            → Δ ⊢ x =ₑ y
            -----------------
            → Δ ⊢ f x =ₑ f y
      
      =ₑ-subst : {Δ : Hypotheses}
            → {P : Expr → Formula}
            → {x y : Expr}
            → Δ ⊢ x =ₑ y
            → Δ ⊢ P x
            -----------------
            → Δ ⊢ P y

      -- successor

      suc-ℤ : {Δ : Hypotheses}
            → {i : ℤ}
            ------------------------
            → Δ ⊢ suc (int i) =ₑ int (ℤ-suc i)

      -- addition

      ≤ₑ-intro : {Δ : Hypotheses}
            → {x : Expr}
            --------------------------
            → Δ ⊢ x ≤ₑ x

      ≤ₑ-suc : {Δ : Hypotheses}
            → {x : Expr}
            --------------------------
            → Δ ⊢ x ≤ₑ (suc x)

      ≤ₑ-trans : {Δ : Hypotheses}
            → {x y z : Expr}
            → Δ ⊢ x ≤ₑ y
            → Δ ⊢ y ≤ₑ z
            -----------------
            → Δ ⊢ x ≤ₑ z 

      ≤ₑ-add : {Δ : Hypotheses}
            → {x y z : Expr}
            → Δ ⊢ x ≤ₑ y
            --------------------------
            → Δ ⊢ (x +ₑ z) ≤ₑ (y +ₑ z)

      +ₚ-zero : {Δ : Hypotheses}
            → {x : Expr}
            ------------------------
            → Δ ⊢ x +ₑ (int (+ 0)) =ₑ x

      +ₚ-carry : {Δ : Hypotheses}
            → {x y : Expr}
            ------------------------
            → Δ ⊢ x +ₑ suc y =ₑ suc (x +ₑ y)

      +ₚ-comm : {Δ : Hypotheses}
            → {x y : Expr}
            ----------------------
            → Δ ⊢ x +ₑ y =ₑ y +ₑ x

   -- We define negation and logical equivalence as syntactic sugar.
   -- These definitions are standard logical encodings of `¬` and `⇔`.

   ¬_ : Formula → Formula              -- unicode \neg
   ¬ φ = φ ⇒ ⊥

   _⇔_ : Formula → Formula → Formula    -- unicode \<=>
   φ ⇔ ψ = (φ ⇒ ψ) ∧ (ψ ⇒ φ)

   infix 7 ¬_
   infix 3 _⇔_

   ¬-intro : {Δ : Hypotheses}
         → {φ : Formula}
         → Δ ++ [ φ ] ⊢ ⊥
         → Δ ⊢ ¬ φ

   ¬-intro d = ⇒-intro d

   ¬-elim : {Δ : Hypotheses}
         → {φ : Formula}
         → Δ ⊢ φ
         → Δ ⊢ ¬ φ
         → Δ ⊢ ⊥

   ¬-elim d₁ d₂ = ⇒-elim d₂ d₁

   cut-derivable : {Δ : Hypotheses}
               → {φ ψ : Formula}
               → Δ ⊢ φ
               → Δ ++ [ φ ] ⊢ ψ
               ------------------
               → Δ ⊢ ψ

   cut-derivable d₁ d₂ = ⇒-elim (⇒-intro d₂) d₁  
  