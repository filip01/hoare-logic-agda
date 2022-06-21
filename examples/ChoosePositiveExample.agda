open import Data.Nat using (ℕ; _≡ᵇ_)

open import AngelicHoareLogic
open import PQSyntax ℕ 
open import PQDeduction ℕ _≡ᵇ_
open import PQSubstitution ℕ _≡ᵇ_
open import WhileSemantics ℕ
open import WhileSyntax ℕ

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong; cong₂; subst; inspect)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)

open import Data.List using (List; _∷_; []; [_]; _++_)

open import Data.Integer renaming (suc to ℤ-suc; pred to ℤ-pred)


module ChoosePositiveExample where
    0≤ₑn : (n : ℕ) → ⊤ ∷ [] ⊢ (int +0 ≤ₑ int (+ n))
    0≤ₑn 0 = ≤ₑ-intro
    0≤ₑn (ℕ.suc n) = 
        ≤ₑ-trans 
            (0≤ₑn n) 
            (=ₑ-subst {_} {int (+ n) ≤ₑ loc 0} {0} 
                suc-ℤ 
                ≤ₑ-suc)

    +a≥0∨-a≥0 : (a : ℤ) → ⊤ ∷ [] ⊢ (int +0 ≤ₑ int a) ∨ (int +0 ≤ₑ (-ₑ int a))
    +a≥0∨-a≥0 (+ n) = ∨-intro₁ (0≤ₑn n)
    +a≥0∨-a≥0 (-[1+_] n) =
        ∨-intro₂ 
            (=ₑ-subst {⊤ ∷ []} {int +0 ≤ₑ loc 0} {0} 
                n⁺=-ₑ-n⁺
                (0≤ₑn (ℕ.suc n)))
        where
            n⁺=-ₑ-n⁺ : ⊤ ∷ [] ⊢ int +[1+ n ] =ₑ -ₑ int -[1+ n ]
            n⁺=-ₑ-n⁺ = =ₑ-subst {_} {int +[1+ n ] =ₑ loc 0} {0} (=ₑ-refl neg-ℤ) (=ₑ-intro)


    or-example : {a : ℤ}
          → ⟪ ⊤ ⟫ 
            0 ≔ Int a Or 0 ≔ (-' (Int a))
            ⟪ int (+ 0) ≤ₑ loc 0 ⟫         -- angelic : a or -a must be a positive number
    
    or-example {a} =
        implied {_} {_} {(int +0 ≤ₑ loc 0)}
            (⇒-intro 
                (+a≥0∨-a≥0 a))
            (⇒-intro 
                (hyp (int (+ 0) ≤ₑ loc 0) {{∈-here}})) 
            (or-statement 
                assignment 
                assignment)  