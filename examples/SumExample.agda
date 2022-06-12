open import Data.Nat using (ℕ; _≡ᵇ_)

open import DemonicHoareLogic
open import PQSyntax ℕ 
open import PQDeduction ℕ _≡ᵇ_
open import PQSubstitution ℕ _≡ᵇ_
open import WhileSemantics ℕ
open import WhileSyntax ℕ

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong; cong₂; subst; [_]; inspect)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)

open import Data.List using (List; _∷_; [])

open import Data.Integer renaming (suc to ℤ-suc; pred to ℤ-pred)


module SumExample where

    -- Some useful lemmas

    l-carry-over-int : {Δ : Hypotheses} {x : ℤ} {i : ℤ} →
        Δ ⊢ (int x +ₑ int (ℤ-suc i)) =ₑ int x +ₑ suc (int i)
    l-carry-over-int {_} {x} {i} = 
        =ₑ-subst {_} {int x +ₑ (loc 1) =ₑ int x +ₑ suc (int i)} {1} {_} {int (ℤ-suc i)}
            suc-ℤ
            =ₑ-intro
    
    l-carry-over-int-and-out : {Δ : Hypotheses} {x : ℤ} {i : ℤ} →
        Δ ⊢ (int x +ₑ int (ℤ-suc i)) =ₑ suc (int x +ₑ (int i))
    l-carry-over-int-and-out {_} {x} {i} = =ₑ-trans (l-carry-over-int {_} {x} {i}) +ₚ-carry

    l-eq-add : {Δ : Hypotheses} → {x y z : ℤ} →
        (Δ ⊢ (int x) =ₑ (int y) +ₑ (int z)) →
        (Δ ⊢ ( int (ℤ-suc x)) =ₑ (int y) +ₑ (int (ℤ-suc z)))
    l-eq-add {_} {x} {y} {z} h =
        =ₑ-trans (=ₑ-refl (suc-ℤ {_} {x}))
            (=ₑ-refl (=ₑ-trans (l-carry-over-int-and-out {_} {y} {z})
                    (=ₑ-subst {_} {suc (loc 1) =ₑ suc (int x)} {1} {_} {int y +ₑ int z} h =ₑ-intro)))

    -- Proof that location 1 is equal to 8 after the assignment.
                        
    sum-example : ⟪ ⊥ ⟫ 1 ≔ (Int (+ 5) +' Int (+ 3)) ⟪ loc 1 =ₑ int (+ 8) ⟫
    sum-example = implied
        ((⇒-intro (=ₑ-refl
            ((l-eq-add {_} {+ 7} {+ 5} {+ 2})
             ((l-eq-add {_} {+ 6} {+ 5} {+ 1})
              (l-eq-add {_} {+ 5} {+ 5} {+ 0}
               (=ₑ-refl +ₚ-zero)))))))
        (⇒-intro (hyp (loc 1 =ₑ int (+ 8)) {{∈-here}} ))
        assignment 
 