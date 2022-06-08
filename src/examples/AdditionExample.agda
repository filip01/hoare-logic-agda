import DemonicHoareLogic
open DemonicHoareLogic.WhileSyntaxNat
open DemonicHoareLogic.PQDeductionNat hiding (_∈_)
open DemonicHoareLogic using (⟪_⟫_⟪_⟫)
open DemonicHoareLogic.⟪_⟫_⟪_⟫

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong; cong₂; subst; [_]; inspect)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)

open import Data.List using (List; _∷_; [])

open import Data.Integer renaming (suc to ℤ-suc; pred to ℤ-pred)

module AdditionExample where

    l-carry-over : {Δ : Hypotheses} {e : Expr} {i : ℤ} →
        Δ ⊢ (e +ₑ int (ℤ-suc i)) =ₑ e +ₑ suc (int i)
    l-carry-over {_} {e} = =ₑ-cong ((_+ₑ_ e)) (=ₑ-refl suc-ℤ)
    
    l-carry-over' : {Δ : Hypotheses} {e : Expr} {i : ℤ} →
        Δ ⊢ (e +ₑ int (ℤ-suc i)) =ₑ suc (e +ₑ (int i))
    l-carry-over' {_} {e} {i} = =ₑ-trans (l-carry-over {_} {e} {i}) +ₚ-carry

    l-eq-add : {Δ : Hypotheses} → {x y z : ℤ} →
        (Δ ⊢ (int x) =ₑ (int y) +ₑ (int z)) →
        (Δ ⊢ ( int (ℤ-suc x)) =ₑ (int y) +ₑ (int (ℤ-suc z)))
    l-eq-add {_} {x} {y} {z} h =
        =ₑ-trans (=ₑ-refl (suc-ℤ {_} {x}))
            (=ₑ-refl (=ₑ-trans (l-carry-over' {_} {int y} {z})
                (=ₑ-cong suc (=ₑ-refl h))))
    
    addition-examples : ⟪ (int (+ 8)) =ₑ int (+ 8) ⟫ 1 :=ʷ (intʷ (+ 5) +ʷ intʷ (+ 3)) ⟪ loc 1 =ₑ int (+ 8) ⟫
    addition-examples = implied {[]}
        ((⇒-intro (=ₑ-refl
            ((l-eq-add {_} {+ 7} {+ 5} {+ 2})
             ((l-eq-add {_} {+ 6} {+ 5} {+ 1})
              (l-eq-add {_} {+ 5} {+ 5} {+ 0}
               (=ₑ-refl +ₚ-zero)))))))
        (⇒-intro (hyp (loc 1 =ₑ int (+ 8)) {{∈-here}} ))
        assignment 