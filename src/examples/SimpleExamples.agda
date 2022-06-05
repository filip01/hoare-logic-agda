import DemonicHoareLogic
open DemonicHoareLogic.WhileSyntaxNat
open DemonicHoareLogic.PQDeductionNat hiding (_∈_)
open DemonicHoareLogic using (⟪_⟫_⟪_⟫)
open DemonicHoareLogic.⟪_⟫_⟪_⟫

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong; cong₂; subst; [_]; inspect)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)


open import Data.Integer

module SimpleExamples where

    assignment' : ⟪ intʷ (+ 0) =ₑ (intʷ (+ 0)) ⟫ 1 :=ʷ (intʷ (+ 0)) ⟪ locʷ 1 =ₑ (intʷ (+ 0)) ⟫
    assignment' = assignment

    addition₁ : ⟪ (intʷ (+ 8)) =ₑ intʷ (+ 8) ⟫ 1 :=ʷ (intʷ (+ 3) +ʷ intʷ (+ 5)) ⟪ locʷ 1 =ₑ intʷ (+ 8) ⟫
    addition₁ = implied {_}
            {(intʷ (+ 3) +ʷ intʷ (+ 5)) =ₑ intʷ (+ 8) } {(intʷ (+ 8)) =ₑ intʷ (+ 8)}
            {locʷ 1 =ₑ intʷ (+ 8)} {locʷ 1 =ₑ intʷ (+ 8)}
        (⇒-intro
            (=ₑ-trans +ₚ-carry-out (=ₑ-trans +ₚ-comm (=ₑ-trans {! +ₚ-is-suc   !} {!   !}))))
        (⇒-intro (hyp (locʷ 1 =ₑ intʷ (+ 8)) {{∈-here}} ))
        assignment
    
    lemma : (intʷ (+ 3) +ʷ intʷ (+ 5)) ≡ (intʷ (+ 8))
    lemma = {!   !} 