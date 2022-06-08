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

module ForLoopExample where

-- Useful lemmas.

1-≤ₑ-5 : {Δ : Hypotheses} → Δ ⊢ (int (+ 1) ≤ₑ int (+ 5))
1-≤ₑ-5 = (≤ₑ-trans ≤ₑ-suc
            (=ₑ-subst {_} {λ x → x ≤ₑ int (+ 5)}
            (=ₑ-refl suc-ℤ)
            (≤ₑ-trans ≤ₑ-suc
                (=ₑ-subst {_} {λ x → x ≤ₑ int (+ 5)}
                (=ₑ-refl suc-ℤ)
                (≤ₑ-trans ≤ₑ-suc
                    (=ₑ-subst {_} {λ x → x ≤ₑ int (+ 5)}
                    (=ₑ-refl suc-ℤ)
                    (≤ₑ-trans ≤ₑ-suc
                        (=ₑ-subst {_} {λ x → x ≤ₑ int (+ 5)}
                            (=ₑ-refl suc-ℤ)
                            ≤ₑ-intro))))))))

0-≤ₑ-5 : {Δ : Hypotheses} → Δ ⊢ (int +0 ≤ₑ int (+ 5))
0-≤ₑ-5 = (≤ₑ-trans ≤ₑ-suc
            (=ₑ-subst {_} {λ x → x ≤ₑ int (+ 5)}
            (=ₑ-refl suc-ℤ)
            1-≤ₑ-5))

-- We assume that all formulas are stable.

postulate ¬¬p⇒p : {Δ : Hypotheses} {P : Formula} → Δ ⊢ ¬ (¬ P) ⇒ P

-- Proof that 'loc 1` is never greater then 5 during the for-loop.

for-loop-example :
    ⟪ ⊤ ⟫
        (1 :=ʷ (intʷ (+ 0))) |ʷ
        (forʷ (intʷ (+ 5)) doo
            ((1 :=ʷ ((locʷ 1) +ʷ (intʷ (+ 1)))) |ʷ
            (ifʷ (¬ʷ (locʷ 1 ≤ʷ intʷ (+ 5)))
                then (1 :=ʷ intʷ (+ 1))
                else (passʷ))))
    ⟪ loc 1 ≤ₑ int (+ 5) ⟫ 
for-loop-example = composition
    -- From '1 :=ʷ (intʷ (+ 0))' follows 'loc 1 =ₑ int +0'.
    (implied {[]} {int (+ 0) =ₑ int (+ 0)} {_} {loc 1 =ₑ int (+ 0)}
        (⇒-intro (=ₑ-intro {_} {int (+ 0)}))
        (⇒-intro (hyp (loc 1 =ₑ int +0) {{∈-here}}))
        assignment)
    (implied {[]} {loc 1 ≤ₑ int (+ 5)} {_} {loc 1 ≤ₑ int (+ 5)}
        (⇒-intro
            (=ₑ-subst {_} {λ x → x ≤ₑ int (+ 5)} (=ₑ-refl (hyp (_) {{∈-here}}))
                0-≤ₑ-5))
        (⇒-intro (hyp (_) {{∈-here}}))
        (for-statement
            (composition 
                -- Statement '1 :=ʷ locʷ 1 +ʷ intʷ + 1' is not relevant for the conclusion.
                --  Therfore, we do not need to carry any additional information forward.
                --  (We set the precondition and postcondition to '⊤'.)
                (implied {[]} {⊤} {_} {⊤} (⇒-intro ⊤-intro) (⇒-intro ⊤-intro)
                    assignment)
                (if-statement
                    (implied {[]} {int (+ 1) ≤ₑ int (+ 5)} {_} {loc 1 ≤ₑ int (+ 5)}
                        (⇒-intro 1-≤ₑ-5)
                        (⇒-intro (hyp (_) {{∈-here}}))
                        assignment)
                    (implied {[]} {loc 1 ≤ₑ int (+ 5)} {_} {loc 1 ≤ₑ int (+ 5)}
                        (⇒-intro (⇒-elim (¬¬p⇒p)
                            ((∧-elim₂ (hyp (⊤ ∧ ¬ (¬ (loc 1 ≤ₑ int (+ 5)))) {{∈-here}} )))))
                        (⇒-intro (hyp (_) {{∈-here}}))
                        skip)))))
 