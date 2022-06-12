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


module AlwaysZeroExample where

    -- Useful lemma

    6-≤ₑ-10 : {Δ : Hypotheses} → Δ ⊢ (int (+ 6) ≤ₑ int (+ 10))
    6-≤ₑ-10 = (≤ₑ-trans ≤ₑ-suc
                (=ₑ-subst {_} {loc 1 ≤ₑ int (+ 10)} {1}
                (=ₑ-refl suc-ℤ)
                (≤ₑ-trans ≤ₑ-suc
                    (=ₑ-subst {_} {loc 1 ≤ₑ int (+ 10)} {1}
                    (=ₑ-refl suc-ℤ)
                    (≤ₑ-trans ≤ₑ-suc
                        (=ₑ-subst {_} {loc 1 ≤ₑ int (+ 10)} {1}
                        (=ₑ-refl suc-ℤ)
                        (≤ₑ-trans ≤ₑ-suc
                            (=ₑ-subst {_} {loc 1 ≤ₑ int (+ 10)} {1}
                                (=ₑ-refl suc-ℤ)
                                ≤ₑ-intro))))))))

    -- We show that a value at location 1 is always 0.

    always-zero-example :
        ⟪ (loc 1 =ₑ int (+ 0)) ∧ (loc 2 =ₑ int (+ 6)) ⟫
            If Loc 2 ≤' Int (+ 10)
                Then (2 ≔ Int (+ 11))
                Else (1 ≔ Int (+ 2) Or 2 ≔ Int (+ 2))
        ⟪ loc 1 =ₑ int (+ 0) ⟫
    always-zero-example = if-statement
        (implied {loc 1 =ₑ int +0} {_} {loc 1 =ₑ int +0} {loc 1 =ₑ int +0}
            (⇒-intro (∧-elim₁ (∧-elim₁
                (hyp (((loc 1 =ₑ int +0) ∧ (loc 2 =ₑ int (+ 6))) ∧ (loc 2 ≤ₑ int (+ 10))) {{∈-here}}))))
            (⇒-intro (hyp (loc 1 =ₑ int +0) {{∈-here}}))
            assignment)
        (implied {⊥} {_} {⊥} {loc 1 =ₑ int +0}
            (⇒-intro
                (⊥-elim
                    (⇒-elim (∧-elim₂
                        (hyp (((loc 1 =ₑ int +0) ∧ (loc 2 =ₑ int (+ 6))) ∧ ((loc 2 ≤ₑ int (+ 10)) ⇒ ⊥))
                            {{∈-here}}))
                    (=ₑ-subst {_} {loc 2 ≤ₑ int (+ 10)} {2}
                        (=ₑ-refl (∧-elim₂ (∧-elim₁ (
                            (hyp (((loc 1 =ₑ int +0) ∧ (loc 2 =ₑ int (+ 6))) ∧ ((loc 2 ≤ₑ int (+ 10)) ⇒ ⊥))
                                {{∈-here}})))))
                        6-≤ₑ-10))))
            (⇒-intro (⊥-elim (hyp (⊥) {{∈-here}})))
            (implied
                (⇒-intro (∧-intro
                    (hyp (⊥) {{∈-here}})
                    (hyp (⊥) {{∈-here}})))
                (⇒-intro (hyp (⊥) {{∈-here}}))
                (or-statement assignment assignment)))     