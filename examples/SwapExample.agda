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


module SwapExample where
    swap-example : {a b : ℤ}
                 → ⟪ (loc 0 =ₑ int a) ∧ (loc 1 =ₑ int b) ⟫
                   2 ≔ Loc 1 ；
                   (1 ≔ Loc 0 ；
                   0 ≔ Loc 2) 
                   ⟪ (loc 0 =ₑ int b) ∧ (loc 1 =ₑ int a) ⟫
    swap-example {a} {b} = composition 
        (implied {_} {_} {(loc 0 =ₑ int a) ∧ (loc 1 =ₑ int b) ∧ (loc 2 =ₑ int b)}
            (⇒-intro 
                (∧-intro 
                    (∧-elim₁ 
                        (hyp ((loc 0 =ₑ int a) ∧ (loc 1 =ₑ int b)) {{∈-here}})) 
                    (∧-intro 
                        (∧-elim₂ (hyp ((loc 0 =ₑ int a) ∧ (loc 1 =ₑ int b)) {{∈-here}})) 
                        (∧-elim₂ (hyp ((loc 0 =ₑ int a) ∧ (loc 1 =ₑ int b)) {{∈-here}})))))
            (⇒-intro (hyp ((loc 0 =ₑ int a) ∧ (loc 1 =ₑ int b) ∧ (loc 2 =ₑ int b)) {{∈-here}} )) 
            assignment) 
        (composition 
            (implied {_} {_} {(loc 0 =ₑ int a) ∧ (loc 1 =ₑ int a) ∧ (loc 2 =ₑ int b)}
                (⇒-intro 
                    (∧-intro 
                        (∧-elim₁ (((hyp ((loc 0 =ₑ int a) ∧ (loc 1 =ₑ int b) ∧ (loc 2 =ₑ int b)))) {{∈-here}})) 
                        (∧-intro 
                            (∧-elim₁ 
                                ((hyp ((loc 0 =ₑ int a) ∧ (loc 1 =ₑ int b) ∧ (loc 2 =ₑ int b)) {{∈-here}}))) 
                            (∧-elim₂ 
                                (∧-elim₂ 
                                    (hyp ((loc 0 =ₑ int a) ∧ (loc 1 =ₑ int b) ∧ (loc 2 =ₑ int b)) {{∈-here}}))))))
                (⇒-intro (hyp ((loc 0 =ₑ int a) ∧ (loc 1 =ₑ int a) ∧ (loc 2 =ₑ int b)) {{∈-here}})) 
                assignment) 
            (implied {_} {_} {(loc 0 =ₑ int b) ∧ (loc 1 =ₑ int a) ∧ (loc 2 =ₑ int b)}
                (⇒-intro 
                    (∧-intro 
                        (∧-elim₂ 
                            (∧-elim₂ 
                                (hyp ((loc 0 =ₑ int a) ∧ (loc 1 =ₑ int a) ∧ (loc 2 =ₑ int b)) {{∈-here}}))) 
                        (∧-elim₂ 
                            (hyp ((loc 0 =ₑ int a) ∧ (loc 1 =ₑ int a) ∧ (loc 2 =ₑ int b)) {{∈-here}})))) 
                (⇒-intro 
                    (∧-intro 
                        (∧-elim₁ 
                            (hyp ((loc 0 =ₑ int b) ∧ (loc 1 =ₑ int a) ∧ (loc 2 =ₑ int b)) {{∈-here}})) 
                        (∧-elim₁ 
                            (∧-elim₂
                                (hyp ((loc 0 =ₑ int b) ∧ (loc 1 =ₑ int a) ∧ (loc 2 =ₑ int b)) {{∈-here}})))))
                assignment)) 