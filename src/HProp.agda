open import Data.Product hiding (∃)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]) renaming (map to ⊎-map)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤)

open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Axiom.Extensionality.Propositional using (Extensionality)


--
-- Universe of propositions where propositions are represented as types that only have one element.
--

module HProp where

    postulate fun-ext : ∀ {a b} → Extensionality a b

    -- Propositions are (Set₀) types with at most one inhabitant

    is-proposition : Set → Set
    is-proposition A = (x y : A) → x ≡ y
    
    -- Truncation structure

    postulate
      ∥_∥ : Set → Set
      ∥∥-is-proposition : (A : Set) → is-proposition ∥ A ∥
      ∣_∣ : {A : Set} → A → ∥ A ∥
      ∥∥-elim : {A : Set} {B : Set} → is-proposition B → (A → B) → ∥ A ∥ → B
    
    infix 0 ∥_∥

    -- Computation rule for truncation

    ∥∥-compute : {A : Set} {B : Set}
              → (i : (x y : B) → x ≡ y) (p : A → B) (a : A)
              → ∥∥-elim i p ∣ a ∣ ≡ p a
    ∥∥-compute i p a = i (∥∥-elim i p ∣ a ∣) (p a)

    -- Propositions

    record HProp : Set₁ where
      constructor ⟨_,_⟩
      field
        proof : Set
        is-prop : is-proposition proof

    open HProp public


    -- Logic of propositions

    -- truth

    ⊤ʰ : HProp
    ⊤ʰ = ⟨ ⊤ , (λ _ _ → refl) ⟩

    -- falsehood

    ⊥ʰ : HProp
    ⊥ʰ = ⟨ ⊥ , (λ x y → ⊥-elim x) ⟩

    -- conjunction

    _∧ʰ_ : HProp → HProp → HProp
    ⟨ p , ξ ⟩ ∧ʰ ⟨ q , ζ ⟩ = ⟨ p × q , θ ⟩
      where
        θ : (x y : p × q) → x ≡ y
        θ (x₁ , y₁) (x₂ , y₂) with ξ x₁ x₂ | ζ y₁ y₂
        ... | refl | refl = refl

    ∧ʰ-proj₁ : (a b : HProp) → proof (a ∧ʰ b) → proof (a)
    ∧ʰ-proj₁ _ _ (x , y) = x

    ∧ʰ-proj₂ : (a b : HProp) → proof (a ∧ʰ b) → proof (b)
    ∧ʰ-proj₂ _ _ (x , y) = y

    -- disjunction

    _∨ʰ_ : HProp → HProp → HProp
    ⟨ p , ξ ⟩ ∨ʰ ⟨ q , ζ ⟩ = ⟨ ∥ p ⊎ q ∥ , θ ⟩
      where
        θ : is-proposition ∥ p ⊎ q ∥
        θ = ∥∥-is-proposition _

    ∨ʰ-inj₁ : (a b : HProp) → proof a → proof (a ∨ʰ b)
    ∨ʰ-inj₁ _ _ p = ∣ inj₁ p ∣

    ∨ʰ-inj₂ : (a b : HProp) → proof b → proof (a ∨ʰ b)
    ∨ʰ-inj₂ _ _ p = ∣ inj₂ p ∣

    -- implication

    _⇒ʰ_ : HProp → HProp → HProp
    ⟨ p , ξ ⟩ ⇒ʰ ⟨ q , ζ ⟩ = ⟨ (p → q) , θ ⟩
      where
        θ : is-proposition (p → q)
        θ f g = fun-ext λ x → ζ(f x) (g x)

    -- existential quantification

    ∃ʰ : (A : Set) → (A → HProp) → HProp
    ∃ʰ A ϕ = ⟨ ∥ Σ[ x ∈ A ] proof (ϕ x) ∥ , ∥∥-is-proposition _ ⟩

    -- universal quantification

    ∀ʰ : (A : Set) → (A → HProp) → HProp
    ∀ʰ A ϕ = ⟨ (∀ x → proof (ϕ x)) , (λ f g → fun-ext (λ x → is-prop (ϕ x) (f x) (g x))) ⟩


    -- additional laws

    ∨ʰ-cong : (a b : HProp) → {c d : HProp} → (f : proof a → proof c) → (g : proof b → proof d)
            → proof (a ∨ʰ b) → proof (c ∨ʰ d)
    ∨ʰ-cong a b {c} {d} f g p = ∥∥-elim ((∥∥-is-proposition (proof c ⊎ proof d)))
      (λ { (inj₁ x) → ∣ inj₁ (f x) ∣
        ; (inj₂ y) → ∣ inj₂ (g y) ∣ } ) p

    ∨ʰ-idem : {a : HProp} → proof (a ∨ʰ a) → proof (a)
    ∨ʰ-idem {⟨ proof₁ , is-prop₁ ⟩} p = ∥∥-elim is-prop₁ (λ { (inj₁ x) → x
                                                          ; (inj₂ y) → y }) p

    ∧ʰ-distribˡ : (a b c : HProp) → proof (a ∧ʰ (b ∨ʰ c)) → proof ((a ∧ʰ b) ∨ʰ (a ∧ʰ c))
    ∧ʰ-distribˡ a b c (fst , snd) 
      = ∥∥-elim (∥∥-is-proposition (Σ (proof a) (λ v → proof b) ⊎ Σ (proof a) 
              (λ v → proof c))) (λ { (inj₁ x) → ∣ inj₁ (fst , x) ∣
                                    ; (inj₂ y) → ∣ inj₂ (fst , y) ∣  }) snd 
