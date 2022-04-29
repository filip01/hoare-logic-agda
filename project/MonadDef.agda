open import Level

open import Relation.Binary.PropositionalEquality using (_≡_)

record Monad (l : Level) : Set (suc l) where
    field
        T       : Set l → Set l         -- carrier type
        η       : {X : Set l} → X → T X -- unit
        _>>=_   : {X Y : Set l} → T X → (X → T Y) → T Y -- bind
        -- monad laws
        η-left  : {X Y : Set l} (x : X) (f : X → T Y) → η x >>= f ≡ f x
        η-right : {X : Set l} (c : T X) → c >>= η ≡ c
        >>=-assoc : {X Y Z : Set l} (c : T X) (f : X → T Y) (g : Y → T Z)
            → ((c >>= f) >>= g) ≡ c >>= (λ x → f x >>= g)

    -- the derived operation _>>_ is needed to make Agda do notation work
    _>>_ : {X Y : Set l} → T X → T Y → T Y
    m >> k = ( m >>= λ _ → k)

    -- programers call η return, so we alias it
    return = η