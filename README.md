# Hoare logic for WHILE language with state and nondeterminism 

This repository contains formalization of *Hoare logic for WHILE language extended with state and nondeterminism* in Agda that was done as part of the course *Logic in computer science* at [Faculty of Mathematics and Physics, University of Ljubljana](https://www.fmf.uni-lj.si/en/) by Filip Marušič and Žiga Putrle.

## The extent of our work

 - We embedded a small imperative programming language (commonly called *WHILE language*) extended with state and nondeterminism; and defined an interpreter for it that models computation as a monad with a carrier type `T 1 = State -> List (1 x State)`.
 - We defined a logic (called *PQ logic*) that can be used to reason about the state of the program and interpret it as a truncated logic `HProp`. 
 - Then, we embedded two variants of Hoare logic for extended WHILE language using PQ logic; one variant assumes angelic, and the other, demonic nondeterminism.
 - At the end, we proved soundness for both variants of the Hoar logic with respect to the interpreter in the partial correctness reading as stated below:
    - (angelic soundness) `⟪ P ⟫ C ⟪ Q ⟫ → ∀ (s : State) → ⟦ P ⟧ s → Σ (s' : State) s' ∈ (⟦ C ⟧ᶜ s) x ⟦ Q ⟧ s'`, and
    - (demonic soundness) `⟪ P ⟫ C ⟪ Q ⟫ → ∀ (s : State) → ⟦ P ⟧ s → ∀ (s' : State) s' ∈ (⟦ C ⟧ᶜ s) x ⟦ Q ⟧ s'` where `P` and `Q` are formulas in PQ logic, `C` is a piece of code written in the extended WHILE language, ⟪ P ⟫ C ⟪ Q ⟫ is Hoare triple and ⟦ _ ⟧ and ⟦ _ ⟧ᶜ present interpretation of a provided term.
    
## Structure of the repository

 - `src/` - directory containing the source code
 - `src/AngelicHoareLogic.agda` - embedding of the Hoare logic with angelic nondeterminism
 - `src/AngelicSoundness.agda` - proof of soundness of the Hoare logic with angelic nondeterminism
 - `src/DemonicHoareLogic.agda` - embedding of the Hoare logic with demonic nondeterminism
 - `src/DemonicSoundness.agda` - proof of soundness of the Hoare logic with demonic nondeterminism
 - `src/HProp.agda` - definition of the universe of propositions
 - `src/Monads.agda` - definition of a monad, state transformer and monad of lists
 - `src/PQDeduction.agda` - definition of deduction rules for PQ logic
 - `src/PQSemantics.agda` - interpretation of PQ logic
 - `src/PQSubstitution.agda` - definition of a substitution for PQ logic
 - `src/PQSyntax.agda` - embedding of PQ logic
 - `src/WhileSemantics.agda` - embedding of the extended WHILE language
 - `src/WhileSyntax.agda` - interpretation of the extended WHILE language
 - `examples/` - directory containig examples of how the Hoare logic can be used
 - `examples/AdditionExample.agda` - example of how we can prove what is the result of a sum of two numbers
 - `examples/ForLoopExample.agda` - example of how we can prove that a value of a location is never greater then some number while performing a for loop

## Getting all the related materials

In order to type-check the code in `src/`, you also need to checkout the `agda-lib` submodule. For the initial checkout of the repository, you can use
    
    git clone --recurse-submodules git@github.com:filip01/hoare-logic-agda.git

## Used literature

- "Logic in Computer Science" by Huth & Ryan
