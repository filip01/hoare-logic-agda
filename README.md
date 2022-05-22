# Hoare logic for WHILE language with state and nondeterminism 

This repository contains formalization of *Hoare logic for WHILE language extended with state and nondeterminism* in Agda that was done as part of the course *Logic in computer science* at [Faculty of Mathematics and Physics, University of Ljubljana](https://www.fmf.uni-lj.si/en/) by Filip Marušič and Žiga Putrle.

## The extent of our work

 - We embedded a small imperative programming language (commonly called WHILE language) extended with state and nondeterminism.
 - Defined an interpreter for the extended WHILE language.
 - Embedded a logic (called *PQ logic*) that can be used to reason about the state of the program.
 - Embedded two variants of Hoare logic for extended WHILE language based upon PQ logic; one variant assumed angelic, and the other, demonic nondeterminism.
 - Proved soundness for both variants of the Hoar logic with respect to the interpreter in the partial correctness reading.

## Structure of the repository

 - `src/` - directory containing the source code
 - `src/AngelicHoareLogic.agda` - embedding of the Hoare logic with angelic nondeterminism
 - `src/AngelicSoundness.agda` - proof of soundness of the Hoare logic with angelic nondeterminism
 - `src/DemonicHoareLogic.agda` - embedding of the Hoare logic with demonic nondeterminism
 - `src/DemonicSoundness.agda` - proof of soundness of the Hoare logic with demonic nondeterminism
 - `src/HProp.agda` - definition of the universe of propositions
 - `src/Monads.agda` - definition of a monad, state transformer and monad of lists
 - `src/PQDeduction.agda` - embedding of PQ logic
 - `src/PQSemantics.agda` - interpretation of PQ logic
 - `src/PQSubstitution.agda` - definition of a substitution used in the interpretation of PQ logic
 - `src/WhileSemantics.agda` - embedding of the extended WHILE language
 - `src/WhileSyntax.agda` - interpretation of the extended WHILE language

## Getting all the related materials

In order to type-check the code in `src/`, you also need to checkout the `agda-lib` submodule. For the initial checkout of the repository, you can use
    
    git clone --recurse-submodules git@github.com:filip01/hoare-logic-agda.git
