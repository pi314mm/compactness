# Coq Formalization of Compactness
This repo uses the Pattern Stepping Bisimulation approach to formally verify the compactness lemma for a language with control flow effects and polymorphism.

The files in the ``EasySubst`` folder represent a substitution framework similar to that of AutoSubst and are based on the formulation given in [Crary's Fully Abstract Module Compilation paper](https://www.cs.cmu.edu/~crary/papers/2018/famc-formal.tgz).

This code provides a good starting point for utilizing the logical relation approach to formalize properties about languages.

The project can be compiled using ``make -f CoqMakefile``.

## Overview of Files

### EasySubst/Sequence.v
Definitions of ``truncate`` and ``index`` operations on lists and associated lemmas.

### EasySubst/Subst.v
Abstractly defines substitution based on a ``traverse`` function. It uses explicit substitutions on De Bruijn indicies. The fact it is defined abstractly makes it great as a substitution framework as an alternative to AutoSubst.

It defines a hint database with several rewrite theorems for simplifying substitutions, which for the most part works well.

### EasySubst/TSubstGeneral.v
This is one of the big advantages this framework has over that of AutoSubst, namely a methodology for reasoning about substitutions $\Gamma'\vdash \sigma : \Gamma$.

This is also defined abstractly so it can be applied to any language.

### SyntaX.v
Definition of the language syntax and the E[e] operation for evaluation contexts. Applies the ``Subst.v`` file substitution definitions to this language.

### Rules.v
The structural operational semantics for the language, along with some lemmas about determinicity and the compositionality of running under evaluation contexts.

### Substitution.v
Builds the substitution theorem for this language by utilizing the methodology given in ``TSubstGeneral.v``. Adds several items to the hint database for substitution, which resolves most things for this language via the simp_sub tactic.

### Safety.v
Progress and Preservation of the language, utilizing the substitution theorem.

### Kleene.v
Definition of termination and mutual termination (Kleene equivalence). Proves a lemma that a particular term does not terminate by utilizing determinicity.

### Compactness.v
Defines a pattern language for verifying the compactness lemma. Defines some helper lemmas associated with ``of`` judgment, dealing with substitution and evaluation contexts.

Then proves generalized compactness via the Pattern Stepping Bisimulation approach, and the standard definition of compactness falls out from this generalized compactness lemma.
