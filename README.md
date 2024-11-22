# Leo-III-lambdapi-lib

This repository contains the encodings of various inference rules and meta-theorems used in the verification of the Higher-Order Logic Automated Theorem Prover (HOL ATP) **Leo-III** [1] within the **Dedukti** framework [2]. The encodings are created using the interactive proof assistant **Lambdapi** [3].

## Included Files

### `extt.lp`
- Encodes the axioms required in addition to the standard library encodings of HOL to represent the extensional type theory used in Leo-III.

### `accessoryRules.lp`
- Encodes accessory rules to handle variations in the output formulas produced by Leo-III due to its implementation.

### `simp.lp`
- Contains basic Boolean identities used as simplification rules in Leo-III.

### `metaTheorems.lp`
- Includes theorems to demonstrate the permissibility of:
  - Permutation of literals.
  - Deletion of duplicate literals.
  - Application of rules operating on individual literals.

### `calcRules.lp`
- Encodes the rules of the calculus **EP** [4], as implemented in Leo-III.

## References and Related Projects
1. [Leo-III: A Higher-Order Logic Automated Theorem Prover](https://github.com/leoprover/Leo-III)  
2. [Dedukti: a Logical Framework based on the λΠ-Calculus Modulo Theory](https://inria.hal.science/hal-04281492/document)  
3. [Lambdapi: An Interactive Proof Assistant for Dedukti](https://github.com/Deducteam/lambdapi)  
4. [Extensional Higher-Order Paramodulation in Leo-III](https://arxiv.org/pdf/1907.11501)

