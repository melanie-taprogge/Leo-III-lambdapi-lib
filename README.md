# Leo-III-lambdapi-lib

This repository contains encodings of various inference rules and meta-theorems used in the verification of the Higher-Order Logic Automated Theorem Prover (HOL ATP) **Leo-III** [1] within the **Dedukti** framework [2]. These encodings are developed with the interactive proof assistant **Lambdapi** [3].

> **Note:**  
> Many encodings that were originally part of this library have been integrated into the Lambdapi **standard library** [4]. This includes axioms for functional and propositional extensionality, along with theorems for simplification, literal transformations, and several list encodings (formerly in `MetaTheorems.lp`).

## Included Files

- **`EPrules.lp`**  
  Encodes the rules of the calculus **EP** [5], as implemented in Leo-III.

- **`MetaTheorems.lp`**  
  Contains theorems allowing operations on literals of a given clause:
  - Permutation of literals.
  - Deletion of duplicate literals.
  - Application of rules on individual literals.

- **`SimpTactic.lp`**  
  Defines a tactic for Lambdapi that exhaustively applies all of Leo-III's simplification rules to terms.

## Dependencies

Some of the encodings rely on features added after the latest stable releases of Lambdapi and the Lambdapi standard library. You must install the latest development versions of both. Please follow the instructions in the respective repositories for:
- [Lambdapi](https://github.com/Deducteam/lambdapi)
- [Lambdapi Standard Library](https://github.com/Deducteam/lambdapi-stdlib)

## Installation from Source

Assuming Lambdapi is already installed, you can install this package by running:
```
make install
```

## Usage

To use these encodings in your Lambdapi files, simply require them as follows:
```
require open Leo-III-lambdapi-lib.EPrules Leo-III-lambdapi-lib.MetaTheorems Leo-III-lambdapi-lib.SimpTactic;
```


## References and Related Projects
1. [Leo-III: A Higher-Order Logic Automated Theorem Prover](https://github.com/leoprover/Leo-III)  
2. [Dedukti: a Logical Framework based on the λΠ-Calculus Modulo Theory](https://inria.hal.science/hal-04281492/document)  
3. [Lambdapi: An Interactive Proof Assistant for Dedukti](https://github.com/Deducteam/lambdapi)
4. [Standard library of Lambdapi](https://github.com/Deducteam/lambdapi-stdlib/tree/master)
5. [Extensional Higher-Order Paramodulation in Leo-III](https://arxiv.org/pdf/1907.11501)

