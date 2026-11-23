# Positivity, contraction and the existence boundary: one chain behind Yang-Mills, GRH and P vs NP

*Working title. Draft 1, 2026-11-23. Not a claim of a solution of any Millennium Prize problem. Claim labels (0.n) are listed in
`../CLAIMS.md`.*

## Abstract

Three open problems, the Yang-Mills mass gap, the generalised Riemann hypothesis and P versus NP, are read here as instances of one
chain: a positivity builds a space, the space carries an evolution, and the positivity pins the spectrum of that evolution. The
chain is stated once and proved in its general finite form; much of it is machine-checked in Lean 4 with Mathlib, using only the
standard axioms. The language that names the steps is DMP, a specification for systems of trust, which we use as a vocabulary for
existence; its readings are marked as readings throughout and carry no proof.

**What is proved.** For SU(2) lattice Yang-Mills: reflection positivity, the strict bound between a sector and its twist, a per-box
hand-over rate of at least log(1 + sqrt 2), superadditivity of the carried flux along a chain, and the assembly from a one-box gap
certificate to a mass gap of the lattice theory in both orders of limits. For GRH: Weil's criterion, the Lee-Yang and similitude
mechanisms, and a shared Pringsheim-Landau theorem ("positivity locates singularities"), all in finite models; the same theorem gives
the decay-rate form of the mass gap. For P vs NP: polynomial-time sampling and a spectral gap under Dobrushin's condition, refutation
completeness, Gauss's law mod 2, and the theorem that every refutation of an expanding formula, in every sound proof system with
two-premise rules, contains a line crossing at least the expansion many variables (under two stated graph hypotheses, classical but
not yet formalised).

**What is not proved.** None of the three problems is solved here.

* *Yang-Mills.* The gap mechanism reduces to one statement about one box at one scale: the box's loss rate is below one for every
  well-defined outside. That statement is open. The Clay statement further needs the line of constant physics and non-triviality as
  theorems, Euclidean invariance and reconstruction for a continuum field algebra, and the extension from SU(2) to every compact
  simple group.
* *GRH.* The Riemann hypothesis and GRH for Dirichlet L-functions were proved in Lean by others in November 2026, by a route that
  does not use positivity. This paper follows the positivity route independently. Its open step is a Hilbert space for Weil's form
  built from the primes, the characters and the real place without the zeros, given in five forms. GRH beyond Dirichlet L-functions
  remains open.
* *P vs NP.* Inside a class with a local certificate, search, sampling and counting are polynomial. The crossing from that class to
  all inputs, and super-polynomial lower bounds for Frege proof systems, are open, and any argument for them must pass the
  relativization, natural-proofs and algebrization barriers.

The paper is built so that it closes locally: each open step is stated in the exact form that would close it.

---

## Introduction

### What this paper is

This is a paper about one idea used three times. The idea is old: **positivity is existence**. A positive weight makes a measure; a
positive form makes a Hilbert space; a positive operator has its spectrum where it can be seen. Osterwalder and Schrader built
quantum field theories from reflection positivity. Weil reduced the Riemann hypothesis to the positivity of one pairing. Dobrushin
showed that a contraction of local influences forces a unique equilibrium, reached fast. Each of these is a link in the same chain.

The paper says the chain once (Part II), in its most general form, and derives the three applications from it (Parts III to V). It
introduces the chain through the vocabulary of DMP (Part I), because DMP names the steps that the three problems share: what exists,
what a boundary lets through, what an act leaves behind, and how a system goes from rehearsal to production. Part VI states the one
open step that all three problems share.

### What a reader can take from it

* A reader from **mathematical physics** finds the Yang-Mills mass gap reduced, for SU(2), to a single worst-case statement about one
  box at one scale, with the rest of the gap mechanism machine-checked, and a precise list of what still separates it from the Clay
  statement.
* A reader from **number theory** finds the positivity route to GRH carried to the point where only a construction is missing,
  that construction located by numerics (all primes up to the scale and the real place must enter together, through an exact
  identity), and the shared theorem with Yang-Mills proved.
* A reader from **complexity theory** finds a dictionary in which Dobrushin's condition is a polynomial-time promise class, and a
  transfer of the Yang-Mills dichotomy (local, crossing flux, residue) to refutations, with its exact parts proved and its first
  unclosable step identified.

### How to read the status marks

Every statement carries one mark. **[Lean]**: machine-checked here, standard axioms only, module named. **[classical]**: known, with a
reference. **[external]**: a result by others, read but not rebuilt. **[paper]**: argued here in prose. **[numerical]**: measured here;
it can refute, never prove a for-all statement. **[reading]**: a DMP interpretation, never mathematics. **[open]**: not settled. The
claims ledger (`../CLAIMS.md`) lists every claim with its mark, source and what would upgrade it.

### The three verification layers

The work behind this paper is checked three ways: by proof (on paper and in Lean), by the literature, and by computation. The
computations can refute a statement or guide a proof; they never establish a statement about all cases. Every measured number in the
paper is tied to the statement it would discharge, and a passing measurement is reported as consistent, not as proof.

### What is new

* The Pringsheim-Landau theorem in Lean, with its three instances (Landau's theorem, positive Laplace transforms, the mass gap as the
  bottom of the spectrum) **[Lean]**.
* The hand-over bound: a strict inequality between a sector and its twist forces a rate of at least log(1 + sqrt 2) in one of the two
  dual channels **[Lean]**.
* The reduction of the SU(2) gap mechanism to one box at one scale **[Lean]** + **[classical]**, with the open statement isolated.
* The crossing theorem for every two-premise proof system **[Lean]**.
* The semilocal and prime-by-prime measurements of Weil's form, showing that the missing positivity must be an exact identity
  **[numerical]**.

What is *not* new is listed with references at each use: Osterwalder-Schrader, Weil, Dobrushin, Lee-Yang, Pringsheim and Landau,
Cook-Reckhow, and the barrier theorems.

### Plan

Part I: DMP, the vocabulary. Part II: the chain and the tools. Part III: Yang-Mills. Part IV: GRH. Part V: P vs NP. Part VI: the
common open step.
