# GUID v8: A set theory based approach to the proofing of Yang-Mills, the Generalized Riemann Hypothesis and NP vs coNP, as subsets of DMP, in a DMP-complete state

*Title by the owner (2026-11-23; aspirational by intent). Draft 1. Not a claim of a solution of any Millennium Prize problem. Claim
labels (0.n) are listed in `../CLAIMS.md`. Earlier working title: "Positivity, contraction and the existence boundary: one chain
behind Yang-Mills, GRH and P vs NP".*

## Personal note by the first author

In v1 I invited everyone to use their own intuition to make the derivations which I could see slumbering inside, but which I did not
feel worthy of waking myself. Since no one had any interest in that, I finally got frustrated by it and, after GRH got proven and
certified, I decided to take a look if Yang-Mills is something where I could finally get a nice verification that can't be ignored,
since I previously presumed that DMP also gives YM. One thing led to three, since those three are one, so the initial goal of one
Millennium Problem attempt turned into three :D

I hope I put enough effort into this paper to make it both a worthwhile contribution to science and still get my point across in a
way that tries to spark the needed core intuition in the reader. For follow-up please see GitHub, where everything needed is public
under Apache 2.0.

Have fun with it, and I am always happy about qualified and constructive feedback :)
Steven

(By the way, I also went to Goettingen, but dropped out of my BSc with nearly zero credits after three semesters, though I'll still
count the tie to Riemann in spirit and causality :D
Another by the way: since my going there without graduating satisfies as entanglement over studying at Goettingen as existence, the tie
is constructable and thus exists ;)
In my reading, the zeta function is at heart a pure tool: it needs its subset, and a definition of what it certifies as existence,
before it can be interpreted in a way that produces more insight. Treated as a tool for the true problem, the shared superset, its
meaning becomes apparent and its place in existence slots neatly into a better picture.)

*Editorial notes for the owner (to remove before publication): (1) the Riemann sentence is phrased as your reading; a historical claim
about what Riemann did or did not realize would draw objections, since his 1859 paper introduced the zeta function as a tool for
counting primes. (2) "Goettingen" is transliterated here per the repository rule; the typeset version can use the umlaut.*

## Abstract

Three open problems, the Yang-Mills mass gap, the generalised Riemann hypothesis and P versus NP, are read here as instances of one
chain: a positivity builds a space, the space carries an evolution, and the positivity pins the spectrum of that evolution. The
chain is stated once and proved in its general finite form; much of it is machine-checked in Lean 4 with Mathlib, using only the
standard axioms. The language that names the steps is DMP, a specification for systems of trust, which we use as a vocabulary for
existence; its readings are marked as readings throughout and carry no proof.

**What is proved.** For SU(2) lattice Yang-Mills: reflection positivity, the strict bound between a sector and its twist, a per-box
hand-over rate of at least log(1 + sqrt 2), a forced and unscreenable centre flux obeying the same law on both sides of every box,
superadditivity of the carried flux along a chain, the conversion of a one-box contraction at fixed physical size into a physical mass,
the assembly from a one-box gap certificate to a mass gap of the lattice theory in both orders of limits, and the exact thresholds a
grid of boxes needs beyond a chain (log 8 from column sums, the path entropy log mu_4 from path counting). For GRH: Weil's criterion,
the Lee-Yang and similitude mechanisms and a shared Pringsheim-Landau theorem ("positivity locates singularities"), all in finite
models; that duality without positivity allows zeros off the line; and that positivity cannot be assembled place by place or bounded
by any two separate terms. The same Pringsheim-Landau theorem gives the decay-rate form of the mass gap, and one formal statement ("it
runs") holds the targets of Yang-Mills and GRH side by side. For P vs NP: polynomial-time sampling and a spectral gap under
Dobrushin's condition for finite systems, refutation completeness, Gauss's law mod 2, the DAG-like size-width relation of resolution,
and the theorem that every refutation of an expanding formula, in every sound proof system with two-premise rules, contains a line
crossing at least the expansion many variables (machine-checked under two stated graph hypotheses, which are classical for expanders
but not formalised for concrete graphs); for cutting planes, an exact duality floor for unit-threshold lines and its failure for
weighted lines.

**What is not proved.** None of the three problems is solved here.

* *Yang-Mills.* The gap mechanism reduces to one statement about one box of fixed physical size: its electric flux free energy
  exceeds the path entropy of the four-dimensional lattice, F_e(L) > log mu_4 = 1.91, for every well-defined outside. That statement
  is open; measurements pass it centrally at one coupling but do not certify it. The Clay statement further needs the line of
  constant physics and non-triviality as theorems, Euclidean invariance and reconstruction for a continuum field algebra, and the
  extension from SU(2) to every compact simple group.
* *GRH.* The Riemann hypothesis and GRH for Dirichlet L-functions were proved in Lean by others in November 2026, by a route that
  does not use positivity. This paper follows the positivity route independently and proves no case of GRH. Its open step is one
  positivity built from the primes, the characters and the real place without the zeros, met in eight faces; the measurements show
  it must be an exact identity coupling all primes up to the scale and the real place at once. GRH beyond Dirichlet L-functions
  remains open.
* *P vs NP.* Inside a class with a local certificate, search, sampling and counting are polynomial. The crossing from that class to
  all inputs is open. On the proof-complexity side (NP vs coNP), the sharpest open step located here is a size lower bound for
  cutting planes on random 3-CNF of constant width, which needs a cost measure that no single-line measure provides; super-polynomial
  lower bounds for Frege systems are open. Any argument must pass the relativization, natural-proofs and algebrization barriers.

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

* A reader from **mathematical physics** finds the Yang-Mills mass gap reduced, for SU(2), to a single worst-case number for one box
  of fixed physical size, with the rest of the gap mechanism machine-checked, the reason why a chain of boxes is easy and a grid is
  not, and a precise list of what still separates it from the Clay statement.
* A reader from **number theory** finds the positivity route to GRH carried to the point where only a construction is missing,
  the ways it cannot be assembled proved (place by place, by subsets, by two separate terms), the construction located by numerics
  (all primes up to the scale and the real place must enter together, through an exact identity), and the shared theorems with
  Yang-Mills proved.
* A reader from **complexity theory** finds a dictionary in which Dobrushin's condition is a polynomial-time promise class, a
  transfer of the Yang-Mills dichotomy (local, crossing flux, residue) to refutations with its exact parts proved, and, for cutting
  planes on random 3-CNF, the open step reduced to one missing cost measure.

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
* The reduction of the SU(2) gap mechanism to one box of fixed physical size **[Lean]** + **[classical]**, with the open statement
  isolated as one number, and the thresholds a grid needs beyond a chain **[Lean]**.
* The crossing theorem for every two-premise proof system, and the duality floor and its failure for cutting-planes lines **[Lean]**.
* "It runs": one formal statement holding the Yang-Mills and GRH targets side by side **[Lean]**.
* The semilocal and prime-by-prime measurements of Weil's form, showing that the missing positivity must be an exact identity
  **[numerical]**.

What is *not* new is listed with references at each use: Osterwalder-Schrader, Weil, Dobrushin, Lee-Yang, Pringsheim and Landau,
Cook-Reckhow, and the barrier theorems.

### Plan

Part I: DMP, the vocabulary. Part II: the chain and the tools. Part III: Yang-Mills. Part IV: GRH. Part V: P vs NP. Part VI: the
common open step.
