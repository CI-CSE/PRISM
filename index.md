---
layout: page
---
# Programming really is simple mathematics
PRISM is a novel framework that offers a fresh perspective on programming. Traditionally, key aspects of programming — such as specification and implementation, formal and applied methods, and static and dynamic verification — are often viewed as distinct and even opposing concepts. PRISM challenges this notion by providing a unified, mathematically rigorous foundation that integrates these elements seamlessly.

Currently, the project comprises a [research paper](https://arxiv.org/abs/2502.17149), soon submitted as part of a Festschrift honoring [Yuri Gurevich](https://web.eecs.umich.edu/~gurevich/), along with the [formal proofs](https://github.com/CI-CSE/PRISM/tree/main/Isabelle) of the paper's theorems, developed in [Isabelle HOL](https://isabelle.in.tum.de/). Moving forward, PRISM will continue to be refined and expanded, with the ultimate goal of enabling the generation of formally verified programming languages.

---
## Abstract
A re-construction of the fundamentals of programming as a small mathematical theory
(“PRISM”) based on elementary set theory. Highlights:
- Zero axioms. No properties are assumed, all are proved (from standard set theory).
- A single concept covers specifications and programs.
- Its definition only involves one relation and one set.
- Everything proceeds from three operations: choice, composition and restriction.
- These techniques suffice to derive the axioms of classic papers on the “laws of programming” as consequences and prove them mechanically.
- The ordinary subset operator suffices to define both the notion of program correctness
and the concepts of specialization and refinement.
- From this basis, the theory deduces dozens of theorems characterizing important
properties of programs and programming.
- All these theorems have been mechanically verified (using Isabelle/HOL); the proofs
are available in a public repository.
 
 This paper is a considerable extension and rewrite of an [earlier contribution](https://arxiv.org/abs/1507.00723).