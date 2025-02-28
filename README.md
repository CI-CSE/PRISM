PRISM
===
>Programming really is simple mathematics.

This contains of some [Eiffel][eif] implementation and Isabelle proofs for [PRISM][pm_web]. The eiffel code is work in progress the isabelle files too but the theory is synchronized with the [research paper][pm_pap]. All definitions and claims have the same name in the isabelle files as they have in the reasearch paper.

Prerequisite
---
Default [Isabelle2024][isa] installation

How to use
---
### Validate the proofs:
1. Download this repository.
1. And open the `PRISM.thy` file.
1. In the *Theories* tab you see the progress of the validation.

### Find proof
Use your prefered search engine for looking through multiple files or just search here on GitHub.

### Prove a new claim

First state the claim at the end of `PRISM.thy` e.g. `theorem "(p;q);r=p;(q;r)"`
   - If the system tells you "`Auto solve_direct: the current goal can be solved directly with...`" in which case we already proved the property.
   - Else you can ask *Sledgehammer* to solve it and it will produce something like `cvc4 found a proof... Try this: by simp`
   - If Sledgehammer does not find a proof you have to learn a bit of [Isabelle][isa_tut] and prove it manually.


[pm_web]: https://se.constructor.ch/PRISM/
[pm_pap]: https://arxiv.org/abs/2502.17149
[eif]: https://www.eiffel.com/
[isa]: https://isabelle.in.tum.de/
[isa_tut]: https://isabelle.in.tum.de/documentation.html
