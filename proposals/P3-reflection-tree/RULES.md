# Proposed contest rules: Lean edition

These adapt the constructive contest at
https://github.com/codyroux/name-the-biggest-number
(commit d56dce013e6264292533efdc5e1de71863c6fb86)
by replacing Coq with Lean.

1. **A constructive natural number.** Supply a closed executable Lean declaration
   whose type is Nat. Its definition must compute a finite natural in principle.
   There is no requirement to print or evaluate that natural within the checking
   time. A halting oracle or Busy Beaver definition is not allowed.

2. **A formal improvement.** Supply a Lean theorem that the previous contender is
   strictly less than the new one. The comparison must refer to the actual
   previous contender, or to a faithfully ported definition whose source
   correspondence is explicitly documented when changing proof assistants.

3. **Fixed proof-assistant release.** This submission uses Lean 4.19.0. State and
   pin the release so that definitions and proofs can be checked reproducibly.
   The standard Init library is allowed; this entry requires no Mathlib.

4. **No axiom dependencies.** The number and all comparison results must have
   empty transitive axiom lists under Lean's #print axioms audit. This includes
   avoiding Classical.choice, propext, Quot.sound, sorryAx, and custom axioms.
   Admit, sorry, partial, unsafe, noncomputable definitions, and native_decide
   are excluded from the submitted source in this package.

5. **Checking budgets.** From fresh project object files, checking the definition
   and its required project definitions must take at most 15 seconds. Checking
   the comparison and its proof dependencies must take at most 60 seconds.
   The ordinary standard-library objects may be preinstalled. Record compiler,
   machine environment, and wall times. The supplied harness conservatively
   includes auxiliary proofs, small examples, and two audits in the proof budget.

6. **Substantive improvement.** Do not define the entry by using the previous
   contender's winning constant, directly or through a renamed helper, and
   applying a routine operation to it. Reusing uniform syntax and interpretation
   infrastructure is permitted. Document the new construction and its compiled
   constant dependencies.

7. **Reproducible source.** Supply the complete definitions, proofs, commands,
   and relevant provenance. Clearly distinguish kernel-checked theorems from
   external audits and mathematical motivations.

The included contender_6 satisfies these proposed rules on the recorded
checking environment. Its definition check took 1.404626 seconds and its
proofs, examples, and audits took 2.741057 seconds. Hardware-independent
running-time guarantees and global optimality among all valid entries are
not claimed.
