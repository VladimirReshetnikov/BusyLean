# Validation boundary

## Established in the packaging environment

- The BusyLean baseline was inspected at commit
  `4c4b03d0e2003c479e3bee90a21c8bea13f66c40`.
- The current repository winner at that revision is Contender 10.
- The candidate definition and proof sources pass the supplied static audit:
  forbidden escape-hatch tokens are absent, delimiters are balanced, all
  advertised declarations are present, and the executable definition does not
  reference the named scalar `contender_10`.
- The independent finite reference model passed 670 assertions, including a
  dense test of the 2-adic family code and the strict crown/forest inequalities.
- The LaTeX article was compiled and the rendered PDF was inspected.

## Not established here

The environment did not contain `lake` or Lean 4.34.0, and outbound binary
installation was unavailable.  Therefore this package does **not** claim:

- successful Lean elaboration or kernel checking;
- a completed `#print axioms` audit;
- transitive dependency-closure success inside Lean;
- compliance with the 15-second and 60-second contest budgets.

The exact commands and an automated checker are included so these obligations
can be discharged in a pinned BusyLean checkout.  Until that run succeeds, the
entry is a serious formalization proposal, not an accepted certified contender.

## Mathematical versus implementation confidence

The comparison argument is elementary once the inherited BusyLean lemmas are
available: every reflector exceeds its visible children; the old self-generated
index contains a leaf through a two-edge path; each crown edge is a visible
child edge; and every stage exceeds its input.  The principal residual risk is
Lean elaboration at definitional-equality boundaries, not the paper inequality.
