# Provenance and research status

This bundle was prepared against the public BusyLean repository at commit
`86b360648163f0249eab79539438b6a83dfe8215`.

Repository facts used in the design:

- Contender 6 is `stage p5Family index 42`.
- `stage` is forest reflection over oracle families along `WTree Nat`.
- `index` joins every W-tree denoted by a finite-depth program enumeration.
- the repository warns that reflection is not monotone in its oracle;
  comparisons must use explicit occurrences.
- the repository's informal calibration places the W-language near
  `psi(Omega_omega)` and Contender 6 near the square of that scale.

Original contribution in this bundle:

- lift from oracle families to family transformers;
- autonomous transformer run and lift;
- an outer `operatorStage` recursion over the universal index;
- progressivity as the direct comparison invariant;
- pointwise comparison source from the full Contender-6 family to the new
  autonomous family; and
- a structural domination theorem for every W-language-defined outer schedule.

The `lambda^lambda` size claim is an informal calibration, not a formal result.
The Lean source was not kernel-compiled in the preparation environment; see
`validation/VALIDATION.md`.
