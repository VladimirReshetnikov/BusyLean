# Provenance and scope

The proposal was prepared against the public `main` branch of
`VladimirReshetnikov/BusyLean` as inspected on 2026-10-12/13 UTC. It reuses the
public interfaces and proof patterns of:

- `BusyLean/Contender9.lean` and `Comparison9.lean` for packed oracle families
  and forest reflection;
- `BusyLean/Contender10.lean` and `Comparison10.lean` for kind-polymorphic
  reflection and its local inequalities;
- `BusyLean/Contender6.lean` and `Comparison.lean` for the self-generated W-tree
  index and the explicit leaf-to-index inclusion path.

No existing repository file is redistributed in full. The package consists of
new proposed source files, integration text, and a research article.

The article's growth-rate discussion is heuristic. The exact claimed result is
the Lean theorem `contender_10_lt_contender_11`, pending kernel verification in
the target checkout.
