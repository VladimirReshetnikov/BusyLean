# Design alternatives considered

## Chosen: self-accelerated full-round diagonal

The selected construction combines three distinct amplifiers:

1. kind-polymorphic System Fω reflection;
2. forest reflection along the W-language's self-generated index; and
3. a prior-family-sized tower whose successor input is the preceding value.

It has a short formal comparison and reuses already formalized normalization.

## Rejected: a larger arithmetic wrapper around Contender 10

Expressions such as `2 ^ family10 42`, a fixed iterate of `F10`, or directly
adding one to the preceding number would prove a numerical increase but would
not constitute the qualitative strengthening required by the contest's
no-laziness rule.

## Rejected: a single forest-reflection round

One round is already stronger than the incumbent and would be easier to check,
but it leaves a readily available diagonal unused. The selected tower proves a
strict increase at every round and then diagonalizes at a count supplied by the
preceding construction itself.

## Deferred: a hierarchy of kind universes

The repository article identifies stratified kind universes as a natural next
language-level jump. Formalizing their syntax, checker, reducibility model, and
strong normalization would be scientifically valuable, but it is substantially
larger and riskier than a contest successor that can reuse the current
kind-polymorphic normalization theorem.

## Deferred: large elimination / CIC-like reflection

This is potentially a much larger jump, but requires a realizability model for
dependent inductive types and large elimination. It is a research program, not
a compact successor module.

## Rejected: pointwise maximum of many rounds

Taking a finite maximum loses the dynamic ability of a reflected program to
select and call a child stage at a computed index. Forest reflection preserves
that oracle-family structure.
