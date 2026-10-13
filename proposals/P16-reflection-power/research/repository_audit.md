# BusyLean repository audit

Audit target: `VladimirReshetnikov/BusyLean` at commit
`86b360648163f0249eab79539438b6a83dfe8215` (2026-10-13 UTC).

## Incumbent

The repository defines

```lean
def contender_6 : Nat := stage p5Family index 42
```

where `stage` is forest reflection, `p5Family` is the P5 diagonal seed, and
`index` joins every `W Nat` tree denoted by the closed terms enumerated by the
P5 W-language.  `Comparison.lean` proves strict domination of the exact
Contender 5 port and of P5's proposed value.

## Underused structure

The incumbent uses a W-tree as the control object *inside one scheduler*.  The
new proposal observes that a scheduler itself has the same three-argument shape

```text
Family -> WTree Nat -> Nat -> Nat
```

and can therefore be reflected through the same universal index.  This yields
an order-raising operator on schedulers, not merely a larger input constant.

## Rule alignment

- Closed `Nat`: yes.
- Constructive: structural W-tree recursion plus primitive Nat recursion.
- No incumbent-value counter: `contender_6` is not in the defining closure by
  design; a kernel-side audit is supplied.
- Large margin: the order height is `succ (42 + p5Family 0 42)`.
- Formal comparison: `contender_6_lt_contender_7` is supplied.
- Toolchain: the upstream repository pins `leanprover/lean4:v4.34.0`.
