# Contender 35 theorem inventory

## New tree and metalanguage layer

- `BusyLean.Ordinal.MTL.Tm.eval`: total semantic interpreter for the typed
  metalanguage with `boost` and higher-order `lift` primitives.
- `BusyLean.Ordinal.MTL.infer`: sound-by-construction raw-term type checker.
- `BusyLean.Ordinal.MTL.funsUpTo`: finite enumeration of checked closed
  `tree -> tree` programs.
- `BusyLean.Ordinal.metaLangLift`: one closure step over a language-closure
  operator and a base tree transformer.
- `BusyLean.Ordinal.metaBoostT`: structural transfinite iteration of
  metalanguage closure along a countable tree.
- `BusyLean.Ordinal.metaLanguageTree`: the Contender 35 tree at input `n`.

## Reflection definitions

- `BusyLean.FL.sn_erase_metatree`
- `BusyLean.FL.metavalue`
- `BusyLean.FL.metatreeLadderUpTo`
- `BusyLean.reflectMetaFamily`
- `BusyLean.metaTransformer`
- `BusyLean.family34`
- `BusyLean.schedule35`
- `BusyLean.rank35`
- `BusyLean.F35`
- `BusyLean.contender_35`

## Comparison theorems

- `BusyLean.lt_reflectMetaFamily`
- `BusyLean.oracle_lt_reflectMetaFamily`
- `BusyLean.metavalue_lt_reflectMetaFamily`
- `BusyLean.metaTransformer_progressive`
- `BusyLean.family34_lt_F35`
- `BusyLean.raw_meta_reflection_lt_F35`
- `BusyLean.metavalue_lt_F35`
- `BusyLean.input_lt_family34`
- `BusyLean.input_lt_F35`
- `BusyLean.contender_34_lt_contender_35`
- `BusyLean.contender_33_lt_contender_35`

The decisive uniform theorem is `family34_lt_F35 (n) : family34 n < F35 n`.
The final theorem follows because `family34 42` is definitionally equal to
`contender_34` and `F35` is strictly inflationary.
