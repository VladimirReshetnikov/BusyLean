# Proof obligations and fallback forms

This note separates the mathematical argument from Lean elaboration details.

## 1. Reflection maximum

For

```lean
def reflect11 (fs : W.Family) (n : Nat) : Nat :=
  n + 1 + max (prefixMax (fun i => fs i n) n)
    (maximum (Fk.fvalue (packFamily fs) n) (Fk.ctmsUpTo n))
```

prove:

- every `fs i n` with `i <= n` is smaller;
- every `Fk.fvalue ... t` for `t ∈ Fk.ctmsUpTo n` is smaller;
- `n` is smaller.

These are direct copies of the established Contender 9/10 maximum arguments.

## 2. Seed inclusion in one full round

The explicit path is

```text
seed value
  < stage11 seed leaf
  < stage11 seed (treesOfDepth 0)
  < stage11 seed index
  = round11 seed.
```

The middle step uses the existing theorem `first_tree_leaf`.
No monotonicity of reflection in its oracle is assumed or needed.

## 3. Tower successor

By definition,

```text
T_{k+1}(n) = round11(T_k)(T_k(n)).
```

The theorem `input_lt_round11` gives

```text
T_k(n) < round11(T_k)(T_k(n)) = T_{k+1}(n).
```

## 4. Comparison with Contender 10

Let `B = family10`. Then

```text
B(n) < B(B(n)) < T_{B(n)+1}(B(n)) = F11(n).
```

The first inequality is `input_lt_family10` at `B(n)`. The second follows by
iterating the strict tower-successor theorem.

At `n = 42`, `B(42)` is definitionally `contender_10`, hence

```text
contender_10 < F11(42) < F11(F11(42)) = contender_11.
```

## 5. Elaboration fallbacks

If definitional reduction does not fire automatically, replace the affected
closing line by an explicit `simpa`:

```lean
simpa [F11] using Nat.lt_trans h₁ h₂
```

For `fvalue_lt_round11`, use:

```lean
unfold round11 index stage11
exact fvalue_lt_reflect11 _ ht
```

For `input_lt_family10`, name the two intermediate terms explicitly:

```lean
have h₁ : n < F10 n := Fk.input_lt_reflectFk family9 n
have h₂ : F10 n < F10 (F10 n) :=
  Fk.input_lt_reflectFk family9 (F10 n)
simpa [family10] using Nat.lt_trans h₁ h₂
```

For the required comparison:

```lean
change F10 (F10 42) < F11 (F11 42)
exact Nat.lt_trans (family10_lt_F11 42) (input_lt_F11 (F11 42))
```

These are presentation changes only.
