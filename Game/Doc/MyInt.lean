import GameServer

/-!
# Documentation for the integers
-/

/--
`MyInt` (written `ℤ`) is our type of integers. An integer is a pair of natural numbers
`(a, b)`, read as `a - b`. Two pairs give the same integer when `a + d = c + b`.

## Examples

* `mk 3 5` and `mk 0 2` are the same integer, `-2`, because `3 + 2 = 0 + 5`.
* `mk 4 0` is the integer `4`.
-/
DefinitionDoc MyInt as "ℤ (MyInt)"

/--
`mk a b` is the integer `a - b`, for natural numbers `a` and `b`.

## Examples

* `mk 1 0` is `1` (theorem `one_def`).
* `mk 0 0` is `0` (theorem `zero_def`).
-/
DefinitionDoc MyInt.mk as "mk"

/--
`x ≤ y` for integers means: `y = x + mk c 0` for some natural number `c`.

## Examples

* `mk 1 0 ≤ mk 3 0`, with `c = 2`.
* `x ≤ x`, with `c = 0`.
-/
DefinitionDoc MyInt.le as "≤ on ℤ"

/--
`mk_eq a b c d : mk a b = mk c d ↔ a + d = c + b`. When are two pairs the same integer?

## Examples

* Goal `mk a b = mk c d`: `rw [mk_eq]` changes it to `a + d = c + b`.
* `h : mk a b = mk c d`: `rw [mk_eq] at h` gives `h : a + d = c + b`.
-/
TheoremDoc MyInt.mk_eq as "mk_eq" in "ℤ"

/--
`exists_mk x : ∃ a b, x = mk a b`. Every integer is a pair.

## Examples

* `obtain ⟨a, b, rfl⟩ := exists_mk x` replaces `x` by `mk a b` everywhere.
* `obtain ⟨a, b, h⟩ := exists_mk x` gives `h : x = mk a b`.
-/
TheoremDoc MyInt.exists_mk as "exists_mk" in "ℤ"

/--
`zero_def : 0 = mk 0 0`.

## Examples

* `rw [zero_def]` changes the integer `0` to `mk 0 0`.
* `rw [← zero_def]` changes `mk 0 0` to `0`.
-/
TheoremDoc MyInt.zero_def as "zero_def" in "ℤ"

/--
`one_def : 1 = mk 1 0`.

## Examples

* `rw [one_def]` changes the integer `1` to `mk 1 0`.
* `rw [← one_def]` changes `mk 1 0` to `1`.
-/
TheoremDoc MyInt.one_def as "one_def" in "ℤ"

/--
`mk_add_mk a b c d : mk a b + mk c d = mk (a + c) (b + d)`. This is how `+` is defined.

## Examples

* `rw [mk_add_mk]` adds the first two pairs it finds.
* `mk 1 0 + mk 0 1 = mk (1 + 0) (0 + 1)`.
-/
TheoremDoc MyInt.mk_add_mk as "mk_add_mk" in "ℤ"

/--
`neg_mk a b : -mk a b = mk b a`. This is how `-` is defined.

## Examples

* `rw [neg_mk]` swaps the pair under the first `-`.
* `-mk 2 0 = mk 0 2`.
-/
TheoremDoc MyInt.neg_mk as "neg_mk" in "ℤ"

/--
`mk_mul_mk a b c d : mk a b * mk c d = mk (a * c + b * d) (a * d + b * c)`.
This is how `*` is defined: `(a - b)(c - d) = (ac + bd) - (ad + bc)`.

## Examples

* `rw [mk_mul_mk]` multiplies the first two pairs it finds.
* `mk 0 1 * mk 0 1 = mk (0 * 0 + 1 * 1) (0 * 1 + 1 * 0)`, which is `1`.
-/
TheoremDoc MyInt.mk_mul_mk as "mk_mul_mk" in "ℤ"

/--
`le_iff x y : x ≤ y ↔ ∃ c : ℕ, y = x + mk c 0`. This is the definition of `≤` on `ℤ`.

## Examples

* Goal `x ≤ y`: `rw [le_iff]` changes it to `∃ c, y = x + mk c 0`.
* `h : x ≤ y`: `rw [le_iff] at h`, then `obtain ⟨c, hc⟩ := h`.
-/
TheoremDoc MyInt.le_iff as "le_iff" in "ℤ"

/--
`mk_self a : mk a a = 0`.

## Examples

* `rw [mk_self]` changes `mk a a` to `0`.
* `mk_self 3 : mk 3 3 = 0`.
-/
TheoremDoc MyInt.mk_self as "mk_self" in "ℤ"

/--
`add_comm x y : x + y = y + x` for integers.

## Examples

* `rw [add_comm]` swaps the first sum it finds.
* `rw [add_comm x y]` changes exactly `x + y`.
-/
TheoremDoc MyInt.add_comm as "add_comm (ℤ)" in "ℤ"

/--
`add_assoc x y z : x + y + z = x + (y + z)` for integers.

## Examples

* `rw [add_assoc]` moves brackets to the right.
* `rw [← add_assoc]` moves brackets to the left.
-/
TheoremDoc MyInt.add_assoc as "add_assoc (ℤ)" in "ℤ"

/--
`add_zero x : x + 0 = x` for integers.

## Examples

* `rw [add_zero]` removes `+ 0`.
* `add_zero (mk 2 1) : mk 2 1 + 0 = mk 2 1`.
-/
TheoremDoc MyInt.add_zero as "add_zero (ℤ)" in "ℤ"

/--
`add_neg x : x + -x = 0` for integers.

## Examples

* `rw [add_neg]` changes `y + -y` to `0`.
* `add_neg 5 : 5 + -5 = 0`.
-/
TheoremDoc MyInt.add_neg as "add_neg" in "ℤ"

/--
`mul_comm x y : x * y = y * x` for integers.

## Examples

* `rw [mul_comm]` swaps the first product it finds.
* `rw [mul_comm x y]` changes exactly `x * y`.
-/
TheoremDoc MyInt.mul_comm as "mul_comm (ℤ)" in "ℤ"

/--
`mul_add x y z : x * (y + z) = x * y + x * z` for integers.

## Examples

* `rw [mul_add]` multiplies out the first bracket of this shape.
* `rw [← mul_add]` takes out a common factor on the left.
-/
TheoremDoc MyInt.mul_add as "mul_add (ℤ)" in "ℤ"

/--
`mul_assoc x y z : x * y * z = x * (y * z)` for integers.

## Examples

* `rw [mul_assoc]` moves brackets to the right.
* `rw [← mul_assoc]` moves brackets to the left.
-/
TheoremDoc MyInt.mul_assoc as "mul_assoc (ℤ)" in "ℤ"

/--
`le_refl x : x ≤ x` for integers.

## Examples

* `exact le_refl x` proves `x ≤ x`.
* `le_refl 0 : (0 : ℤ) ≤ 0`.
-/
TheoremDoc MyInt.le_refl as "le_refl (ℤ)" in "ℤ"
