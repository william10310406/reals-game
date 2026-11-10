import GameServer

/-!
# Documentation for the natural numbers
-/

/--
`MyNat` is our own type of natural numbers. Every natural number is
either `0` or `succ n` for a natural number `n`.

## Examples

* `succ 0` is the number after `0`. We write it `1` (theorem `one_eq_succ_zero`).
* `succ (succ 0)` is the number after `1`.
-/
DefinitionDoc MyNat as "ℕ (MyNat)"

/--
`succ n` is the number after `n` (the successor of `n`).

## Examples

* `succ 0 = 1` (theorem `one_eq_succ_zero`, read backwards).
* `a + succ b = succ (a + b)` (theorem `add_succ`).
-/
DefinitionDoc MyNat.succ as "succ"

/--
`a + b` is addition. It is defined by two rules:
`a + 0 = a` (`add_zero`) and `a + succ b = succ (a + b)` (`add_succ`).

## Examples

* `a + 0 = a`.
* `a + succ 0 = succ a`.
-/
DefinitionDoc MyNat.add as "+"

/--
`a * b` is multiplication. It is defined by two rules:
`a * 0 = 0` (`mul_zero`) and `a * succ b = a * b + a` (`mul_succ`).

## Examples

* `a * 0 = 0`.
* `a * succ 0 = a * 0 + a`.
-/
DefinitionDoc MyNat.mul as "*"

/--
`a ≤ b` means: there is a `c` with `b = a + c`.
Use `rw [le_iff_exists_add]` to see this form.

## Examples

* `a ≤ a + 3`, because `a + 3 = a + 3`.
* `0 ≤ b`, because `b = 0 + b`.
-/
DefinitionDoc MyNat.le as "≤"

/--
`add_zero a : a + 0 = a`. This is a rule of addition.

## Examples

* `rw [add_zero]` changes `x + 0` to `x` in the goal.
* `rw [add_zero] at h` changes `x + 0` to `x` in the hypothesis `h`.
-/
TheoremDoc MyNat.add_zero as "add_zero" in "+"

/--
`add_succ a b : a + succ b = succ (a + b)`. This is a rule of addition.

## Examples

* `rw [add_succ]` changes `x + succ y` to `succ (x + y)`.
* With `a + succ 0` in the goal, `rw [add_succ, add_zero]` gives `succ a`.
-/
TheoremDoc MyNat.add_succ as "add_succ" in "+"

/--
`one_eq_succ_zero : 1 = succ 0`.

## Examples

* `rw [one_eq_succ_zero]` changes `1` to `succ 0`.
* `rw [← one_eq_succ_zero]` changes `succ 0` to `1`.
-/
TheoremDoc MyNat.one_eq_succ_zero as "one_eq_succ_zero" in "ℕ"

/--
`succ_inj a b : succ a = succ b → a = b`. Different numbers have different successors.

## Examples

* `h : succ a = succ b`: `exact succ_inj a b h` proves `a = b`.
* Goal `a = b`: `apply succ_inj` changes it to `succ a = succ b`.
-/
TheoremDoc MyNat.succ_inj as "succ_inj" in "ℕ"

/--
`zero_ne_succ a : 0 ≠ succ a`. Zero is not a successor.

## Examples

* `h : 0 = succ a`: `exact zero_ne_succ a h` proves `False`.
* Goal `False` and `h : succ a = 0`: `apply zero_ne_succ a`, then `rw [h]`.
-/
TheoremDoc MyNat.zero_ne_succ as "zero_ne_succ" in "ℕ"

/--
`add_one_eq_succ a : a + 1 = succ a`.

## Examples

* `rw [add_one_eq_succ]` changes `x + 1` to `succ x`.
* `rw [← add_one_eq_succ]` changes `succ x` to `x + 1`.
-/
TheoremDoc MyNat.add_one_eq_succ as "add_one_eq_succ" in "+"

/--
`zero_add n : 0 + n = n`.

## Examples

* `rw [zero_add]` changes `0 + x` to `x`.
* `zero_add 5 : 0 + 5 = 5`.
-/
TheoremDoc MyNat.zero_add as "zero_add" in "+"

/--
`succ_add a b : succ a + b = succ (a + b)`.

## Examples

* `rw [succ_add]` changes `succ x + y` to `succ (x + y)`.
* `succ_add 0 b : succ 0 + b = succ (0 + b)`.
-/
TheoremDoc MyNat.succ_add as "succ_add" in "+"

/--
`add_comm a b : a + b = b + a`.

## Examples

* `rw [add_comm]` swaps the first sum it finds.
* `rw [add_comm a b]` changes exactly `a + b` to `b + a`.
-/
TheoremDoc MyNat.add_comm as "add_comm" in "+"

/--
`add_assoc a b c : a + b + c = a + (b + c)`. Note `a + b + c` means `(a + b) + c`.

## Examples

* `rw [add_assoc]` moves brackets to the right.
* `rw [← add_assoc]` moves brackets to the left.
-/
TheoremDoc MyNat.add_assoc as "add_assoc" in "+"

/--
`add_right_cancel a b n : a + n = b + n → a = b`.

## Examples

* `h : x + 3 = y + 3`: `exact add_right_cancel x y 3 h` proves `x = y`.
* Goal `a = b`: `apply add_right_cancel a b n` changes it to `a + n = b + n`.
-/
TheoremDoc MyNat.add_right_cancel as "add_right_cancel" in "+"

/--
`add_left_cancel a b n : n + a = n + b → a = b`.

## Examples

* `h : 3 + x = 3 + y`: `exact add_left_cancel x y 3 h` proves `x = y`.
* Goal `a = b`: `apply add_left_cancel a b n` changes it to `n + a = n + b`.
-/
TheoremDoc MyNat.add_left_cancel as "add_left_cancel" in "+"

/--
`eq_zero_of_add_eq_zero a b : a + b = 0 → b = 0`.

## Examples

* `h : x + y = 0`: `exact eq_zero_of_add_eq_zero x y h` proves `y = 0`.
* With `add_comm` you also get `a = 0` from `a + b = 0`.
-/
TheoremDoc MyNat.eq_zero_of_add_eq_zero as "eq_zero_of_add_eq_zero" in "+"

/--
`mul_zero a : a * 0 = 0`. This is a rule of multiplication.

## Examples

* `rw [mul_zero]` changes `x * 0` to `0`.
* `mul_zero 7 : 7 * 0 = 0`.
-/
TheoremDoc MyNat.mul_zero as "mul_zero" in "*"

/--
`mul_succ a b : a * succ b = a * b + a`. This is a rule of multiplication.

## Examples

* `rw [mul_succ]` changes `x * succ y` to `x * y + x`.
* `rw [mul_succ, mul_zero]` changes `a * succ 0` to `0 + a`.
-/
TheoremDoc MyNat.mul_succ as "mul_succ" in "*"

/--
`zero_mul n : 0 * n = 0`.

## Examples

* `rw [zero_mul]` changes `0 * x` to `0`.
* `zero_mul 4 : 0 * 4 = 0`.
-/
TheoremDoc MyNat.zero_mul as "zero_mul" in "*"

/--
`succ_mul a b : succ a * b = a * b + b`.

## Examples

* `rw [succ_mul]` changes `succ x * y` to `x * y + y`.
* `succ_mul 0 b : succ 0 * b = 0 * b + b`.
-/
TheoremDoc MyNat.succ_mul as "succ_mul" in "*"

/--
`mul_comm a b : a * b = b * a`.

## Examples

* `rw [mul_comm]` swaps the first product it finds.
* `rw [mul_comm a b]` changes exactly `a * b` to `b * a`.
-/
TheoremDoc MyNat.mul_comm as "mul_comm" in "*"

/--
`mul_add a b c : a * (b + c) = a * b + a * c`.

## Examples

* `rw [mul_add]` multiplies out `x * (y + z)`.
* `rw [← mul_add]` takes out a common factor on the left.
-/
TheoremDoc MyNat.mul_add as "mul_add" in "*"

/--
`add_mul a b c : (a + b) * c = a * c + b * c`.

## Examples

* `rw [add_mul]` multiplies out `(x + y) * z`.
* `rw [← add_mul]` takes out a common factor on the right.
-/
TheoremDoc MyNat.add_mul as "add_mul" in "*"

/--
`mul_assoc a b c : a * b * c = a * (b * c)`.

## Examples

* `rw [mul_assoc]` moves brackets to the right.
* `rw [← mul_assoc]` moves brackets to the left.
-/
TheoremDoc MyNat.mul_assoc as "mul_assoc" in "*"

/--
`le_iff_exists_add a b : a ≤ b ↔ ∃ c, b = a + c`. This is the definition of `≤`.

## Examples

* Goal `a ≤ b`: `rw [le_iff_exists_add]` changes it to `∃ c, b = a + c`.
* `h : a ≤ b`: `rw [le_iff_exists_add] at h`, then `obtain ⟨c, hc⟩ := h`.
-/
TheoremDoc MyNat.le_iff_exists_add as "le_iff_exists_add" in "≤"

/--
`le_refl a : a ≤ a`.

## Examples

* `exact le_refl x` proves `x ≤ x`.
* `le_refl 0 : 0 ≤ 0`.
-/
TheoremDoc MyNat.le_refl as "le_refl" in "≤"

/--
`le_trans a b c : a ≤ b → b ≤ c → a ≤ c`.

## Examples

* `h₁ : a ≤ b` and `h₂ : b ≤ c`: `exact le_trans a b c h₁ h₂` proves `a ≤ c`.
* Goal `a ≤ c`: `apply le_trans a b c` gives the goals `a ≤ b` and `b ≤ c`.
-/
TheoremDoc MyNat.le_trans as "le_trans" in "≤"

/--
`mul_one a : a * 1 = a`.

## Examples

* `rw [MyNat.mul_one]` removes `* 1`.
* `MyNat.mul_one 5 : 5 * 1 = 5`.
-/
TheoremDoc MyNat.mul_one as "mul_one" in "*"

/--
`one_ne_zero : 1 ≠ 0` in `ℕ`.

## Examples

* `exact MyNat.one_ne_zero` proves `(1 : ℕ) ≠ 0`.
* `frac_eq hb MyNat.one_ne_zero` compares a fraction with `frac c 1`.
-/
TheoremDoc MyNat.one_ne_zero as "one_ne_zero" in "ℕ"

/--
`mul_ne_zero a b : a ≠ 0 → b ≠ 0 → a * b ≠ 0`.

## Examples

* `MyNat.mul_ne_zero b d hb hd : b * d ≠ 0`.
* Needed when you add fractions: the new denominator is `b * d`.
-/
TheoremDoc MyNat.mul_ne_zero as "mul_ne_zero" in "ℕ"
