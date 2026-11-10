import GameServer

/-! # Documentation for inequalities and limits -/

/--
`add_le_add_right a b c : a ≤ b → a + c ≤ b + c`.

## Examples

* `exact add_le_add_right a b c h` adds `c` on both sides of `h : a ≤ b`.
* `add_le_add_right 0 1 c h : 0 + c ≤ 1 + c`.
-/
TheoremDoc MyRat.add_le_add_right as "add_le_add_right" in "ℚ"

/--
`neg_neg x : -(-x) = x` for integers.

## Examples

* `rw [neg_neg]` removes two minus signs.
* `MyInt.neg_neg 3 : -(-3) = 3`.
-/
TheoremDoc MyInt.neg_neg as "neg_neg (ℤ)" in "ℤ"

/--
`neg_neg x : -(-x) = x` for rationals.

## Examples

* `rw [neg_neg]` removes two minus signs.
* `neg_neg (frac 1 2) : -(-frac 1 2) = frac 1 2`.
-/
TheoremDoc MyRat.neg_neg as "neg_neg (ℚ)" in "ℚ"

/--
`neg_le_neg a b : a ≤ b → -b ≤ -a`.

## Examples

* `exact neg_le_neg a b h` flips `h : a ≤ b`.
* `neg_le_neg 0 x h : -x ≤ -0`.
-/
TheoremDoc MyRat.neg_le_neg as "neg_le_neg" in "ℚ"

/--
`eq_zero_of_nonneg_neg x : 0 ≤ x → 0 ≤ -x → x = 0` for integers.

## Examples

* `MyInt.eq_zero_of_nonneg_neg a h₁ h₂ : a = 0`.
* Used for the same fact in `ℚ`.
-/
TheoremDoc MyInt.eq_zero_of_nonneg_neg as "eq_zero_of_nonneg_neg (ℤ)" in "ℤ"

/--
`eq_zero_of_nonneg_neg x : nonneg x → nonneg (-x) → x = 0`.

## Examples

* `eq_zero_of_nonneg_neg (y - x) h₁ h₂ : y - x = 0`.
* The key step of `le_antisymm`.
-/
TheoremDoc MyRat.eq_zero_of_nonneg_neg as "eq_zero_of_nonneg_neg (ℚ)" in "ℚ"

/--
`neg_sub x y : -(y - x) = x - y`.

## Examples

* `rw [neg_sub]` turns `-(y - x)` into `x - y`.
* `rw [← neg_sub x y] at h` turns `x - y` into `-(y - x)`.
-/
TheoremDoc MyRat.neg_sub as "neg_sub" in "ℚ"

/--
`eq_of_sub_eq_zero x y : y - x = 0 → y = x`.

## Examples

* `exact eq_of_sub_eq_zero x y h` proves `y = x`.
* `have e := eq_of_sub_eq_zero x y h` adds `e : y = x`.
-/
TheoremDoc MyRat.eq_of_sub_eq_zero as "eq_of_sub_eq_zero" in "ℚ"

/--
`le_antisymm x y : x ≤ y → y ≤ x → x = y`.

## Examples

* `exact le_antisymm x y h₁ h₂` proves `x = y`.
* To prove `x = y`, prove `x ≤ y` and `y ≤ x`.
-/
TheoremDoc MyRat.le_antisymm as "le_antisymm (ℚ)" in "ℚ"

/--
`nonneg_mul x y : 0 ≤ x → 0 ≤ y → 0 ≤ x * y` for integers.

## Examples

* `MyInt.nonneg_mul a c ha hc : 0 ≤ a * c`.
* Used for products of rationals.
-/
TheoremDoc MyInt.nonneg_mul as "nonneg_mul (ℤ)" in "ℤ"

/--
`nonneg_mul x y : nonneg x → nonneg y → nonneg (x * y)`.

## Examples

* `exact nonneg_mul x y hx hy` proves `nonneg (x * y)`.
* `nonneg_mul x x h h : nonneg (x * x)`.
-/
TheoremDoc MyRat.nonneg_mul as "nonneg_mul (ℚ)" in "ℚ"

/--
`frac_mul_frac hb hd : frac a b * frac c d = frac (a * c) (b * d)`.

## Examples

* `rw [frac_mul_frac hb hd]` multiplies two fractions.
* `frac 1 2 * frac 1 3 = frac (1 * 1) (2 * 3)`.
-/
TheoremDoc MyRat.frac_mul_frac as "frac_mul_frac" in "ℚ"

/--
`tendsto_iff_close s L : Tendsto s L ↔ Close s (const L)`. This is the definition of a limit.

## Examples

* `rw [tendsto_iff_close] at h ⊢` turns limits into closeness.
* `rw [← tendsto_iff_close]` turns `Close s (const L)` back into `Tendsto s L`.
-/
TheoremDoc MyRat.tendsto_iff_close as "tendsto_iff_close" in "lim"

/--
`invSucc_apply n : invSucc n = frac 1 (succ n)`.

## Examples

* `rw [invSucc_apply]` computes the first `invSucc n`.
* `invSucc_apply 0 : invSucc 0 = frac 1 (succ 0)`.
-/
TheoremDoc MyRat.invSucc_apply as "invSucc_apply" in "lim"

/--
`tendsto_const c : Tendsto (const c) c`.

## Examples

* `exact tendsto_const c`.
* `tendsto_const 0 : Tendsto (const 0) 0`.
-/
TheoremDoc MyRat.tendsto_const as "tendsto_const" in "lim"

/--
`close_const_add a b : Close (addSeq (const a) (const b)) (const (a + b))`.

## Examples

* Used in `tendsto_add`.
* `close_const_add 1 2`.
-/
TheoremDoc MyRat.close_const_add as "close_const_add" in "lim"

/--
`tendsto_add s t a b : Tendsto s a → Tendsto t b → Tendsto (addSeq s t) (a + b)`.

## Examples

* `exact tendsto_add s t a b hs ht`.
* The limit of a sum is the sum of the limits.
-/
TheoremDoc MyRat.tendsto_add as "tendsto_add" in "lim"

/--
`tendsto_of_close s t L : Close t s → Tendsto s L → Tendsto t L`.

## Examples

* `exact tendsto_of_close s t L h₁ h₂`.
* Close sequences have the same limit.
-/
TheoremDoc MyRat.tendsto_of_close as "tendsto_of_close" in "lim"

/--
`cauchy_of_tendsto s L : Tendsto s L → IsCauchy s`.

## Examples

* `cauchy_of_tendsto s L h : IsCauchy s`.
* So `ofSeq s (cauchy_of_tendsto s L h)` is a real number.
-/
TheoremDoc MyRat.cauchy_of_tendsto as "cauchy_of_tendsto" in "lim"

/--
`ofSeq_eq_of_tendsto s L hs : Tendsto s L → ofSeq s hs = ofSeq (const L) (const_cauchy L)`.

## Examples

* `ofSeq_eq_of_tendsto s L hs h` says `s` is the real number `L`.
* With `tendsto_invSucc`: the real of `invSucc` is `0`.
-/
TheoremDoc MyRat.ofSeq_eq_of_tendsto as "ofSeq_eq_of_tendsto" in "lim"

/--
`inv_le_inv k n : k ≤ n → frac 1 (succ n) ≤ frac 1 (succ k)`.

## Examples

* `exact inv_le_inv k n h`.
* Bigger denominators give smaller fractions.
-/
TheoremDoc MyRat.inv_le_inv as "inv_le_inv" in "lim"

/--
`tendsto_invSucc : Tendsto invSucc 0`. The sequence `1/(n+1)` tends to `0`.

## Examples

* `exact tendsto_invSucc`.
* With `tendsto_add`: `invSucc + const c` tends to `0 + c`.
-/
TheoremDoc MyRat.tendsto_invSucc as "tendsto_invSucc" in "lim"

/--
`Tendsto s L`: for every `k` there is `N` such that `s n - L ≤ frac 1 (succ k)` and
`L - s n ≤ frac 1 (succ k)` for all `n ≥ N`.

## Examples

* `Tendsto (const c) c` (theorem `tendsto_const`).
* `Tendsto invSucc 0` (theorem `tendsto_invSucc`).
-/
DefinitionDoc MyRat.Tendsto as "Tendsto"

/--
`invSucc` is the sequence `1/1, 1/2, 1/3, ...`: `invSucc n = frac 1 (succ n)`.

## Examples

* `invSucc 0 = frac 1 (succ 0)`.
* `Tendsto invSucc 0` (theorem `tendsto_invSucc`).
-/
DefinitionDoc MyRat.invSucc as "invSucc"
