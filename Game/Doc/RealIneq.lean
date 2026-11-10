import GameServer

/-! # Documentation for inequalities in `ℝ` -/

/--
`neg_le_neg a b : a ≤ b → -b ≤ -a` for reals.

## Examples

* `MyReal.neg_le_neg _ _ h` turns `h : a n ≤ b n` into `-b n ≤ -a n`.
* `MyReal.neg_le_neg 0 x h : -x ≤ -0`.
-/
TheoremDoc MyReal.neg_le_neg as "neg_le_neg (ℝ)" in "≤ℝ"

/--
`add_le_add a b c d : a ≤ b → c ≤ d → a + c ≤ b + d` for reals.

## Examples

* `MyReal.add_le_add _ _ _ _ h1 h2` adds two inequalities.
* `MyReal.add_le_add _ _ _ _ h (MyReal.le_refl c)` adds `c` on the right.
-/
TheoremDoc MyReal.add_le_add as "add_le_add (ℝ)" in "≤ℝ"

/--
`neg_zero : -(0 : ℝ) = 0`.

## Examples

* `rw [MyReal.neg_zero]` replaces `-0` by `0`.
* `x - 0`: `rw [sub_eq_add_neg, neg_zero, add_zero]` gives `x`.
-/
TheoremDoc MyReal.neg_zero as "neg_zero (ℝ)" in "ℝ"

/--
`eq_zero_of_nonneg_neg x : nonneg x → nonneg (-x) → x = 0` for reals.

## Examples

* `MyReal.eq_zero_of_nonneg_neg x h1 h2 : x = 0`.
* With `x = y - x'` it shows two reals are equal.
-/
TheoremDoc MyReal.eq_zero_of_nonneg_neg as "eq_zero_of_nonneg_neg (ℝ)" in "≤ℝ"

/--
`eq_of_sub_eq_zero x y : y - x = 0 → y = x` for reals.

## Examples

* `MyReal.eq_of_sub_eq_zero x y h : y = x` from `h : y - x = 0`.
* Goal `L = M`: `apply MyReal.eq_of_sub_eq_zero`, then prove `L - M = 0`.
-/
TheoremDoc MyReal.eq_of_sub_eq_zero as "eq_of_sub_eq_zero (ℝ)" in "ℝ"

/--
`ofRat_le a b : a ≤ b → ofRat a ≤ ofRat b`. `ofRat` keeps `≤`.

## Examples

* `ofRat_le _ _ (MyRat.eps_nonneg k) : ofRat 0 ≤ ofRat (frac 1 (succ k))`.
* `ofRat_le _ _ (MyRat.inv_le_inv k n h)` compares two small reals.
-/
TheoremDoc MyReal.ofRat_le as "ofRat_le" in "≤ℝ"

/--
`abs_neg a : abs (-a) = abs a` for rationals.

## Examples

* `rw [MyRat.abs_neg]` removes a minus inside `abs`.
* `MyRat.abs_neg (s n) : MyRat.abs (-s n) = MyRat.abs (s n)`.
-/
TheoremDoc MyRat.abs_neg as "abs_neg (ℚ)" in "abs"

/--
`abs_neg x : abs (-x) = abs x` for reals.

## Examples

* `rw [MyReal.abs_neg]` removes a minus inside `abs`.
* `rw [← abs_neg x]` turns `abs x` into `abs (-x)`.
-/
TheoremDoc MyReal.abs_neg as "abs_neg (ℝ)" in "abs"

/--
`abs_sub_comm x y : abs (x - y) = abs (y - x)` for reals.

## Examples

* `rw [abs_sub_comm]` swaps the first difference inside `abs`.
* `abs_sub_comm (a n) L : abs (a n - L) = abs (L - a n)`.
-/
TheoremDoc MyReal.abs_sub_comm as "abs_sub_comm" in "abs"

/--
`abs_bounds x : x ≤ abs x ∧ -x ≤ abs x` for reals.

## Examples

* `obtain ⟨h1, h2⟩ := MyReal.abs_bounds (a n - L)`.
* `MyReal.le_trans _ _ _ (MyReal.abs_bounds x).1 h` with `h : abs x ≤ y` gives `x ≤ y`.
-/
TheoremDoc MyReal.abs_bounds as "abs_bounds (ℝ)" in "abs"

/--
`abs_le x y : x ≤ y → -x ≤ y → abs x ≤ y` for reals.

## Examples

* Goal `abs x ≤ y`: `apply MyReal.abs_le` leaves `x ≤ y` and `-x ≤ y`.
* `MyReal.abs_le _ _ h1 h2` with both bounds.
-/
TheoremDoc MyReal.abs_le as "abs_le (ℝ)" in "abs"

/--
`archimedean q : ∃ n : ℕ, q ≤ frac (mk n 0) 1`. Every rational is below a natural number.

## Examples

* `obtain ⟨p, hp⟩ := MyRat.archimedean q`.
* `MyRat.archimedean (s N + frac 1 (succ 0))` bounds `s N + 1`.
-/
TheoremDoc MyRat.archimedean as "archimedean (ℚ)" in "ℚ"

/--
`archimedean x : ∃ n : ℕ, x ≤ ofRat (frac (mk n 0) 1)`. Every real is below a natural number.

## Examples

* `obtain ⟨n, hn⟩ := MyReal.archimedean x`.
* `MyReal.archimedean (ofRat q)` for a rational `q` seen in `ℝ`.
-/
TheoremDoc MyReal.archimedean as "archimedean (ℝ)" in "≤ℝ"
