import GameServer

/-!
# Documentation for the rationals
-/

/--
`MyRat` (written `ℚ`) is our type of rational numbers. A rational is `frac a b`,
read as `a / b`, with `a : ℤ` and `b : ℕ`, `b ≠ 0`.

## Examples

* `frac 1 2` and `frac 2 4` are the same rational, because `1 * 4 = 2 * 2`.
* `0 = frac 0 1` and `1 = frac 1 1`.
-/
DefinitionDoc MyRat as "ℚ (MyRat)"

/--
`frac a b` is the rational `a / b`. The denominator `b` is a natural number.
Every rule about `frac` needs `b ≠ 0`. (For `b = 0`, `frac a 0` is just `0`.)

## Examples

* `frac (mk 3 0) 4` is `3/4`.
* `frac (mk 0 1) 2` is `-1/2`.
-/
DefinitionDoc MyRat.frac as "frac"

/--
`nonneg x` means `x ≥ 0`. For a fraction: `nonneg (frac a b) ↔ 0 ≤ a` (theorem `nonneg_frac`).
And `x ≤ y` means `nonneg (y - x)` (theorem `le_iff_nonneg`).

## Examples

* `nonneg (frac (mk 1 0) 2)`, because `0 ≤ mk 1 0`.
* `x ≤ y` unfolds to `nonneg (y - x)`.
-/
DefinitionDoc MyRat.nonneg as "nonneg"

/--
`frac_eq hb hd : frac a b = frac c d ↔ a * mk d 0 = c * mk b 0`, for `hb : b ≠ 0` and `hd : d ≠ 0`.
Cross-multiply to compare fractions.

## Examples

* Goal `frac a b = frac c d`: `rw [frac_eq hb hd]`.
* `h : frac a b = frac c d`: `rw [frac_eq hb hd] at h`.
-/
TheoremDoc MyRat.frac_eq as "frac_eq" in "ℚ"

/--
`exists_frac x : ∃ a b, b ≠ 0 ∧ x = frac a b`. Every rational is a fraction.

## Examples

* `obtain ⟨a, b, hb, rfl⟩ := exists_frac x` replaces `x` by `frac a b` and gives `hb : b ≠ 0`.
* `obtain ⟨a, b, hb, h⟩ := exists_frac x` gives `h : x = frac a b` instead.
-/
TheoremDoc MyRat.exists_frac as "exists_frac" in "ℚ"

/--
`zero_def : 0 = frac 0 1` in `ℚ`.

## Examples

* `rw [zero_def]` changes the rational `0` to `frac 0 1`.
* `rw [← zero_def]` changes `frac 0 1` to `0`.
-/
TheoremDoc MyRat.zero_def as "zero_def (ℚ)" in "ℚ"

/--
`frac_add_frac hb hd : frac a b + frac c d = frac (a * mk d 0 + c * mk b 0) (b * d)`.

## Examples

* `rw [frac_add_frac hb hd]` adds `frac a b + frac c d`.
* `rw [frac_add_frac hb hb]` adds two fractions with denominator `b`.
-/
TheoremDoc MyRat.frac_add_frac as "frac_add_frac" in "ℚ"

/--
`neg_frac a b : -frac a b = frac (-a) b`.

## Examples

* `rw [neg_frac]` moves the minus into the numerator.
* `neg_frac 1 2 : -frac 1 2 = frac (-1) 2`.
-/
TheoremDoc MyRat.neg_frac as "neg_frac" in "ℚ"

/--
`sub_eq_add_neg x y : x - y = x + -y`. This is how `-` between two rationals is defined.

## Examples

* `rw [sub_eq_add_neg]` changes the first `x - y` to `x + -y`.
* `rw [← sub_eq_add_neg]` goes back.
-/
TheoremDoc MyRat.sub_eq_add_neg as "sub_eq_add_neg" in "ℚ"

/--
`le_iff_nonneg x y : x ≤ y ↔ nonneg (y - x)`. This is the definition of `≤` on `ℚ`.

## Examples

* Goal `x ≤ y`: `rw [le_iff_nonneg]` changes it to `nonneg (y - x)`.
* `rw [le_iff_nonneg] at h₁ h₂ ⊢` unfolds `≤` in three places.
-/
TheoremDoc MyRat.le_iff_nonneg as "le_iff_nonneg" in "ℚ"

/--
`nonneg_frac hb : nonneg (frac a b) ↔ 0 ≤ a`, for `hb : b ≠ 0`.

## Examples

* Goal `nonneg (frac a b)`: `rw [nonneg_frac hb]` changes it to `0 ≤ a`.
* `h : nonneg (frac a b)`: `rw [nonneg_frac hb] at h`.
-/
TheoremDoc MyRat.nonneg_frac as "nonneg_frac" in "ℚ"

/--
`frac_scale a b c hb hc : frac a b = frac (a * mk c 0) (b * c)`. Multiply top and bottom by `c`.

## Examples

* `frac_scale a b 2 hb h2 : frac a b = frac (a * mk 2 0) (b * 2)`.
* `rw [frac_scale a b c hb hc]` scales `frac a b`.
-/
TheoremDoc MyRat.frac_scale as "frac_scale" in "ℚ"

/--
`add_comm x y : x + y = y + x` for rationals.

## Examples

* `rw [add_comm]` swaps the first sum it finds.
* `rw [add_comm x y]` changes exactly `x + y`.
-/
TheoremDoc MyRat.add_comm as "add_comm (ℚ)" in "ℚ"

/--
`add_zero x : x + 0 = x` for rationals.

## Examples

* `rw [add_zero]` removes `+ 0`.
* `add_zero (frac 1 2) : frac 1 2 + 0 = frac 1 2`.
-/
TheoremDoc MyRat.add_zero as "add_zero (ℚ)" in "ℚ"

/--
`add_neg x : x + -x = 0` for rationals.

## Examples

* `rw [add_neg]` changes `y + -y` to `0`.
* `add_neg (frac 1 2) : frac 1 2 + -frac 1 2 = 0`.
-/
TheoremDoc MyRat.add_neg as "add_neg (ℚ)" in "ℚ"

/--
`neg_add x y : -(x + y) = -x + -y` for rationals.

## Examples

* `rw [neg_add]` spreads a minus over a sum.
* Useful with `sub_eq_add_neg`: `a - (b + c) = a + (-b + -c)`.
-/
TheoremDoc MyRat.neg_add as "neg_add (ℚ)" in "ℚ"

/--
`add_assoc x y z : x + y + z = x + (y + z)` for rationals. After this level, `ac_rfl` works for `+` on `ℚ`.

## Examples

* `rw [add_assoc]` moves brackets to the right.
* `rw [← add_assoc]` moves brackets to the left.
-/
TheoremDoc MyRat.add_assoc as "add_assoc (ℚ)" in "ℚ"

/--
`nonneg_add x y : nonneg x → nonneg y → nonneg (x + y)`.

## Examples

* `exact nonneg_add x y hx hy` proves `nonneg (x + y)`.
* The key step behind `le_trans` and `add_le_add`.
-/
TheoremDoc MyRat.nonneg_add as "nonneg_add (ℚ)" in "ℚ"

/--
`le_refl x : x ≤ x` for rationals.

## Examples

* `exact le_refl x` proves `x ≤ x`.
* `le_refl 0 : (0 : ℚ) ≤ 0`.
-/
TheoremDoc MyRat.le_refl as "le_refl (ℚ)" in "ℚ"

/--
`sub_add_sub x y z : z - y + (y - x) = z - x`.

## Examples

* `rw [← sub_add_sub x y z]` splits `z - x` at `y`.
* `sub_add_sub 0 1 2 : 2 - 1 + (1 - 0) = 2 - 0`.
-/
TheoremDoc MyRat.sub_add_sub as "sub_add_sub" in "ℚ"

/--
`le_trans x y z : x ≤ y → y ≤ z → x ≤ z` for rationals.

## Examples

* `exact le_trans x y z h₁ h₂` proves `x ≤ z`.
* Goal `x ≤ z`: `apply le_trans x y z` gives the goals `x ≤ y` and `y ≤ z`.
-/
TheoremDoc MyRat.le_trans as "le_trans (ℚ)" in "ℚ"

/--
`add_le_add a b c d : a ≤ b → c ≤ d → a + c ≤ b + d`.

## Examples

* `exact add_le_add a b c d h₁ h₂` proves `a + c ≤ b + d`.
* With `c = d`: add the same number to both sides.
-/
TheoremDoc MyRat.add_le_add as "add_le_add (ℚ)" in "ℚ"
