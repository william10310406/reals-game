import GameServer

/-! # Documentation for the arithmetic of `ℝ` -/

/--
`mul_comm x y : x * y = y * x` for rationals.

## Examples

* `rw [MyRat.mul_comm]` swaps the first product of rationals.
* `MyRat.mul_comm (s n) (t n) : s n * t n = t n * s n`.
-/
TheoremDoc MyRat.mul_comm as "mul_comm (ℚ)" in "ℚ"

/--
`mul_assoc x y z : x * y * z = x * (y * z)` for rationals.

## Examples

* `rw [MyRat.mul_assoc]` moves the brackets of the first triple product to the right.
* After this level, `ac_rfl` can reorder products of rationals.
-/
TheoremDoc MyRat.mul_assoc as "mul_assoc (ℚ)" in "ℚ"

/--
`one_def : (1 : ℚ) = frac 1 1`. The rational `1` as a fraction.

## Examples

* `rw [one_def]` turns `x * 1` into `x * frac 1 1`.
* Then `frac_mul_frac hb MyNat.one_ne_zero` can multiply.
-/
TheoremDoc MyRat.one_def as "one_def (ℚ)" in "ℚ"

/--
`mul_one x : x * 1 = x` for rationals.

## Examples

* `rw [MyRat.mul_one]` removes a `* 1`.
* `MyRat.mul_one (s n) : s n * 1 = s n`.
-/
TheoremDoc MyRat.mul_one as "mul_one (ℚ)" in "ℚ"

/--
`mul_add x y z : x * (y + z) = x * y + x * z` for rationals.

## Examples

* `rw [MyRat.mul_add]` multiplies out the first bracket `x * (y + z)`.
* `MyRat.mul_add (s n) (t n) (u n)` is the law for the terms of three sequences.
-/
TheoremDoc MyRat.mul_add as "mul_add (ℚ)" in "ℚ"

/--
`close_of_eq s t : (∀ n, s n = t n) → Close s t`. Sequences with equal terms are close.

## Examples

* Goal `Close s t`: `apply MyRat.close_of_eq`, then `intro n` and prove `s n = t n`.
* Goal `ofSeq s hs = ofSeq t ht`: `rw [ofSeq_eq]`, then `apply MyRat.close_of_eq`.
-/
TheoremDoc MyRat.close_of_eq as "close_of_eq" in "ℚ"

/--
`add_assoc x y z : x + y + z = x + (y + z)` for reals.

## Examples

* `rw [MyReal.add_assoc]` moves the brackets of the first triple sum to the right.
* After this level, `ac_rfl` can reorder sums of reals.
-/
TheoremDoc MyReal.add_assoc as "add_assoc (ℝ)" in "ℝ"

/--
`ofRat q` is the rational `q` as a real number: the constant sequence `q, q, q, …`.

## Examples

* `ofRat_def q : ofRat q = ofSeq (MyRat.const q) (MyRat.const_cauchy q)`.
* `(0 : ℝ) = ofRat 0` (`zero_def`) and `(1 : ℝ) = ofRat 1` (`one_def`).
-/
DefinitionDoc MyReal.ofRat as "ofRat"

/--
`ofRat_def q : ofRat q = ofSeq (MyRat.const q) (MyRat.const_cauchy q)`.

## Examples

* `rw [ofRat_def]` writes the first `ofRat q` as a sequence.
* `rw [zero_def, ofRat_def]` writes `0 : ℝ` as the sequence `0, 0, 0, …`.
-/
TheoremDoc MyReal.ofRat_def as "ofRat_def" in "ℝ"

/--
`zero_def : (0 : ℝ) = ofRat 0`.

## Examples

* `rw [zero_def]` replaces `0 : ℝ` by `ofRat 0`.
* `rw [zero_def, ofRat_def]` makes it a sequence.
-/
TheoremDoc MyReal.zero_def as "zero_def (ℝ)" in "ℝ"

/--
`add_zero x : x + 0 = x` for reals.

## Examples

* `rw [MyReal.add_zero]` removes a `+ 0`.
* `rw [add_neg, add_zero]` simplifies `z + (y + -y)` to `z`.
-/
TheoremDoc MyReal.add_zero as "add_zero (ℝ)" in "ℝ"

/--
`zero_add x : 0 + x = x` for reals.

## Examples

* `rw [MyReal.zero_add]` removes a `0 +`.
* `MyReal.zero_add (-x) : 0 + -x = -x`.
-/
TheoremDoc MyReal.zero_add as "zero_add (ℝ)" in "ℝ"

/--
`negSeq s` is the sequence `-s 0, -s 1, …`.

## Examples

* `MyRat.negSeq_apply s n : MyRat.negSeq s n = -s n`.
* `-ofSeq s hs = ofSeq (MyRat.negSeq s) _` (`ofSeq_neg`).
-/
DefinitionDoc MyRat.negSeq as "negSeq"

/--
`negSeq_apply s n : negSeq s n = -s n`.

## Examples

* `rw [MyRat.negSeq_apply]` computes the first `negSeq s n`.
* `rw [MyRat.negSeq_apply, MyRat.negSeq_apply]` for `negSeq (negSeq s) n`.
-/
TheoremDoc MyRat.negSeq_apply as "negSeq_apply" in "ℚ"

/--
`ofSeq_neg : -ofSeq s hs = ofSeq (negSeq s) _`. Reals are negated term by term.

## Examples

* `rw [ofSeq_neg]` computes the first negative of this form.
* `rw [ofSeq_neg, ofSeq_add]` computes `ofSeq s hs + -ofSeq t ht`.
-/
TheoremDoc MyReal.ofSeq_neg as "ofSeq_neg" in "ℝ"

/--
`add_neg x : x + -x = 0` for reals.

## Examples

* `rw [MyReal.add_neg]` replaces `y + -y` by `0`.
* `MyReal.add_neg (ofRat q) : ofRat q + -ofRat q = 0`.
-/
TheoremDoc MyReal.add_neg as "add_neg (ℝ)" in "ℝ"

/--
`neg_add x y : -(x + y) = -x + -y` for reals.

## Examples

* `rw [MyReal.neg_add]` splits the first negative of a sum.
* `rw [sub_eq_add_neg, neg_add]` turns `-(y - x)` into `-y + -(-x)`.
-/
TheoremDoc MyReal.neg_add as "neg_add (ℝ)" in "ℝ"

/--
`neg_neg x : -(-x) = x` for reals.

## Examples

* `rw [MyReal.neg_neg]` removes a double minus.
* `MyReal.neg_neg (ofRat q) : -(-ofRat q) = ofRat q`.
-/
TheoremDoc MyReal.neg_neg as "neg_neg (ℝ)" in "ℝ"

/--
`sub_eq_add_neg x y : x - y = x + -y` for reals. This is the definition of `-` between reals.

## Examples

* `rw [MyReal.sub_eq_add_neg]` writes the first difference as a sum.
* `rw [← MyReal.sub_eq_add_neg]` turns `x + -y` back into `x - y`.
-/
TheoremDoc MyReal.sub_eq_add_neg as "sub_eq_add_neg (ℝ)" in "ℝ"

/--
`sub_add_sub x y z : z - y + (y - x) = z - x` for reals.

## Examples

* `rw [← MyReal.sub_add_sub x y z]` splits `z - x` at `y`.
* With `nonneg_add` it gives `le_trans` for reals.
-/
TheoremDoc MyReal.sub_add_sub as "sub_add_sub (ℝ)" in "ℝ"

/--
`neg_sub x y : -(y - x) = x - y` for reals.

## Examples

* `rw [MyReal.neg_sub]` turns `-(y - x)` into `x - y`.
* `rw [← MyReal.neg_sub x y]` turns `x - y` into `-(y - x)`.
-/
TheoremDoc MyReal.neg_sub as "neg_sub (ℝ)" in "ℝ"

/--
`mulSeq s t` is the sequence `s 0 * t 0, s 1 * t 1, …`.

## Examples

* `MyRat.mulSeq_apply s t n : MyRat.mulSeq s t n = s n * t n`.
* `ofSeq s hs * ofSeq t ht = ofSeq (MyRat.mulSeq s t) _` (`ofSeq_mul`).
-/
DefinitionDoc MyRat.mulSeq as "mulSeq"

/--
`mulSeq_apply s t n : mulSeq s t n = s n * t n`.

## Examples

* `rw [MyRat.mulSeq_apply]` computes the first `mulSeq s t n`.
* `rw [MyRat.mulSeq_apply, MyRat.mulSeq_apply]` for both sides of an equation.
-/
TheoremDoc MyRat.mulSeq_apply as "mulSeq_apply" in "ℚ"

/--
`ofSeq_mul : ofSeq s hs * ofSeq t ht = ofSeq (mulSeq s t) _`. Reals multiply term by term.

## Examples

* `rw [ofSeq_mul]` multiplies the first two reals of this form.
* `rw [ofSeq_mul, ofSeq_mul, ofSeq_eq]` for both sides of an equation.
-/
TheoremDoc MyReal.ofSeq_mul as "ofSeq_mul" in "ℝ"

/--
`mul_comm x y : x * y = y * x` for reals.

## Examples

* `rw [MyReal.mul_comm]` swaps the first product of reals.
* `rw [MyReal.mul_comm (b - a)]` swaps the product that starts with `b - a`.
-/
TheoremDoc MyReal.mul_comm as "mul_comm (ℝ)" in "ℝ"

/--
`mul_assoc x y z : x * y * z = x * (y * z)` for reals.

## Examples

* `rw [MyReal.mul_assoc]` moves the brackets of the first triple product to the right.
* After this level, `ac_rfl` can reorder products of reals.
-/
TheoremDoc MyReal.mul_assoc as "mul_assoc (ℝ)" in "ℝ"

/--
`one_def : (1 : ℝ) = ofRat 1`.

## Examples

* `rw [one_def]` replaces `1 : ℝ` by `ofRat 1`.
* `rw [one_def, ofRat_def]` makes it the sequence `1, 1, 1, …`.
-/
TheoremDoc MyReal.one_def as "one_def (ℝ)" in "ℝ"

/--
`mul_one x : x * 1 = x` for reals.

## Examples

* `rw [MyReal.mul_one]` removes a `* 1`.
* `MyReal.mul_one (x + y) : (x + y) * 1 = x + y`.
-/
TheoremDoc MyReal.mul_one as "mul_one (ℝ)" in "ℝ"

/--
`mul_add x y z : x * (y + z) = x * y + x * z` for reals.

## Examples

* `rw [MyReal.mul_add]` multiplies out the first bracket `x * (y + z)`.
* `rw [MyReal.mul_comm (y + z), MyReal.mul_add]` multiplies out `(y + z) * x`.
-/
TheoremDoc MyReal.mul_add as "mul_add (ℝ)" in "ℝ"

/--
`ofRat_add a b : ofRat (a + b) = ofRat a + ofRat b`. `ℚ` and `ℝ` add the same way.

## Examples

* `rw [ofRat_add]` splits `ofRat (a + b)`.
* `rw [← ofRat_add]` turns `ofRat a + ofRat b` into `ofRat (a + b)`.
-/
TheoremDoc MyReal.ofRat_add as "ofRat_add" in "ℝ"

/--
`ofRat_mul a b : ofRat (a * b) = ofRat a * ofRat b`. `ℚ` and `ℝ` multiply the same way.

## Examples

* `rw [ofRat_mul]` splits `ofRat (a * b)`.
* `rw [← ofRat_mul]` turns `ofRat a * ofRat b` into `ofRat (a * b)`.
-/
TheoremDoc MyReal.ofRat_mul as "ofRat_mul" in "ℝ"
