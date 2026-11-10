import GameServer

/-! # Documentation for completeness -/

/--
`choose f hf using h` turns `h : ∀ n, ∃ y, P n y` into a function `f` and
`hf : ∀ n, P n (f n)`. It uses the axiom of choice.

## Examples

* `h : ∀ n, ∃ m, P n m`: `choose f hf using h` gives `f : ℕ → ℕ` and `hf : ∀ n, P n (f n)`.
* `h : ∀ n, ∃ q : ℚ, abs (a n - ofRat q) ≤ eps n`: `choose q hq using h` gives a sequence `q`.
-/
TacticDoc choose

/--
`abs_sub_le x y z : abs (x - z) ≤ abs (x - y) + abs (y - z)`. The triangle inequality for distances.

## Examples

* `abs_sub_le (a n) (b n) L : abs (a n - L) ≤ abs (a n - b n) + abs (b n - L)`.
* `MyReal.le_trans _ _ _ (abs_sub_le x y z) h` bounds the distance from `x` to `z`.
-/
TheoremDoc MyReal.abs_sub_le as "abs_sub_le" in "abs"

/--
`ratSeq q` is the sequence `ofRat (q 0), ofRat (q 1), …`: the rationals `q n` seen as reals.

## Examples

* `ratSeq_apply q n : ratSeq q n = ofRat (q n)`.
* `Tendsto (ratSeq q) (ofSeq q hq)` (`tendsto_ratSeq`).
-/
DefinitionDoc MyReal.ratSeq as "ratSeq"

/--
`ratSeq_apply q n : ratSeq q n = ofRat (q n)`.

## Examples

* `rw [ratSeq_apply]` computes the first `ratSeq q n`.
* `rw [ratSeq_apply, ratSeq_apply] at h` for `abs (ratSeq q m - ratSeq q n)`.
-/
TheoremDoc MyReal.ratSeq_apply as "ratSeq_apply" in "limℝ"

/--
`tendsto_ratSeq q hq : Tendsto (ratSeq q) (ofSeq q hq)`. A real is the limit of its own rationals.

## Examples

* `obtain ⟨N, hN⟩ := tendsto_ratSeq s hs k`.
* `tendsto_ratSeq q hc` gives the limit in the proof of completeness.
-/
TheoremDoc MyReal.tendsto_ratSeq as "tendsto_ratSeq" in "limℝ"

/--
`exists_rat_near x k : ∃ q : ℚ, abs (x - ofRat q) ≤ eps k`. There is a rational next to every real.

## Examples

* `obtain ⟨q, hq⟩ := exists_rat_near x k`.
* `exists_rat_near (a n) n` gives a rational within `1/(n+1)` of `a n`.
-/
TheoremDoc MyReal.exists_rat_near as "exists_rat_near" in "limℝ"

/--
`le_of_ofRat_le a b : ofRat a ≤ ofRat b → ∀ k, a ≤ b + frac 1 (succ k)`.

## Examples

* `le_of_ofRat_le _ _ h k` brings `h : ofRat a ≤ ofRat b` back to `ℚ`, up to `1/(k+1)`.
* `le_of_ofRat_le _ _ d (succ K + K)` pays half of `1/(K+1)`.
-/
TheoremDoc MyReal.le_of_ofRat_le as "le_of_ofRat_le" in "limℝ"

/--
`IsCauchy a` (for `a : ℕ → ℝ`): for every `k` there is `N` with `abs (a m - a n) ≤ eps k`
for all `m, n ≥ N`.

## Examples

* Goal `IsCauchy a`: `intro k`, `use N`, `intro m n hm hn`.
* `h : IsCauchy a`: `obtain ⟨N, hN⟩ := h k`, then `hN m n hm hn`.
-/
DefinitionDoc MyReal.IsCauchy as "IsCauchy (ℝ)"

/--
`cauchy_ratSeq a q : IsCauchy a → (∀ n, abs (a n - ofRat (q n)) ≤ eps n) → IsCauchy (ratSeq q)`.

## Examples

* `cauchy_ratSeq a q ha hq` says the chosen rationals are Cauchy in `ℝ`.
* Together with `rat_cauchy` they are Cauchy in `ℚ`.
-/
TheoremDoc MyReal.cauchy_ratSeq as "cauchy_ratSeq" in "limℝ"

/--
`rat_cauchy q : IsCauchy (ratSeq q) → MyRat.IsCauchy q`. Cauchy in `ℝ` means Cauchy in `ℚ`.

## Examples

* `rat_cauchy q h : MyRat.IsCauchy q`.
* `ofSeq q (rat_cauchy q h)` is a real number.
-/
TheoremDoc MyReal.rat_cauchy as "rat_cauchy" in "limℝ"

/--
`tendsto_of_near a b L : Tendsto b L → (∀ n, abs (a n - b n) ≤ eps n) → Tendsto a L`.

## Examples

* `tendsto_of_near a (ratSeq q) L h hq` moves a limit from `ratSeq q` to `a`.
* With `b = const L`, a sequence within `1/(n+1)` of `L` tends to `L`.
-/
TheoremDoc MyReal.tendsto_of_near as "tendsto_of_near" in "limℝ"

/--
`complete a : IsCauchy a → ∃ L, Tendsto a L`. Every Cauchy sequence of reals converges.

## Examples

* `obtain ⟨L, hL⟩ := complete a ha`.
* `complete (ratSeq q) h` gives a limit for the rationals `q n` seen in `ℝ`.
-/
TheoremDoc MyReal.complete as "complete" in "limℝ"
