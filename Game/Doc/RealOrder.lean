import GameServer

/-! # Documentation for the order of `ℝ` -/

/--
`neg_eps_le k : -frac 1 (succ k) ≤ 0`.

## Examples

* `exact MyRat.neg_eps_le k` closes a goal `-frac 1 (succ k) ≤ 0`.
* `MyRat.le_trans _ 0 _ (MyRat.neg_eps_le k) h` with `h : 0 ≤ s n` gives `-frac 1 (succ k) ≤ s n`.
-/
TheoremDoc MyRat.neg_eps_le as "neg_eps_le" in "ℚ"

/--
`nonneg x` means `x ≥ 0`. For `x = ofSeq s hs`: for every `k` there is `N` with
`-frac 1 (succ k) ≤ s n` for all `n ≥ N`.

## Examples

* `nonneg (ofSeq s hs) ↔ ∀ k, ∃ N, ∀ n, N ≤ n → -frac 1 (succ k) ≤ s n` (`nonneg_ofSeq`).
* `x ≤ y` means `nonneg (y - x)` (`le_iff_nonneg`).
-/
DefinitionDoc MyReal.nonneg as "nonneg (ℝ)"

/--
`nonneg_ofSeq : nonneg (ofSeq s hs) ↔ ∀ k, ∃ N, ∀ n, N ≤ n → -frac 1 (succ k) ≤ s n`.

## Examples

* Goal `nonneg (ofSeq s hs)`: `rw [nonneg_ofSeq]`, then `intro k`, `use N`, `intro n hn`.
* `h : nonneg (ofSeq s hs)`: `rw [nonneg_ofSeq] at h`, then `obtain ⟨N, hN⟩ := h k`.
-/
TheoremDoc MyReal.nonneg_ofSeq as "nonneg_ofSeq" in "≤ℝ"

/--
`le_iff_nonneg x y : x ≤ y ↔ nonneg (y - x)` for reals. This is the definition of `≤` on `ℝ`.

## Examples

* `rw [le_iff_nonneg]` turns the first `x ≤ y` into `nonneg (y - x)`.
* `rw [le_iff_nonneg] at h ⊢` unfolds a hypothesis and the goal.
-/
TheoremDoc MyReal.le_iff_nonneg as "le_iff_nonneg (ℝ)" in "≤ℝ"

/--
`le_refl x : x ≤ x` for reals.

## Examples

* `exact MyReal.le_refl x` proves `x ≤ x`.
* `MyReal.add_le_add _ _ _ _ h (MyReal.le_refl c)` adds `c` on the right of `h`.
-/
TheoremDoc MyReal.le_refl as "le_refl (ℝ)" in "≤ℝ"

/--
`nonneg_add x y : nonneg x → nonneg y → nonneg (x + y)` for reals.

## Examples

* `exact nonneg_add (z - y) (y - x) h1 h2` proves `nonneg (z - y + (y - x))`.
* Used to prove `le_trans` for reals.
-/
TheoremDoc MyReal.nonneg_add as "nonneg_add (ℝ)" in "≤ℝ"

/--
`le_trans x y z : x ≤ y → y ≤ z → x ≤ z` for reals.

## Examples

* `exact MyReal.le_trans x y z h1 h2` chains two inequalities.
* `MyReal.le_trans _ (abs x) _ h1 h2` goes through `abs x`.
-/
TheoremDoc MyReal.le_trans as "le_trans (ℝ)" in "≤ℝ"

/--
`add_le_add_right a b c : a ≤ b → a + c ≤ b + c` for reals.

## Examples

* `MyReal.add_le_add_right _ _ (-L) h` turns `h : a ≤ b` into `a + -L ≤ b + -L`.
* `MyReal.add_le_add_right x y 1 h : x + 1 ≤ y + 1`.
-/
TheoremDoc MyReal.add_le_add_right as "add_le_add_right (ℝ)" in "≤ℝ"

/--
`le_antisymm x y : x ≤ y → y ≤ x → x = y` for reals.

## Examples

* Goal `L = M`: `apply MyReal.le_antisymm`, then prove `L ≤ M` and `M ≤ L`.
* `MyReal.le_antisymm x 0 h1 h2 : x = 0`.
-/
TheoremDoc MyReal.le_antisymm as "le_antisymm (ℝ)" in "≤ℝ"

/--
`by_cases h : P` splits the proof into two cases: one with `h : P`, one with `h : ¬ P`.

It uses that every statement is true or false.

## Examples

* `by_cases h : nonneg a` gives a goal with `h : nonneg a` and a goal with `h : ¬ nonneg a`.
* `by_cases hp : P` in a proof of `¬ (P → Q) → P ∧ ¬ Q`.
-/
TacticDoc by_cases

/--
`not_exists α P : ¬ (∃ x, P x) → ∀ x, ¬ P x`.

## Examples

* `have h2 := MyLogic.not_exists _ _ h M` turns `h : ¬ ∃ N, Q N` into `h2 : ¬ Q M`.
* `MyLogic.not_exists _ _ h` is `∀ x, ¬ P x`.
-/
TheoremDoc MyLogic.not_exists as "not_exists" in "logic"

/--
`not_forall α P : ¬ (∀ x, P x) → ∃ x, ¬ P x`.

## Examples

* `obtain ⟨k, hk⟩ := MyLogic.not_forall _ _ h` turns `h : ¬ ∀ k, Q k` into `hk : ¬ Q k`.
* `obtain ⟨n, hn⟩ := MyLogic.not_forall _ _ h` for `h : ¬ ∀ n, M ≤ n → P n`.
-/
TheoremDoc MyLogic.not_forall as "not_forall" in "logic"

/--
`not_imp P Q : ¬ (P → Q) → P ∧ ¬ Q`.

## Examples

* `obtain ⟨h1, h2⟩ := MyLogic.not_imp _ _ h` turns `h : ¬ (M ≤ n → P n)` into `h1 : M ≤ n`, `h2 : ¬ P n`.
* `MyLogic.not_imp P Q h : P ∧ ¬ Q`.
-/
TheoremDoc MyLogic.not_imp as "not_imp" in "logic"

/--
`le_total a b : a ≤ b ∨ b ≤ a` for naturals.

## Examples

* `obtain h | h := MyNat.le_total b a` gives the cases `b ≤ a` and `a ≤ b`.
* `MyNat.le_total 0 n : 0 ≤ n ∨ n ≤ 0`.
-/
TheoremDoc MyNat.le_total as "le_total" in "≤"

/--
`nonneg_or_nonneg_neg x : 0 ≤ x ∨ 0 ≤ -x` for integers.

## Examples

* `obtain h | h := MyInt.nonneg_or_nonneg_neg a` splits by the sign of `a`.
* `MyInt.nonneg_or_nonneg_neg (mk 2 5) : 0 ≤ mk 2 5 ∨ 0 ≤ -mk 2 5`.
-/
TheoremDoc MyInt.nonneg_or_nonneg_neg as "nonneg_or_nonneg_neg (ℤ)" in "ℤ"

/--
`nonneg_or_nonneg_neg x : nonneg x ∨ nonneg (-x)` for rationals.

## Examples

* `obtain h | h := MyRat.nonneg_or_nonneg_neg a` splits by the sign of `a`.
* With `h : ¬ nonneg a`, the first case is impossible, so you get `nonneg (-a)`.
-/
TheoremDoc MyRat.nonneg_or_nonneg_neg as "nonneg_or_nonneg_neg (ℚ)" in "ℚ"

/--
`le_total a b : a ≤ b ∨ b ≤ a` for rationals.

## Examples

* `obtain h | h := MyRat.le_total a b` compares `a` and `b`.
* With `h : ¬ a ≤ b`, the first case is impossible, so `b ≤ a`.
-/
TheoremDoc MyRat.le_total as "le_total (ℚ)" in "ℚ"

/--
`nonneg_or_nonneg_neg x : nonneg x ∨ nonneg (-x)` for reals.

## Examples

* `obtain h | h := MyReal.nonneg_or_nonneg_neg x` splits by the sign of `x`.
* With `rw [← neg_sub x y]` it gives `le_total` for reals.
-/
TheoremDoc MyReal.nonneg_or_nonneg_neg as "nonneg_or_nonneg_neg (ℝ)" in "≤ℝ"

/--
`le_total x y : x ≤ y ∨ y ≤ x` for reals.

## Examples

* `obtain h | h := MyReal.le_total x y` compares `x` and `y`.
* `MyReal.le_total x 0 : x ≤ 0 ∨ 0 ≤ x`.
-/
TheoremDoc MyReal.le_total as "le_total (ℝ)" in "≤ℝ"

/--
`abs a` is the absolute value `|a|` of a rational: `a` if `a ≥ 0`, else `-a`.

## Examples

* `abs_of_nonneg h : abs a = a` when `h : nonneg a`.
* `abs_of_not_nonneg h : abs a = -a` when `h : ¬ nonneg a`.
-/
DefinitionDoc MyRat.abs as "abs (ℚ)"

/--
`abs_of_nonneg : nonneg a → abs a = a` for rationals.

## Examples

* `rw [abs_of_nonneg h]` with `h : nonneg a`.
* `MyRat.abs_of_nonneg hs0 : MyRat.abs (s n) = s n` with `hs0 : MyRat.nonneg (s n)`.
-/
TheoremDoc MyRat.abs_of_nonneg as "abs_of_nonneg (ℚ)" in "abs"

/--
`abs_of_not_nonneg : ¬ nonneg a → abs a = -a` for rationals.

## Examples

* `rw [abs_of_not_nonneg h]` with `h : ¬ nonneg a`.
* After `by_cases h : nonneg a`, use `abs_of_nonneg h` in the first case and this in the second.
-/
TheoremDoc MyRat.abs_of_not_nonneg as "abs_of_not_nonneg" in "abs"

/--
`abs_nonneg a : nonneg (abs a)` for rationals.

## Examples

* `MyRat.abs_nonneg (s n) : MyRat.nonneg (MyRat.abs (s n))`.
* `MyRat.nonneg_mul _ _ (MyRat.abs_nonneg a) (MyRat.abs_nonneg b)`.
-/
TheoremDoc MyRat.abs_nonneg as "abs_nonneg (ℚ)" in "abs"

/--
`abs_bounds a : a ≤ abs a ∧ -a ≤ abs a` for rationals.

## Examples

* `obtain ⟨h1, h2⟩ := MyRat.abs_bounds a`.
* `(MyRat.abs_bounds (s n)).1 : s n ≤ MyRat.abs (s n)`.
-/
TheoremDoc MyRat.abs_bounds as "abs_bounds (ℚ)" in "abs"

/--
`abs_le c d : c ≤ d → -c ≤ d → abs c ≤ d` for rationals.

## Examples

* Goal `abs c ≤ d`: `apply MyRat.abs_le` leaves `c ≤ d` and `-c ≤ d`.
* `MyRat.abs_le _ _ h1 h2` with both bounds.
-/
TheoremDoc MyRat.abs_le as "abs_le (ℚ)" in "abs"

/--
`abs_add a b : abs (a + b) ≤ abs a + abs b`. The triangle inequality for rationals.

## Examples

* `MyRat.abs_add (s n) (t n)` bounds the terms of a sum.
* `exact MyRat.abs_add _ _` closes a goal `abs (a + b) ≤ abs a + abs b`.
-/
TheoremDoc MyRat.abs_add as "abs_add (ℚ)" in "abs"

/--
`nonneg_of_eventually s hs : (∃ N, ∀ n, N ≤ n → nonneg (s n)) → nonneg (ofSeq s hs)`.

## Examples

* Goal `nonneg (ofSeq s hs)`: `apply nonneg_of_eventually`, then `use 0`, `intro n hn`.
* If only the terms after `N` are `≥ 0`, use `use N`.
-/
TheoremDoc MyReal.nonneg_of_eventually as "nonneg_of_eventually" in "≤ℝ"

/--
`le_of_eventually s t hs ht : (∃ N, ∀ n, N ≤ n → s n ≤ t n) → ofSeq s hs ≤ ofSeq t ht`.

## Examples

* Goal `ofSeq s hs ≤ ofSeq t ht`: `apply le_of_eventually`, `use 0`, `intro n hn`.
* Goal `abs (ofSeq s hs) ≤ ofRat e`: rewrite with `ofSeq_abs`, `ofRat_def` first.
-/
TheoremDoc MyReal.le_of_eventually as "le_of_eventually" in "≤ℝ"

/--
`absSeq s` is the sequence `abs (s 0), abs (s 1), …`.

## Examples

* `MyRat.absSeq_apply s n : MyRat.absSeq s n = MyRat.abs (s n)`.
* `abs (ofSeq s hs) = ofSeq (MyRat.absSeq s) _` (`ofSeq_abs`).
-/
DefinitionDoc MyRat.absSeq as "absSeq"

/--
`absSeq_apply s n : absSeq s n = abs (s n)`.

## Examples

* `rw [MyRat.absSeq_apply]` computes the first `absSeq s n`.
* `rw [MyRat.absSeq_apply, MyRat.absSeq_apply]` for two terms.
-/
TheoremDoc MyRat.absSeq_apply as "absSeq_apply" in "abs"

/--
`abs x` is the absolute value `|x|` of a real: `abs` term by term.

## Examples

* `abs (ofSeq s hs) = ofSeq (MyRat.absSeq s) _` (`ofSeq_abs`).
* `abs_of_nonneg x h : abs x = x` when `h : nonneg x`.
-/
DefinitionDoc MyReal.abs as "abs (ℝ)"

/--
`ofSeq_abs : abs (ofSeq s hs) = ofSeq (absSeq s) _`.

## Examples

* `rw [ofSeq_abs]` computes the first absolute value of this form.
* `rw [ofSeq_add, ofSeq_abs]` for `abs (ofSeq s hs + ofSeq t ht)`.
-/
TheoremDoc MyReal.ofSeq_abs as "ofSeq_abs" in "abs"

/--
`abs_of_nonneg x : nonneg x → abs x = x` for reals.

## Examples

* `rw [abs_of_nonneg x h]` replaces `abs x` by `x`.
* `rw [← abs_of_nonneg x h]` replaces `x` by `abs x`.
-/
TheoremDoc MyReal.abs_of_nonneg as "abs_of_nonneg (ℝ)" in "abs"

/--
`nonneg_mul x y : nonneg x → nonneg y → nonneg (x * y)` for reals.

## Examples

* `exact MyReal.nonneg_mul (b - a) c h hc` proves `nonneg ((b - a) * c)`.
* `MyReal.nonneg_mul x x h h : nonneg (x * x)`.
-/
TheoremDoc MyReal.nonneg_mul as "nonneg_mul (ℝ)" in "≤ℝ"

/--
`abs_add x y : abs (x + y) ≤ abs x + abs y`. The triangle inequality for reals.

## Examples

* `MyReal.le_trans _ _ _ (MyReal.abs_add _ _) h` bounds `abs (x + y)` by a bound for `abs x + abs y`.
* `MyReal.abs_add (a n - L) (b n - M)`.
-/
TheoremDoc MyReal.abs_add as "abs_add (ℝ)" in "abs"
