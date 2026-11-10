import GameServer

/-!
# Documentation for sequences and reals
-/

/--
`const c` is the constant sequence `c, c, c, ...`.

## Examples

* `const c 5 = c` (theorem `const_apply`).
* `IsCauchy (const c)` (theorem `const_cauchy`).
-/
DefinitionDoc MyRat.const as "const"

/--
`addSeq s t` is the sequence `s 0 + t 0, s 1 + t 1, ...`.

## Examples

* `addSeq s t n = s n + t n` (theorem `addSeq_apply`).
* Real addition adds sequences with `addSeq`.
-/
DefinitionDoc MyRat.addSeq as "addSeq"

/--
`IsCauchy s`: for every `k` there is `N` such that `s m - s n ≤ frac 1 (succ k)` for all `m n ≥ N`.

## Examples

* Goal `IsCauchy s`: start with `intro k`, then `use N`, then `intro m n hm hn`.
* `hs : IsCauchy s`: `obtain ⟨N, hN⟩ := hs k`, then `hN m n hm hn`.
-/
DefinitionDoc MyRat.IsCauchy as "IsCauchy"

/--
`Close s t`: for every `k` there is `N` such that `s n - t n ≤ frac 1 (succ k)` and
`t n - s n ≤ frac 1 (succ k)` for all `n ≥ N`.

## Examples

* Goal `Close s t`: `intro k`, `use N`, `intro n hn`, then `constructor`.
* `h : Close s t`: `obtain ⟨N, hN⟩ := h k`, then `obtain ⟨h1, h2⟩ := hN n hn`.
-/
DefinitionDoc MyRat.Close as "Close"

/--
`MyReal` (written `ℝ`) is our type of real numbers: Cauchy sequences of rationals,
where close sequences are the same real.

## Examples

* `ofSeq (const c) (const_cauchy c)` is the rational `c` as a real.
* Every real is `ofSeq s hs` (theorem `exists_ofSeq`).
-/
DefinitionDoc MyReal as "ℝ (MyReal)"

/--
`ofSeq s hs` is the real number of the Cauchy sequence `s` (`hs : IsCauchy s`).

## Examples

* `ofSeq s hs = ofSeq t ht ↔ Close s t` (theorem `ofSeq_eq`).
* `ofSeq s hs + ofSeq t ht = ofSeq (addSeq s t) _` (theorem `ofSeq_add`).
-/
DefinitionDoc MyReal.ofSeq as "ofSeq"

/--
`const_apply c n : const c n = c`.

## Examples

* `rw [const_apply]` replaces the first `const c n` by `c`.
* `const_apply 0 n : const 0 n = 0`.
-/
TheoremDoc MyRat.const_apply as "const_apply" in "ℚ"

/--
`addSeq_apply s t n : addSeq s t n = s n + t n`.

## Examples

* `rw [addSeq_apply]` computes the first `addSeq s t n`.
* `rw [addSeq_apply, addSeq_apply]` computes two terms.
-/
TheoremDoc MyRat.addSeq_apply as "addSeq_apply" in "ℚ"

/--
`ofSeq_eq : ofSeq s hs = ofSeq t ht ↔ Close s t`. Two reals are equal when their sequences are close.

## Examples

* Goal `ofSeq s hs = ofSeq t ht`: `rw [ofSeq_eq]`.
* `h : ofSeq s hs = ofSeq t ht`: `rw [ofSeq_eq] at h` gives `h : Close s t`.
-/
TheoremDoc MyReal.ofSeq_eq as "ofSeq_eq" in "ℝ"

/--
`exists_ofSeq x : ∃ s hs, x = ofSeq s hs`. Every real comes from a Cauchy sequence.

## Examples

* `obtain ⟨s, hs, rfl⟩ := exists_ofSeq x` replaces `x` by `ofSeq s hs`.
* `obtain ⟨s, hs, h⟩ := exists_ofSeq x` gives `h : x = ofSeq s hs`.
-/
TheoremDoc MyReal.exists_ofSeq as "exists_ofSeq" in "ℝ"

/--
`ofSeq_add : ofSeq s hs + ofSeq t ht = ofSeq (addSeq s t) _`. Reals add term by term.

## Examples

* `rw [ofSeq_add]` adds the first two reals of this form.
* `rw [ofSeq_add, ofSeq_add]` for both sides of an equation.
-/
TheoremDoc MyReal.ofSeq_add as "ofSeq_add" in "ℝ"

/--
`le_add_right a b : a ≤ a + b` in `ℕ`.

## Examples

* `MyNat.le_add_right N1 N2 : N1 ≤ N1 + N2`.
* With `le_trans`: from `N1 + N2 ≤ n` get `N1 ≤ n`.
-/
TheoremDoc MyNat.le_add_right as "le_add_right" in "≤"

/--
`succ_ne_zero n : succ n ≠ 0`.

## Examples

* `MyNat.succ_ne_zero k` is the proof needed for `frac 1 (succ k)`.
* `nonneg_frac (MyNat.succ_ne_zero k)`.
-/
TheoremDoc MyNat.succ_ne_zero as "succ_ne_zero" in "ℕ"

/--
`neg_zero : -0 = 0` in `ℚ`.

## Examples

* `rw [neg_zero]` changes `-0` to `0`.
* `x - 0`: `rw [sub_eq_add_neg, neg_zero, add_zero]` gives `x`.
-/
TheoremDoc MyRat.neg_zero as "neg_zero (ℚ)" in "ℚ"

/--
`eps_nonneg k : 0 ≤ frac 1 (succ k)`. Our small numbers are not negative.

## Examples

* `exact eps_nonneg k` proves `0 ≤ frac 1 (succ k)`.
* After `rw [sub_eq_add_neg, add_neg]`, a goal `0 ≤ frac 1 (succ k)` needs it.
-/
TheoremDoc MyRat.eps_nonneg as "eps_nonneg" in "ℚ"

/--
`half m hm : frac 1 (m + m) + frac 1 (m + m) = frac 1 m`. Two halves make a whole.

## Examples

* `rw [← half (succ k) (MyNat.succ_ne_zero k)]` splits `frac 1 (succ k)`.
* Then `rw [MyNat.add_succ]` writes `succ k + succ k` as `succ (succ k + k)`.
-/
TheoremDoc MyRat.half as "half" in "ℚ"

/--
`const_cauchy c : IsCauchy (const c)`.

## Examples

* `ofSeq (const c) (const_cauchy c)` is the real number `c`.
* `const_cauchy 0 : IsCauchy (const 0)`.
-/
TheoremDoc MyRat.const_cauchy as "const_cauchy" in "ℚ"

/--
`close_refl s : Close s s`.

## Examples

* `exact close_refl s` proves `Close s s`.
* Used to show `Close` is an equivalence relation.
-/
TheoremDoc MyRat.close_refl as "close_refl" in "ℚ"

/--
`close_symm s t : Close s t → Close t s`.

## Examples

* `exact close_symm s t h` turns `h : Close s t` into `Close t s`.
* Used to show `Close` is an equivalence relation.
-/
TheoremDoc MyRat.close_symm as "close_symm" in "ℚ"

/--
`close_trans s t u : Close s t → Close t u → Close s u`.

## Examples

* `exact close_trans s t u h₁ h₂` proves `Close s u`.
* Used to show `Close` is an equivalence relation.
-/
TheoremDoc MyRat.close_trans as "close_trans" in "ℚ"

/--
`add_cauchy s t : IsCauchy s → IsCauchy t → IsCauchy (addSeq s t)`.

## Examples

* `add_cauchy s t hs ht : IsCauchy (addSeq s t)`.
* Needed to define `x + y` for reals.
-/
TheoremDoc MyRat.add_cauchy as "add_cauchy" in "ℚ"

/--
`close_add s s' t t' : Close s s' → Close t t' → Close (addSeq s t) (addSeq s' t')`.

## Examples

* `close_add s s' t t' h₁ h₂` proves the sums are close.
* It says real addition does not depend on the chosen sequences.
-/
TheoremDoc MyRat.close_add as "close_add" in "ℚ"

/--
`add_comm x y : x + y = y + x` for real numbers.

## Examples

* `rw [MyReal.add_comm]` swaps the first sum of reals.
* `MyReal.add_comm x y : x + y = y + x`.
-/
TheoremDoc MyReal.add_comm as "add_comm (ℝ)" in "ℝ"
