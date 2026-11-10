import GameServer

/-! # Documentation for limits in `ℝ` -/

/--
`eps k` is the real number `1/(k+1)`. It is our measure of *small* in `ℝ`.

## Examples

* `eps_def k : eps k = ofRat (frac 1 (succ k))`.
* `eps (succ k + k) + eps (succ k + k) = eps k` (`eps_half`).
-/
DefinitionDoc MyReal.eps as "eps"

/--
`eps_def k : eps k = ofRat (frac 1 (succ k))`.

## Examples

* `rw [eps_def]` unfolds the first `eps`.
* `rw [eps_def n, eps_def k]` unfolds two different ones.
-/
TheoremDoc MyReal.eps_def as "eps_def" in "limℝ"

/--
`eps_nonneg k : 0 ≤ eps k` in `ℝ`.

## Examples

* `exact eps_nonneg k` proves `0 ≤ eps k`.
* `MyReal.le_trans _ 0 _ h (eps_nonneg k)` with `h : x ≤ 0` gives `x ≤ eps k`.
-/
TheoremDoc MyReal.eps_nonneg as "eps_nonneg (ℝ)" in "limℝ"

/--
`eps_half k : eps (succ k + k) + eps (succ k + k) = eps k`. Two halves make a whole.

## Examples

* `rw [← eps_half k]` splits `eps k` into two halves.
* `rw [sub_add_sub, eps_half] at h` after adding two half-size bounds.
-/
TheoremDoc MyReal.eps_half as "eps_half" in "limℝ"

/--
`eps_le k n : k ≤ n → eps n ≤ eps k`. Later `eps` are smaller.

## Examples

* `eps_le k n h : eps n ≤ eps k` with `h : k ≤ n`.
* `MyReal.le_trans _ _ _ h1 (eps_le K n h)` replaces `eps n` by the bigger `eps K`.
-/
TheoremDoc MyReal.eps_le as "eps_le" in "limℝ"

/--
`const c` is the constant sequence `c, c, c, …` of reals.

## Examples

* `const_apply c n : const c n = c`.
* `Tendsto (const c) c` (`tendsto_const`).
-/
DefinitionDoc MyReal.const as "const (ℝ)"

/--
`const_apply c n : const c n = c` for sequences of reals.

## Examples

* `rw [const_apply]` replaces the first `const c n` by `c`.
* `MyReal.const_apply 0 n : const 0 n = 0`.
-/
TheoremDoc MyReal.const_apply as "const_apply (ℝ)" in "limℝ"

/--
`Tendsto a L`: the sequence `a` of reals tends to `L`. For every `k` there is `N` with
`abs (a n - L) ≤ eps k` for all `n ≥ N`.

## Examples

* Goal `Tendsto a L`: `intro k`, `use N`, `intro n hn`.
* `h : Tendsto a L`: `obtain ⟨N, hN⟩ := h k`, then `hN n hn : abs (a n - L) ≤ eps k`.
-/
DefinitionDoc MyReal.Tendsto as "Tendsto (ℝ)"

/--
`tendsto_const c : Tendsto (const c) c`.

## Examples

* `exact tendsto_const c` proves that a constant sequence converges.
* `tendsto_const 0 : Tendsto (const 0) 0`.
-/
TheoremDoc MyReal.tendsto_const as "tendsto_const (ℝ)" in "limℝ"

/--
`addSeq a b` is the sequence `a 0 + b 0, a 1 + b 1, …` of reals.

## Examples

* `addSeq_apply a b n : addSeq a b n = a n + b n`.
* `Tendsto (addSeq a b) (L + M)` (`tendsto_add`).
-/
DefinitionDoc MyReal.addSeq as "addSeq (ℝ)"

/--
`addSeq_apply a b n : addSeq a b n = a n + b n` for sequences of reals.

## Examples

* `rw [addSeq_apply]` computes the first `addSeq a b n`.
* `MyReal.addSeq_apply a (const c) n : addSeq a (const c) n = a n + const c n`.
-/
TheoremDoc MyReal.addSeq_apply as "addSeq_apply (ℝ)" in "limℝ"

/--
`tendsto_add a b L M : Tendsto a L → Tendsto b M → Tendsto (addSeq a b) (L + M)`.

## Examples

* `tendsto_add a b L M h1 h2` gives the limit of a sum.
* `tendsto_add a (const c) L c h (tendsto_const c)` shifts a sequence by `c`.
-/
TheoremDoc MyReal.tendsto_add as "tendsto_add (ℝ)" in "limℝ"

/--
`le_of_forall_eps x y : (∀ k, x ≤ y + eps k) → x ≤ y`.

## Examples

* Goal `L ≤ M`: `apply le_of_forall_eps`, `intro k`, then show `L ≤ M + eps k`.
* Used for the uniqueness of limits.
-/
TheoremDoc MyReal.le_of_forall_eps as "le_of_forall_eps" in "limℝ"

/--
`tendsto_le a L M : Tendsto a L → Tendsto a M → L ≤ M`.

## Examples

* `tendsto_le a L M h1 h2 : L ≤ M`.
* `tendsto_le a M L h2 h1 : M ≤ L`.
-/
TheoremDoc MyReal.tendsto_le as "tendsto_le" in "limℝ"

/--
`tendsto_unique a L M : Tendsto a L → Tendsto a M → L = M`. A sequence has at most one limit.

## Examples

* `tendsto_unique a L M h1 h2 : L = M`.
* `rw [tendsto_unique a L M h1 h2]` replaces `L` by `M`.
-/
TheoremDoc MyReal.tendsto_unique as "tendsto_unique" in "limℝ"

/--
`squeeze a b c L : (∀ n, a n ≤ b n) → (∀ n, b n ≤ c n) → Tendsto a L → Tendsto c L → Tendsto b L`.

## Examples

* `squeeze a b c L hab hbc ha hc : Tendsto b L`.
* With `a = const 0`, a sequence between `0` and a null sequence tends to `0`.
-/
TheoremDoc MyReal.squeeze as "squeeze" in "limℝ"
