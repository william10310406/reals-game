import GameServer

/-!
# Tactic documentation

Every tactic gets one sentence and at least two examples.
-/

/--
`exact h` closes the goal when `h` is a proof of exactly the goal.

## Examples

* Goal `P`, hypothesis `hp : P`: `exact hp` closes the goal.
* Goal `Q`, hypotheses `f : P → Q` and `hp : P`: `exact f hp` closes the goal.

## Common error

`type mismatch`: the proof you gave proves something else. Compare its type with the goal.
-/
TacticDoc exact

/--
`rfl` closes a goal of the form `X = X`, where both sides are the same.

## Examples

* Goal `x = x`: `rfl` closes it.
* Goal `f a = f a`: `rfl` closes it.

## Common error

`The rfl tactic failed`: the two sides are not the same. Rewrite them first with `rw`.
-/
TacticDoc rfl

/--
`rw [h]` uses `h : A = B` to replace every `A` in the goal by `B`.

## Examples

* `h : a = b` and goal `f a = c`: `rw [h]` changes the goal to `f b = c`.
* `rw [← h]` goes the other way: it replaces `B` by `A`.
* `rw [h] at h₂` rewrites the hypothesis `h₂` instead of the goal.
* `rw [h₁, h₂]` does two rewrites in a row.

After rewriting, `rw` tries `rfl`. So `rw` often closes the goal by itself.

## Common errors

* `did not find instance of the pattern`: the left side of `h` is not in the goal.
  Maybe you need `←`, or `at`.
* You need the square brackets: `rw h` is wrong, `rw [h]` is right.
-/
TacticDoc rw

/--
`intro h` moves an assumption out of the goal into the hypotheses.

## Examples

* Goal `P → Q`: `intro hp` gives the hypothesis `hp : P` and the goal `Q`.
* Goal `∀ x, P x`: `intro x` gives an object `x` and the goal `P x`.
* Goal `¬ P`: `intro hp` gives `hp : P` and the goal `False`, because `¬ P` means `P → False`.
-/
TacticDoc intro

/--
`apply h` works backwards: if `h : P → Q` and the goal is `Q`, the goal becomes `P`.

## Examples

* `f : P → Q` and goal `Q`: `apply f` changes the goal to `P`.
* `g : P → Q → R` and goal `R`: `apply g` gives two goals, `P` and `Q`.
-/
TacticDoc apply

/--
`constructor` splits a goal `P ∧ Q` (or `P ↔ Q`) into two goals.

## Examples

* Goal `P ∧ Q`: `constructor` gives the goals `P` and `Q`.
* Goal `P ↔ Q`: `constructor` gives the goals `P → Q` and `Q → P`.
-/
TacticDoc constructor

/--
`obtain ⟨a, b⟩ := h` takes a hypothesis apart.

## Examples

* `h : P ∧ Q`: `obtain ⟨hp, hq⟩ := h` gives `hp : P` and `hq : Q`.
* `h : ∃ x, P x`: `obtain ⟨x, hx⟩ := h` gives an object `x` and `hx : P x`.
* `h : P ∨ Q`: `obtain hp | hq := h` gives two goals, one with `hp : P`, one with `hq : Q`.

Type `⟨` as `\<` and `⟩` as `\>`.
-/
TacticDoc obtain

/--
`left` proves `P ∨ Q` by proving `P`.

## Examples

* Goal `P ∨ Q`: `left` changes the goal to `P`.
* Goal `(a = b) ∨ False`: `left` changes the goal to `a = b`.
-/
TacticDoc left

/--
`right` proves `P ∨ Q` by proving `Q`.

## Examples

* Goal `P ∨ Q`: `right` changes the goal to `Q`.
* Goal `False ∨ (a = b)`: `right` changes the goal to `a = b`.
-/
TacticDoc right

/--
`exfalso` changes any goal to `False`. Use it when your hypotheses contradict each other.

## Examples

* Goal `Q`, hypotheses `hp : P` and `hn : ¬ P`: `exfalso`, then `exact hn hp`.
* Goal `a = b`, hypothesis `h : False`: `exfalso`, then `exact h`.
-/
TacticDoc exfalso

/--
`use x` proves a goal `∃ y, P y` by choosing `y := x`. The goal becomes `P x`.

## Examples

* Goal `∃ y, y = a`: `use a` changes the goal to `a = a`.
* Goal `∃ c, b = a + c`: `use 0` changes the goal to `b = a + 0`.
-/
TacticDoc use

/--
`have h : P := proof` adds a new hypothesis `h : P`.

## Examples

* `hpq : P → Q` and `hp : P`: `have hq : Q := hpq hp` adds `hq : Q`.
* `have h : a + 0 = a := add_zero a` adds `h : a + 0 = a`.
-/
TacticDoc «have»

/--
`induction n with d hd` proves a statement about `n` in two steps:
first for `0`, then for `succ d`, using the induction hypothesis `hd` for `d`.

## Examples

* Goal `0 + n = n`: `induction n with d hd` gives the goals `0 + 0 = 0` and
  `0 + succ d = succ d`, with `hd : 0 + d = d`.
* Goal `P n`: `induction n with d hd` gives the goals `P 0` and `P (succ d)`, with `hd : P d`.

## Tip

If the goal has an `→`, do the induction *before* `intro`. Then the induction hypothesis is stronger.
-/
TacticDoc induction

/--
`cases n with d` splits a natural number into two cases: `0` and `succ d`.
There is no induction hypothesis.

## Examples

* Goal `P n`: `cases n with d` gives the goals `P 0` and `P (succ d)`.
* Goal `a + b = 0 → b = 0`: `cases b with d` gives the cases `b = 0` and `b = succ d`.
-/
TacticDoc cases
