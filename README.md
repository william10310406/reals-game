# Build the Reals

A [Lean 4](https://lean-lang.org) game for the [lean4game](https://github.com/leanprover-community/lean4game) server.

You build the natural numbers, the integers, the rationals and the reals yourself.
Then you make `ℝ` a full number system and prove inequalities and limits in it.
The game uses only Lean core, no Mathlib.

Play: <https://adam.math.hhu.de/#/g/william10310406/reals-game>

## Worlds

| # | World | Levels | What you build or prove |
|---|---|---|---|
| 0 | Tutorial | 6 | goals, hypotheses, error messages; `exact`, `rfl`, `rw` |
| 1 | Logic | 15 | `→ ∧ ∨ ¬ ∀ ∃` |
| 2 | Naturals | 17 | `MyNat` from `0` and `succ`; induction; `+`, `*`, `≤` |
| 3 | Integers | 21 | `MyInt` as pairs `a - b` up to `a + d = c + b`; ring rules, order |
| 4 | Rationals | 13 | `MyRat` as `frac a b` up to cross-multiplication; `+`, `-`, `≤` |
| 5 | Cauchy sequences and Reals | 12 | Cauchy sequences, `Close`, `MyReal` as a quotient, addition |
| 6 | Inequalities in ℚ | 11 | rules for `≤` on `ℚ`: signs, antisymmetry, products |
| 7 | Limits in ℚ | 8 | limits of constants and sums, convergent ⇒ Cauchy, `1/(n+1) → 0` |
| 8 | Arithmetic in ℝ | 19 | `0`, `1`, `-`, `*` on `ℝ`, `ℚ` inside `ℝ`; ring laws |

122 levels. Each world depends on the one before.

## How it is built

* `Game/MyNat`, `Game/MyInt`, `Game/MyRat`, `Game/MyReal`: definitions and the computation rules
  the player may use (`add_zero`, `mk_add_mk`, `frac_eq`, `ofSeq_mul`, ...).
* Quotients need well-definedness proofs. These plumbing proofs use Lean's own `Nat`/`Int`
  and `omega`/`grind` as a checking tool. For `ℝ` (`Game/MyRat/ToRat.lean`) our `ℚ` is mapped into
  Lean's own `Rat`, so that `-`, `*`, `abs` and `≤` on `ℝ` can be checked to not depend on the
  chosen Cauchy sequences. The levels never use them: players only get the computation rules and
  the theorems they proved.
* `Game/Tactic.lean`: `use`, and `induction n with d hd` / `cases n with d` macros.
* The game depends on `lean4game`'s `server/` at tag `v4.35.0` (see `lakefile.lean` for why).

## Building

The GitHub Action builds the game. To publish a new version, wait for a green run,
then open <https://adam.math.hhu.de/import/trigger/william10310406/reals-game>.

## License

Apache 2.0, see `LICENSE`. Third-party parts are listed in `NOTICE`.
