import Game.Levels.Tutorial
import Game.Levels.Logic
import Game.Levels.Naturals
import Game.Levels.Integers
import Game.Levels.Rationals
import Game.Levels.Reals
import Game.Levels.Inequalities
import Game.Levels.Limits
import Game.Levels.RealArith
import Game.Levels.RealOrder
import Game.Levels.RealIneq

Title "Build the Reals"

Introduction
"
# Build the Reals

You will build the real numbers from nothing.

You start with logic. Then you build the natural numbers.
From them you build the integers, then the rationals.
From rationals you build the reals, using Cauchy sequences.
At the end you prove inequalities and limits.

You only use Lean itself. No big library. Every fact you use, you proved yourself.

Start with the **Tutorial** world.
"

Info "
*Build the Reals*, a game for the [Lean game server](https://adam.math.hhu.de).

## Rules

* You may only use tactics and theorems from your inventory.
* New items unlock as you play.
* There is no `ring`, `linarith` or `simp` here.
* Given rules (like `add_zero`, `mk_add_mk`, `frac_eq`) are the definitions of the operations.
  Everything else in your inventory is a theorem you proved.

## Behind the scenes

Building `ℤ`, `ℚ` and `ℝ` as quotients needs proofs that the definitions are well defined.
Those plumbing proofs are in `Game/MyInt`, `Game/MyRat` and `Game/MyReal` of the repository.
Some of them use Lean's own `Nat`, `Int`, `Rat` and the `omega`/`grind` tactics as a checking tool.
The levels never use them.

## Progress

Your progress is saved in your browser.
Clearing site data deletes it.

## Credits

* Game engine: [lean4game](https://github.com/leanprover-community/lean4game).
* Template: [GameSkeleton](https://github.com/hhu-adam/GameSkeleton) (MIT).
* Level structure and some custom tactics follow the
  [Natural Number Game](https://github.com/leanprover-community/NNG4) (Apache 2.0).
  See `NOTICE` in the repository.
* Source: [github.com/william10310406/reals-game](https://github.com/william10310406/reals-game).
"

Languages "en"
CaptionShort "From logic to limits."
CaptionLong "Build the naturals, integers, rationals and reals yourself. Then prove inequalities and limits. Only Lean, no Mathlib."

-- The worlds form one line. Inequalities only needs Rationals, but comes after Reals.
Dependency Reals → Inequalities
Dependency Limits → RealArith
Dependency RealArith → RealOrder
Dependency RealOrder → RealIneq

/-! Build the game. Shows warnings if it found a problem with your game. -/
MakeGame
