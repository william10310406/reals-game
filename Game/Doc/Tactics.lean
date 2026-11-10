import GameServer

/--
`exact h` closes the goal when `h` is exactly the goal.

## Examples

* Goal `P`, hypothesis `hp : P`: `exact hp` closes the goal.
* Goal `Q`, hypotheses `f : P → Q` and `hp : P`: `exact f hp` closes the goal.
-/
TacticDoc exact
