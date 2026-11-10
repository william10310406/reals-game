import Game.Levels.Naturals.L01_AddZero
import Game.Levels.Naturals.L02_AddOne
import Game.Levels.Naturals.L03_ZeroAdd
import Game.Levels.Naturals.L04_SuccAdd
import Game.Levels.Naturals.L05_AddComm
import Game.Levels.Naturals.L06_AddAssoc
import Game.Levels.Naturals.L07_AddRightCancel
import Game.Levels.Naturals.L08_AddLeftCancel
import Game.Levels.Naturals.L09_EqZero
import Game.Levels.Naturals.L10_ZeroMul
import Game.Levels.Naturals.L11_SuccMul
import Game.Levels.Naturals.L12_MulComm
import Game.Levels.Naturals.L13_MulAdd
import Game.Levels.Naturals.L14_AddMul
import Game.Levels.Naturals.L15_MulAssoc
import Game.Levels.Naturals.L16_LeRefl
import Game.Levels.Naturals.L17_LeTrans

World "Naturals"
Title "Naturals"

Introduction "
We build the natural numbers `0, 1, 2, ...` from scratch.

A natural number is either `0`, or `succ n`: the number after `n`.
That is all. From this you will prove the rules of `+`, `*` and `≤`.

Your new tool is **induction**.
"

Conclusion "
`ℕ` is done. Every rule you will need later is a theorem you proved here.
"
