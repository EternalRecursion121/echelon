import GameServer
import Mathlib
import Game.Lib

/-! Things available in every level.

Design: the game sits on Mathlib (so later proofs stay short), but each world first
makes the player *earn* the abstractions it uses — Hefferon's results are proved as
named `Statement`s and then become inventory items. -/
