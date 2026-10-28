import Lake
open Lake DSL

/-
GameServer: the engine (pinned to the lean4game tag matching our toolchain).
To develop against the local fork in `../lean4game`, swap the `require` below for
`require GameServer from "../lean4game/server"`.
-/
require GameServer from git "https://github.com/leanprover-community/lean4game.git" @ "v4.35.0" / "server"
-- Mathlib last, so that its pins of shared dependencies (batteries, Cli, …) win.
require "leanprover-community" / mathlib @ git "v4.35.0"

/-!
# USER DEPENDENCIES

Add any further dependencies of your game below.

Note: If your package (like `mathlib` or `Std`) has tags of the form `v4.X.0` then
you can use

```
require "leanprover-community" / mathlib @ git leanVersion
```
 -/

/-!
# PACKAGE CONFIGURATION

Here you can set options used in your game. The player will use the same options as you'll
have set here.

NOTE: The `leanOptions` and `moreServerOptions` influence how the player preceives the game.
For example, it is important to have `linter.all` set to `false` to prevent any linter
warnings from showing up during playing.

NOTE: We abuse the `trace.debug` option to toggle messages in VSCode on and
off when calling `lake build`. Ideally there would be a better way using `logInfo` and
an option like `lean4game.verbose`.
-/
package Game where
  /- Used in all cases. -/
  leanOptions := #[
    /- linter warnings might block the player. (IMPORTANT) -/
    ⟨`linter.all, false⟩,
    /- to display the values of let declarations, like `:= 42` (IMPORTANT)  -/
    ⟨`pp.showLetValues, true⟩,
    /- make all assumptions always accessible. -/
    ⟨`tactic.hygienic, false⟩]
  /- Used when calling `lake build`. -/
  moreLeanArgs := #[
    -- TODO: replace with `lean4game.verbose`
    "-Dtrace.debug=false"]
  /- Used when opening a file in VSCode or when playing the game. -/
  moreServerOptions := #[
    -- TODO: replace with `lean4game.verbose`
    ⟨`trace.debug, true⟩]

@[default_target]
lean_lib Game
