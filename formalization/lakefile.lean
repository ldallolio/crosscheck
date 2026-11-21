/-
Copyright (c) 2026 Luca Dall'Olio. All rights reserved.
Released under the MIT license as described in the file LICENSE.
-/
import Lake
open Lake DSL

package «ImperativeOptimization» where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.16.0"

@[default_target]
lean_lib «ImperativeOptimization» where

/-- The certificate checker (`lake exe crosscheck-check FILE.json`). -/
lean_exe «crosscheck-check» where
  root := `CheckerMain
