import Lake
open Lake DSL

package «side-window» where
  -- Vanilla Lean 4. NO Mathlib, no Batteries, no dependencies of any kind:
  -- every statement below is decidable arithmetic on small naturals.

@[default_target]
lean_lib «SIDEWindow» where
