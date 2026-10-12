import Lake
open Lake DSL

package «NovelProof» where
  -- add package configuration options here

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.35.0-rc1"

@[default_target]
lean_lib «NovelProof» where
  -- add library configuration options here
