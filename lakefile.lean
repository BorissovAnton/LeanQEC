import Lake
open Lake DSL

package LeanQEC where
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩
  ]

-- Depend on Lean-QuantumInfo (using git URL)
require quantumInfo from git
  "https://github.com/Timeroot/Lean-QuantumInfo" @ "main"

@[default_target]
lean_lib QEC where
  srcDir := "src"
