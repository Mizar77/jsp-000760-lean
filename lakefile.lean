import Lake
open Lake DSL

package "jsp000760" where
  version := v!"0.1.0"

require "leanprover-community" / "mathlib" @ git "v4.31.0"

@[default_target]
lean_lib JSP000760

