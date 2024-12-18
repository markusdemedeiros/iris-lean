import Lake
open Lake DSL

package iris where
  srcDir := "./src/"

require batteries from git "https://github.com/leanprover-community/batteries" @ "main"
require Qq from git "https://github.com/gebner/quote4" @ "master"
require "leanprover-community" / "importGraph" @ git "main"

@[default_target]
lean_lib Iris
