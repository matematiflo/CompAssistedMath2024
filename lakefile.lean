import Lake
open Lake DSL

package «leanproject» where
  -- Settings applied to both builds and interactive editing
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩, -- pretty-prints `fun a ↦ b`
    ⟨`pp.proofs, true⟩,  -- if pp.proofs is false (default is false), then proofs that are any more complicated than a free variable or a constant print as ⋯
    ⟨`pp.proofs.withType, true⟩  -- if pp.proofs is false and pp.proofs.withType is true (the default just changed to false), then omitted proofs print with their types, like (⋯ : p)
    -- if pp.proofs is false, then pp.proofs.threshold can be set to a number greater than 0 to allow more complicated proof terms to be pretty printed.
  ]
  -- add any additional package configuration options here

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"
    -- update toolchain via `curl https://raw.githubusercontent.com/leanprover-community/mathlib4/master/lean-toolchain -o lean-toolchain`
    -- after that, run `lake update`

require mdgen from git
  "https://github.com/Seasawher/mdgen" @ "main"
    -- use it running `lake exe mdgen <input_dir> <output_dir>`
    -- view the result by running `mdbook serve --open`

@[default_target]
lean_lib «Leanproject» where
  -- add any library configuration options here
