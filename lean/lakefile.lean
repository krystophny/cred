import Lake
open Lake DSL

package foundations where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, false⟩
  ]

@[default_target]
lean_lib Foundations where
  roots := #[`Foundations]

lean_lib Synthetic where
  roots := #[`Synthetic]
