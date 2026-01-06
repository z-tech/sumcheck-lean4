import Mathlib.Data.ZMod.Basic

abbrev count_field_size {𝔽} [Fintype 𝔽] : ℕ :=
  Fintype.card 𝔽
