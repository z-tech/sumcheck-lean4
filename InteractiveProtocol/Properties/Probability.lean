import Mathlib.Data.Rat.Init
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Finset.Filter

import InteractiveProtocol.Src.Protocol

/-! ## Probability over challenges -/

/-- The set of all possible challenge vectors of length `n` over `C`. -/
abbrev allChallenges (C : Type*) (n : ℕ) [Fintype C] : Finset (Fin n → C) :=
  Finset.univ

/-- The probability that an event holds over uniformly random challenges. -/
noncomputable def probEvent
    {C : Type*} {n : ℕ} [Fintype C]
    (E : (Fin n → C) → Prop) : ℚ := by
  classical
  let Ω : Finset (Fin n → C) := allChallenges C n
  exact ((Ω.filter E).card : ℚ) / (Ω.card : ℚ)

/-- The probability the verifier accepts when interacting with prover `P`
    on statement `st`, over uniformly random challenges. -/
noncomputable def probAccept {S C : Type*} {n : ℕ} [Fintype C]
    (ip : PublicCoinProtocol S C n)
    (st : S) (P : Prover ip) : ℚ :=
  probEvent (C := C) (n := n)
    (fun r => ip.verifier_accepts st (generateTranscript ip st P r))
