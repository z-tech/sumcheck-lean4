import Mathlib.Data.Rat.Init
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Finset.Filter

import InteractiveProtocol.Src.Protocol

-- these are just some helpers dealing with rationals / distributions

abbrev allChallenges (C : Type*) (n : ℕ) [Fintype C] : Finset (Fin n → C) :=
  Finset.univ

noncomputable def probEvent
    {C : Type*} {n : ℕ} [Fintype C]
    (E : (Fin n → C) → Prop) : ℚ := by
  classical
  let Ω : Finset (Fin n → C) := allChallenges C n
  exact ((Ω.filter E).card : ℚ) / (Ω.card : ℚ)

noncomputable def probAccept {S C : Type*} {n : ℕ} [Fintype C]
    (ip : PublicCoinProtocol S C n)
    (st : S) (P : Prover ip) : ℚ :=
  probEvent (C := C) (n := n)
    (fun r => ip.verifier_accepts st (generateTranscript ip st P r))
