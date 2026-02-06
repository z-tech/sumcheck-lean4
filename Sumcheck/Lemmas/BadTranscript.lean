import CompPoly.CMvPolynomial

import Sumcheck.Events.BadTranscript
import Sumcheck.Models.Adversary
import Sumcheck.Models.AdversaryTranscript

lemma badTranscript_implies_lastBadRound
  {𝔽 : Type _} {n : ℕ}
  [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
  (claim : 𝔽)
  (p : CPoly.CMvPolynomial n 𝔽)
  (adv : Adversary 𝔽 n)
  (r : Fin n → 𝔽) :
  BadTranscriptEvent p (AdversaryTranscript claim p adv r) →
  LastBadRound claim p adv r := by
  classical
  intro hBad
  let t : Transcript 𝔽 n := AdversaryTranscript claim p adv r

  -- the set of "bad" rounds (where the adversary deviates from the honest round poly)
  let bad : Finset (Fin n) :=
    Finset.univ.filter (fun i => t.round_polys i ≠ honest_round_poly p r i)

  have bad_nonempty : bad.Nonempty := by
    rcases hBad with ⟨i0, hi0⟩
    refine ⟨i0, ?_⟩
    -- hi0 : BadRound (t.round_polys i0) p t.challenges i0
    -- and for AdversaryTranscript, t.challenges is (definally) r
    simpa [bad, BadRound, t] using hi0

  -- choose the last bad round
  let i : Fin n := Finset.max' bad bad_nonempty

  have hi_neq :
      t.round_polys i ≠ honest_round_poly p r i := by
    have hi_mem : i ∈ bad := Finset.max'_mem bad bad_nonempty
    simpa [bad] using hi_mem

  refine ⟨i, ?_, ?_⟩
  · -- the witness round is bad
    simpa [t] using hi_neq
  · intro j hij
    -- show every round after i is good, else contradict maximality of i
    by_contra hneq
    have hneq' : t.round_polys j ≠ honest_round_poly p r j := by
      -- convert the hypothesis to use `t`
      simpa [t] using hneq
    have hj_mem : j ∈ bad := by
      simp [bad, hneq']

    have hj_le : j ≤ i := by
      -- maximality: for any member j of bad, j ≤ max' bad ...
      have hle : j ≤ Finset.max' bad bad_nonempty :=
        Finset.le_max' bad j hj_mem
      simpa [i] using hle

    exact (not_le_of_gt hij) hj_le
