import CompPoly.CMvPolynomial

import Sumcheck.Impl.Reference.Transcript

set_option maxHeartbeats 100000

instance : Fact (Nat.Prime 19) := ⟨by decide⟩

-- 3x0x1 + 5x0 + 1
def claim_poly : CPoly.CMvPolynomial 2 (ZMod 19) :=
  CPoly.Lawful.fromUnlawful <|
    ((0 : CPoly.Unlawful 2 (ZMod 19)).insert ⟨#[1, 1], by decide⟩ (3 : ZMod 19))
      |>.insert ⟨#[1, 0], by decide⟩ (5 : ZMod 19)
      |>.insert ⟨#[0, 0], by decide⟩  (1 : ZMod 19)
def claim : (ZMod 19) := (17 : ZMod 19)
def simulated_challenges := ![(2 : ZMod 19), (3 : ZMod 19)]

def valid_transcript := honest_transcript claim_poly claim simulated_challenges
lemma valid_transcript_accepts : is_accepting_transcript claim_poly valid_transcript = true := by
  unfold is_accepting_transcript
  simp
  native_decide

def invalid_transcript := honest_transcript claim_poly (claim + 1) simulated_challenges
lemma invalid_transcript_rejects : is_accepting_transcript claim_poly invalid_transcript = false := by
  unfold is_accepting_transcript
  simp
  native_decide
