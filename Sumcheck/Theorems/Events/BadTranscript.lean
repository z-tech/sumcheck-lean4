import CompPoly.CMvPolynomial

import Sumcheck.Impl.Transcript
import Sumcheck.Impl.Reference.Prover
import Sumcheck.Impl.Reference.Transcript

def honest_round_poly
  {𝔽 : Type _} {n : ℕ}
  [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽] [BEq 𝔽] [LawfulBEq 𝔽]
  (p : CPoly.CMvPolynomial n 𝔽)
  (ch : Fin n → 𝔽)
  (i : Fin n) : CPoly.CMvPolynomial 1 𝔽 :=
  honest_message (n := n) (k := i.val) p (challenge_subset ch i) (Nat.succ_le_of_lt i.isLt)

def BadTranscriptEvent
  {𝔽 : Type _} {n : ℕ} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
  (p : CPoly.CMvPolynomial n 𝔽)
  (t : Transcript 𝔽 n) : Prop :=
  ∃ i : Fin n, t.round_polys i ≠ honest_round_poly (p := p) (ch := t.challenges) i
