import CompPoly.Multivariate.CMvPolynomial
import Sumcheck.Src.Transcript
import Sumcheck.Src.CMvPolynomial

@[simp] def verifier_check {𝔽} [CommRing 𝔽] [DecidableEq 𝔽]
  (domain : List 𝔽)
  (max_degree : ℕ)
  (round_claim : 𝔽)
  (round_p : CPoly.CMvPolynomial 1 𝔽) : Bool :=
  -- identity is sum over domain
  let round_identity_ok : Prop :=
    domain.foldl (fun acc a =>
      acc + CPoly.CMvPolynomial.eval₂ (RingHom.id 𝔽) (fun _ : Fin 1 => a) round_p) 0
      = round_claim
  let deg_bound_ok : Prop :=
    CPoly.CMvPolynomial.degreeOf ⟨0, by decide⟩ round_p ≤ max_degree
  decide round_identity_ok && decide deg_bound_ok

def is_verifier_accepts_transcript
  {𝔽 : Type _} {n : ℕ}
  [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
  (domain : List 𝔽)
  (p : CPoly.CMvPolynomial n 𝔽)
  (t : Transcript 𝔽 n) : Bool :=
  let rounds_ok : Bool :=
    (List.finRange n).all (fun i : Fin n =>
      verifier_check domain (ind_degree_k p i) (t.claims (Fin.castSucc i)) (t.round_polys i)
      &&
      decide (t.claims i.succ = next_claim (t.challenges i) (t.round_polys i))
    )
  let final_ok : Bool :=
    decide (t.claims (Fin.last n) = CPoly.CMvPolynomial.eval t.challenges p)
  rounds_ok && final_ok
