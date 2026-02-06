import Sumcheck.Events.Accepts
import Sumcheck.Probability.Challenges

import Sumcheck.Src.HonestTranscript
import Sumcheck.Src.Hypercube
import Sumcheck.Src.Verifier
import Sumcheck.Events.Accepts

import Sumcheck.Lemmas.Accepts
import Sumcheck.Lemmas.Hypercube

import Sumcheck.Theorems.SoundnessAux

lemma honestTranscript_roundPoly_eq_honestRoundPoly
  {𝔽 : Type _} {n : ℕ}
  [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
  (p : CPoly.CMvPolynomial n 𝔽) (r : Fin n → 𝔽) (i : Fin n) :
  (generate_honest_transcript (𝔽 := 𝔽) (n := n) p (true_sum p) r).round_polys i
    =
  honest_round_poly (p := p) (ch := r) i := by
  classical

  -- Force the same `==` that `generate_honest_transcript` uses.
  letI : BEq 𝔽 := instBEqOfDecidableEq (α := 𝔽)

  -- Make it lawful using decide.
  letI : LawfulBEq 𝔽 :=
  { rfl := by
      intro a
      simp
    eq_of_beq := by
      intro a b h
      have hdec : decide (a = b) = true := by
        simpa [instBEqOfDecidableEq] using h
      -- Turn `decide (a=b)=true` into `a=b` using the equality lemma
      have : (decide (a = b) = true) = (a = b) := by
        simp
      -- rewrite hdec into a proof of `a=b`
      -- after rewriting, `hdec : a=b`
      have hab : a = b := by
        -- rewrite the type of hdec
        simpa [this] using hdec
      exact hab }

  cases i with
  | mk k hk =>
    simp [generate_honest_transcript, honest_round_poly, honest_prover_message]


-- theorem completeness
--   {𝔽 : Type _} {n : ℕ}
--   [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
--   (p : CPoly.CMvPolynomial n 𝔽) :
--   prob_over_challenges (𝔽 := 𝔽) (n := n)
--     (fun r =>
--       AcceptsEvent (𝔽 := 𝔽) (n := n) p
--         (generate_honest_transcript (𝔽 := 𝔽) (n := n) p (true_sum p) r))
--   = 1 :=
-- by
--   classical
--   -- name the event for readability
--   let E : (Fin n → 𝔽) → Prop :=
--     fun r =>
--       AcceptsEvent (𝔽 := 𝔽) (n := n) p
--         (generate_honest_transcript (𝔽 := 𝔽) (n := n) p (true_sum p) r)

--   -- perfect completeness: E holds for every r
--   have hE : ∀ r : Fin n → 𝔽, E r :=
--     perfect_completeness_over_challenges (𝔽 := 𝔽) (n := n) p

--   -- therefore filtering univ by E gives back univ
--   have hfilter :
--       (Finset.univ.filter E : Finset (Fin n → 𝔽)) = Finset.univ := by
--     ext r
--     simp [E, hE r]

--   -- denominator is nonzero (since the challenge space is nonempty)
--   have hdenom :
--       ((Finset.univ : Finset (Fin n → 𝔽)).card : ℚ) ≠ 0 := by
--     have : (Finset.univ.card : ℕ) ≠ 0 := by
--       simpa using (Fintype.card_ne_zero (α := (Fin n → 𝔽)))
--     exact_mod_cast this

--   -- conclude prob = |univ| / |univ| = 1
--   simp [prob_over_challenges, all_assignments_n, E, hfilter]
