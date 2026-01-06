-- import CompPoly.CMvPolynomial

-- import Sumcheck.Prover
-- import Sumcheck.Verifier

-- structure Transcript (𝔽 : Type _) (n : ℕ) [CommRing 𝔽] where
--   round_polys : Fin n → (CPoly.CMvPolynomial 1 𝔽)
--   challenges : Fin n → 𝔽
--   claims : Fin (n + 1) → 𝔽

-- def challenge_subset {𝔽} {n} (ch : Fin n → 𝔽) (i : Fin n) : Fin i.val → 𝔽 :=
--   fun j => ch ⟨j.val, Nat.lt_trans j.isLt i.isLt⟩

-- def derive_claims
--   {𝔽} {n} [CommRing 𝔽] [DecidableEq 𝔽]
--   (initial_claim : 𝔽)
--   (round_polys : Fin n → CPoly.CMvPolynomial 1 𝔽)
--   (challenges : Fin n → 𝔽) : Fin (n+1) → 𝔽
--   | ⟨0, _⟩ => initial_claim
--   | ⟨k+1, hk⟩ =>
--       let i : Fin n := ⟨k, Nat.lt_of_succ_lt_succ hk⟩
--       next_claim (challenges i) (round_polys i)

-- def build_transcript
--   {𝔽} {n} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
--   (claim_p  : CPoly.CMvPolynomial n 𝔽)
--   (initial_claim : 𝔽)
--   (challenges : Fin n → 𝔽) : Transcript 𝔽 n :=
-- by
--   -- compute the round_polys
--   let round_polys : Fin n → CPoly.CMvPolynomial 1 𝔽 :=
--     fun i => prover_message claim_p (challenge_subset challenges i) (Nat.succ_le_of_lt i.isLt)
--   -- use round_polys to compute claims
--   let claims: Fin (n + 1) → 𝔽 := derive_claims initial_claim round_polys challenges
--   exact {
--     round_polys := round_polys
--     challenges  := challenges
--     claims      := claims
--   }

-- def is_accepts
--   {𝔽 : Type _} {n : ℕ}
--   [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
--   (p : CPoly.CMvPolynomial n 𝔽)
--   (t : Transcript 𝔽 n) : Bool :=
-- by
--   -- check all rounds
--   let round_ok : Bool :=
--     (List.finRange n).all (fun i : Fin n =>
--       verifier_check (t.claims (Fin.castSucc i)) (t.round_polys i)
--       &&
--       decide (t.claims i.succ = next_claim (t.challenges i) (t.round_polys i))
--     )

--   -- final check
--   let final_ok : Bool :=
--     decide (t.claims (Fin.last n) = CPoly.CMvPolynomial.eval t.challenges p)

--   exact round_ok && final_ok

-- lemma and_eq_true_iff (a b : Bool) :
--     (a && b) = true ↔ a = true ∧ b = true := by
--   cases a <;> cases b <;> simp

-- @[simp] lemma build_transcript_challenges
--   {𝔽 : Type _} {n : ℕ} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
--   (p : CPoly.CMvPolynomial n 𝔽) (c0 : 𝔽) (ch : Fin n → 𝔽) :
--   (build_transcript (claim_p := p) (initial_claim := c0) (challenges := ch)).challenges = ch :=
-- by
--   rfl

-- @[simp] lemma build_transcript_claims
--   {𝔽 : Type _} {n : ℕ} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
--   (p : CPoly.CMvPolynomial n 𝔽) (c0 : 𝔽) (ch : Fin n → 𝔽) :
--   (build_transcript (claim_p := p) (initial_claim := c0) (challenges := ch)).claims =
--     derive_claims c0
--       (fun i => prover_message p (challenge_subset ch i) (Nat.succ_le_of_lt i.isLt))
--       ch :=
-- by
--   rfl

-- @[simp] lemma build_transcript_round_polys
--   {𝔽 : Type _} {n : ℕ} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
--   (p : CPoly.CMvPolynomial n 𝔽) (c0 : 𝔽) (ch : Fin n → 𝔽) :
--   (build_transcript (claim_p := p) (initial_claim := c0) (challenges := ch)).round_polys =
--     (fun i => prover_message p (challenge_subset ch i) (Nat.succ_le_of_lt i.isLt)) :=
-- by
--   rfl

-- @[simp] lemma derive_claims_zero
--   {𝔽 : Type _} {n : ℕ} [CommRing 𝔽] [DecidableEq 𝔽]
--   (c0 : 𝔽) (rp : Fin n → CPoly.CMvPolynomial 1 𝔽) (ch : Fin n → 𝔽) :
--   derive_claims (n := n) c0 rp ch ⟨0, Nat.succ_pos _⟩ = c0 :=
-- by
--   rfl

-- @[simp] lemma derive_claims_succ
--   {𝔽 : Type _} {n : ℕ} [CommRing 𝔽] [DecidableEq 𝔽]
--   (c0 : 𝔽) (rp : Fin n → CPoly.CMvPolynomial 1 𝔽) (ch : Fin n → 𝔽)
--   (k : Fin n) :
--   derive_claims (n := n) c0 rp ch k.succ = next_claim (ch k) (rp k) :=
-- by
--   -- k.succ is ⟨k.val+1, ...⟩ so this is definitional once you match the branches
--   cases k with
--   | mk k hk =>
--     -- unfold the succ branch; rfl usually works after this `cases`
--     simp [derive_claims]

-- def prob_over_challenges
--   {𝔽 : Type _} {n : ℕ} [Fintype 𝔽] [DecidableEq 𝔽]
--   (E : (Fin n → 𝔽) → Prop) [DecidablePred E] : ℚ :=
--   (( (Finset.univ.filter E).card : ℚ) / (Fintype.card (Fin n → 𝔽) : ℚ))

-- def honest_round_poly
--   {𝔽 : Type _} {n : ℕ} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
--   (p : CPoly.CMvPolynomial n 𝔽)
--   (ch : Fin n → 𝔽)
--   (i : Fin n) : CPoly.CMvPolynomial 1 𝔽 :=
--   prover_message p (challenge_subset ch i) (Nat.succ_le_of_lt i.isLt)

-- def bad_transcript
--   {𝔽 : Type _} {n : ℕ} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
--   (p : CPoly.CMvPolynomial n 𝔽)
--   (t : Transcript 𝔽 n) : Prop :=
--   ∃ i : Fin n, t.round_polys i ≠ honest_round_poly (p := p) (ch := t.challenges) i

-- def honest_transcript
--   {𝔽 : Type _} {n : ℕ}
--   [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
--   (p : CPoly.CMvPolynomial n 𝔽)
--   (c0 : 𝔽)
--   (ch : Fin n → 𝔽) : Transcript 𝔽 n :=
--   build_transcript (claim_p := p) (initial_claim := c0) (challenges := ch)

-- def bad_round_poly_b
--   {𝔽 : Type _} {n : ℕ}
--   [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
--   (p : CPoly.CMvPolynomial n 𝔽) (c0 : 𝔽)
--   (t : Transcript 𝔽 n) : Bool :=
--   let ht := honest_transcript (p := p) (c0 := c0) (ch := t.challenges)
--   (List.finRange n).any (fun i : Fin n =>
--     decide (t.round_polys i ≠ ht.round_polys i)
--   )

-- def bad_round_exists_b
--   {𝔽 : Type _} {n : ℕ}
--   [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
--   (p : CPoly.CMvPolynomial n 𝔽) (c0 : 𝔽)
--   (t : Transcript 𝔽 n) : Bool :=
--   let ht := honest_transcript (p := p) (c0 := c0) (ch := t.challenges)
--   (List.finRange n).any (fun i : Fin n =>
--     decide (t.round_polys i ≠ ht.round_polys i)
--   )

-- def event_accepts_and_bad_b
--   {𝔽 : Type _} {n : ℕ}
--   [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
--   (p : CPoly.CMvPolynomial n 𝔽)
--   (c0 : 𝔽)
--   (P : (Fin n → 𝔽) → Transcript 𝔽 n) : (Fin n → 𝔽) → Bool :=
--   fun ch =>
--     let t := P ch
--     -- (optional but recommended) ensure transcript uses the given challenges
--     decide (t.challenges = ch)
--     &&
--     is_accepts p t
--     &&
--     bad_round_exists_b (p := p) (c0 := c0) t

-- def prob_over_challenges_b
--   {𝔽 : Type _} {n : ℕ} [Fintype 𝔽] [DecidableEq 𝔽]
--   (E : (Fin n → 𝔽) → Bool) : ℚ :=
--   prob_over_challenges (𝔽 := 𝔽) (n := n) (fun ch => E ch = true)

-- def prob_accepts_and_bad
--   {𝔽 : Type _} {n : ℕ}
--   [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
--   (p : CPoly.CMvPolynomial n 𝔽)
--   (c0 : 𝔽)
--   (P : (Fin n → 𝔽) → Transcript 𝔽 n) : ℚ :=
--   prob_over_challenges_b (𝔽 := 𝔽) (n := n) (event_accepts_and_bad_b (p := p) (c0 := c0) P)

-- def FirstBad
--   {𝔽 : Type _} {n : ℕ}
--   [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽] [BEq 𝔽] [LawfulBEq 𝔽]
--   (p : CPoly.CMvPolynomial n 𝔽)
--   (t : Transcript 𝔽 n)
--   (i : Fin n) : Prop :=
--   t.round_polys i ≠ honest_round_poly (p := p) (ch := t.challenges) i ∧
--   ∀ j : Fin n, j.val < i.val →
--     t.round_polys j = honest_round_poly (p := p) (ch := t.challenges) j

-- -- lemma first_bad_round_forces_collision
-- --   {𝔽 : Type _} {n : ℕ}
-- --   [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽] [BEq 𝔽] [LawfulBEq 𝔽]
-- --   (p : CPoly.CMvPolynomial n 𝔽) (c0 : 𝔽)
-- --   (t : Transcript 𝔽 n)
-- --   (hacc : is_accepts p t = true)
-- --   (i : Fin n)
-- --   (hfirst :
-- --     t.round_polys i ≠ (honest_transcript (p := p) (c0 := c0) (ch := t.challenges)).round_polys i)
-- --   (hpref :
-- --     ∀ j : Fin n, j.val < i.val →
-- --       t.round_polys j =
-- --         (honest_transcript (p := p) (c0 := c0) (ch := t.challenges)).round_polys j) :
-- --   next_claim (t.challenges i) (t.round_polys i)
-- --     =
-- --   next_claim (t.challenges i)
-- --     ((honest_transcript (p := p) (c0 := c0) (ch := t.challenges)).round_polys i) :=
-- -- by
-- --   -- proof goes here
-- --   sorry


-- -- theorem prob_accepts_and_bad_le
-- --   {𝔽 : Type _} {n : ℕ}
-- --   [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
-- --   (p : CPoly.CMvPolynomial n 𝔽)
-- --   (c0 : 𝔽)
-- --   (P : (Fin n → 𝔽) → Transcript 𝔽 n)
-- --   (d : ℚ) :
-- --   prob_accepts_and_bad (p := p) (c0 := c0) P ≤ d / (Fintype.card 𝔽 : ℚ) :=
-- -- by
-- --   -- this is where the real proof goes
-- --   sorry

-- namespace __TranscriptTests__
--   -- 3x0x1 + 5x0 + 1
--   def claim_poly : CPoly.CMvPolynomial 2 (ZMod 19) :=
--     CPoly.Lawful.fromUnlawful <|
--       ((0 : CPoly.Unlawful 2 (ZMod 19)).insert ⟨#[1, 1], by decide⟩ (3 : ZMod 19))
--         |>.insert ⟨#[1, 0], by decide⟩ (5 : ZMod 19)
--         |>.insert ⟨#[0, 0], by decide⟩  (1 : ZMod 19)
--   def claim : (ZMod 19) := (17 : ZMod 19)
--   def simulated_challenges := ![(2 : ZMod 19), (3 : ZMod 19)]

--   def valid_transcript := build_transcript claim_poly claim simulated_challenges
--   lemma valid_transcript_accepts : is_accepts claim_poly valid_transcript = true := by
--     unfold is_accepts
--     simp
--     native_decide

--   def invalid_transcript := build_transcript claim_poly (claim + 1) simulated_challenges
--   lemma invalid_transcript_rejects : is_accepts claim_poly invalid_transcript = false := by
--     unfold is_accepts
--     simp
--     native_decide
-- end __TranscriptTests__
