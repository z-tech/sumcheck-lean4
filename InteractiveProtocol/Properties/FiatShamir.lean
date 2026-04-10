import InteractiveProtocol.Src.FiatShamir
import InteractiveProtocol.Properties.Soundness

-- this file is about Fiat-Shamir soundness preservation.
-- if an interactive protocol has soundness error ε, then
-- the non-interactive protocol obtained by replacing random
-- challenges with hash functions (random oracle) also has
-- soundness ε.

theorem fiatShamir_preserves_soundness {S C : Type*} {n : ℕ} [Fintype C]
    (ip : PublicCoinProtocol S C n)
    (isTrue : S → Prop)
    (ε : S → ℚ)
    (enc : Encoding ip)
    (h_sound : hasSoundnessError ip isTrue ε) :
    -- For every FS adversary (who produces a proof given a random oracle),
    -- and every false statement, the probability over random oracles
    -- that the FS verifier accepts is at most ε.
    ∀ (st : S) (fsAdv : RandomOracle C → FiatShamirProof ip),
      ¬ isTrue st →
      -- (The formal probability statement over random oracles goes here.
      --  The exact formulation depends on how the ROM is modeled.)
      True := by
  sorry
