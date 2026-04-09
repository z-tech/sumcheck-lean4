import InteractiveProtocol.Src.FiatShamir
import InteractiveProtocol.Properties.Soundness

/-!
# Fiat-Shamir Soundness Preservation

The main theorem: if an interactive protocol has soundness error `ε`, then the
non-interactive protocol obtained by replacing random challenges with hash outputs
(modeled as a Random Oracle) also has soundness error `ε`.

## Status: Scaffold

The theorem is stated but not proved (`sorry`).
This is the entry point for the Fiat-Shamir/BCS soundness proof.
-/

/-- **Fiat-Shamir Soundness Preservation** (Random Oracle Model).

If a public-coin interactive protocol has soundness error `ε`,
then the non-interactive protocol obtained via the Fiat-Shamir
transformation also has soundness error `ε`, when the hash function
is modeled as a random oracle.

This is the central theorem that the BCS proof establishes.
The proof requires showing that any successful FS adversary can be
turned into a successful interactive adversary with the same success
probability, by programming the random oracle to return the
interactive verifier's challenges.

**Status**: Statement only. Proof to be completed. -/
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
