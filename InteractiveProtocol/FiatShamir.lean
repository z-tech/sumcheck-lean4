import InteractiveProtocol.Basic

/-!
# Fiat-Shamir Transformation

This module defines the Fiat-Shamir transformation for public-coin interactive protocols
and states the key theorem: if an interactive protocol has soundness error `ε`, then the
non-interactive protocol obtained by replacing random challenges with hash outputs
(modeled as a Random Oracle) also has soundness error `ε`.

## Overview

The Fiat-Shamir heuristic converts a public-coin IP into a non-interactive argument:
instead of the verifier sending random challenges, the prover computes challenges
as hash outputs: `challenge_i = H(statement, msg_0, ..., msg_i)`.

In the **Random Oracle Model (ROM)**, where `H` is modeled as a truly random function,
this transformation preserves soundness. This was formalized by Ben-Sasson, Chiesa, and
Spooner (BCS) for IOPs.

## Status: Scaffold

The structures below define the shape of the FS transformation.
The main theorem `fiatShamir_preserves_soundness` is stated but not proved (`sorry`).
This is the entry point for the Fiat-Shamir/BCS soundness proof.
-/

/-- A random oracle maps bytestrings (modeled as lists) to challenge elements.
    In the ROM, this is a uniformly random function. -/
def RandomOracle (C : Type*) := List ℕ → C

/-- A non-interactive argument system derived from a public-coin protocol
    via the Fiat-Shamir transformation. The "proof" consists of all prover messages. -/
structure FiatShamirProof {S C : Type*} {n : ℕ} (ip : PublicCoinProtocol S C n) where
  /-- The prover messages (the "proof" in the non-interactive setting) -/
  messages : ∀ i : Fin n, ip.ProverMessage i

/-- An encoding function that serializes a statement and partial transcript
    into a bytestring for hashing. This is needed to compute FS challenges.
    The encoding at round `i` takes the statement and messages from rounds `0..i-1`. -/
structure Encoding {S C : Type*} {n : ℕ} (ip : PublicCoinProtocol S C n) where
  /-- Encode the statement + first `i` prover messages into a bytestring -/
  encode : S → (i : Fin n) →
           (∀ j : Fin i.val, ip.ProverMessage ⟨j.val, Nat.lt_trans j.isLt i.isLt⟩) →
           List ℕ

/-- Derive Fiat-Shamir challenges from a random oracle, encoding, statement,
    and prover messages. Challenge at round `i` is `H(encode(st, msgs[0..i-1]))`. -/
noncomputable def fiatShamirChallenges {S C : Type*} {n : ℕ}
    (ip : PublicCoinProtocol S C n)
    (H : RandomOracle C)
    (enc : Encoding ip)
    (st : S)
    (msgs : ∀ i : Fin n, ip.ProverMessage i) :
    Fin n → C :=
  fun i =>
    let prevMsgs : ∀ j : Fin i.val,
        ip.ProverMessage ⟨j.val, Nat.lt_trans j.isLt i.isLt⟩ :=
      fun j => msgs ⟨j.val, Nat.lt_trans j.isLt i.isLt⟩
    H (enc.encode st i prevMsgs)

/-- The Fiat-Shamir verifier: given a statement and non-interactive proof,
    re-derive challenges using the random oracle and check acceptance. -/
noncomputable def fiatShamirVerify {S C : Type*} {n : ℕ}
    (ip : PublicCoinProtocol S C n)
    (H : RandomOracle C)
    (enc : Encoding ip)
    (st : S)
    (proof : FiatShamirProof ip) : Prop :=
  let chs := fiatShamirChallenges ip H enc st proof.messages
  let tr := ip.mkTranscript proof.messages chs
  ip.verifier_accepts st tr

/-! ## Main Theorem (to be proved)

The Fiat-Shamir transformation preserves soundness in the Random Oracle Model.
This is the entry point for the BCS-style proof.
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
    (ε : ℚ)
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
