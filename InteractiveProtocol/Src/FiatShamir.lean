import InteractiveProtocol.Src.Protocol

-- Computable definitions for the Fiat-Shamir transformation
-- these are the things you need to actually generate and verify non-interactive proofs

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
def fiatShamirChallenges {S C : Type*} {n : ℕ}
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
def fiatShamirVerify {S C : Type*} {n : ℕ}
    (ip : PublicCoinProtocol S C n)
    (H : RandomOracle C)
    (enc : Encoding ip)
    (st : S)
    (proof : FiatShamirProof ip) : Prop :=
  let chs := fiatShamirChallenges ip H enc st proof.messages
  let tr := ip.mkTranscript proof.messages chs
  ip.verifier_accepts st tr
