import InteractiveProtocol.Src.Protocol

-- Here we have a systemization of elements need to compute the
-- Fiat-Shamir transformation. These are computable definitions to
-- generate and verify non-interactive proofs

-- A Random Oracle maps bytestrings (lists here) to challenges.
-- in the Random Oracle Model (ROM), this is a uniformly random function
-- here, this can be implemented by a hash function
def RandomOracle (C : Type*) := List ℕ → C

-- this is the non-interactive argument system derived from a protocol
-- via Fiat-Shamir transformation. The proof is the prover messages.
structure FiatShamirProof {S C : Type*} {n : ℕ} (ip : PublicCoinProtocol S C n) where
  messages : ∀ i : Fin n, ip.ProverMessage i

-- to generate FS challenges we much serialize statement and partial transcript
-- into a bytestring for hashing. Encoding at round `i` takes the statement and
-- messages from rounds `0..i-1`.
structure Encoding {S C : Type*} {n : ℕ} (ip : PublicCoinProtocol S C n) where
           -- statement
  encode : S → (i : Fin n) →
           -- first i messages
           (∀ j : Fin i.val, ip.ProverMessage ⟨j.val, Nat.lt_trans j.isLt i.isLt⟩) →
           List ℕ

-- derive the challenges from random oracle, encoding, statement, and prover messages
-- challenge at round i is H(encode(st, msgs[0..i-1]))
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

-- the verifier is given a statement and the non-interactive proof
-- their job is to rederive challenges using the random oracle and check accepts
def fiatShamirVerify {S C : Type*} {n : ℕ}
    (ip : PublicCoinProtocol S C n)
    (H : RandomOracle C)
    (enc : Encoding ip)
    (st : S)
    (proof : FiatShamirProof ip) : Prop :=
  let chs := fiatShamirChallenges ip H enc st proof.messages
  let tr := ip.mkTranscript proof.messages chs
  ip.verifierAccepts st tr
