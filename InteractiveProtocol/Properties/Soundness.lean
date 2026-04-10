import InteractiveProtocol.Properties.Probability

-- here, isTrue is a predicate representing the thing the prover is claiming

-- soundess error ε is defined with respect to this predicate:
--   for every false statement st (and any prover) prob. verifier accepts <= ε
def hasSoundnessError {S C : Type*} {n : ℕ} [Fintype C]
    (ip : PublicCoinProtocol S C n)
    (isTrue : S → Prop) (ε : S → ℚ) : Prop :=
  ∀ (st : S) (P : Prover ip),
    ¬ isTrue st →
    probAccept ip st P ≤ ε st

-- similarly, perfect completeness is defined with respect to isTrue:
--   if for every true statement st, verifier accepts prob. 1
def hasPerfectCompleteness {S C : Type*} {n : ℕ} [Fintype C]
    (ip : PublicCoinProtocol S C n)
    (isTrue : S → Prop) (honest : Prover ip) : Prop :=
  ∀ (st : S),
    isTrue st →
    probAccept ip st honest = 1
