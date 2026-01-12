import Sumcheck.Impl.HonestTranscript

lemma challenge_subset_succ
  {𝔽 : Type _} {n : ℕ}
  (r : Fin n → 𝔽)
  (i : Fin n)
  (h : i.val.succ < n) :
  challenge_subset r (⟨i.val.succ, h⟩ : Fin n)
    = Fin.snoc (challenge_subset r i) (r i) := by
  funext j
  -- split j : Fin (i.val.succ) into last / castSucc
  refine Fin.lastCases (n := i.val) ?h_last ?h_cast j
  · -- j = Fin.last i.val
    -- LHS is r at index i.val; RHS is snoc ... at last = r i
    have hx :
        (⟨i.val, Nat.lt_trans (Fin.last i.val).isLt h⟩ : Fin n) = i := by
      ext
      simp
    -- simp will turn snoc-at-last into (r i)
    simp [challenge_subset, Fin.snoc, hx]
  · intro j0
    -- j = Fin.castSucc j0
    have hx :
        (⟨j0.val, Nat.lt_trans (Nat.lt_trans j0.isLt (Nat.lt_succ_self i.val)) h⟩ : Fin n)
          = ⟨j0.val, Nat.lt_trans j0.isLt i.isLt⟩ := by
      ext
      simp
    -- simp will turn snoc-at-castSucc into the original function
    simp [challenge_subset, Fin.snoc, hx]
