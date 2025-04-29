import Mathlib.Data.Set.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.Finset.Basic

open Set List

def listToSet {α : Type*} (xs : List α) : Set α :=
  {x | x ∈ xs}

/-- `tuples S n` is the set of lists of length `n` whose elements lie in `S`. -/
def tuples {α : Type*} (S : Set α) (n : ℕ) : Set (List α) :=
  { xs | listToSet xs ⊆ S ∧ xs.length = n }

@[simp] theorem tuples_def {α : Type*} {S : Set α} {n : ℕ} :
  tuples S n = { xs | listToSet xs ⊆ S ∧ xs.length = n } := rfl

/-- Introduction rule for `tuples`. -/
theorem tuplesI {α : Type*} {S : Set α} {n : ℕ} {xs : List α}
  (hS : listToSet xs ⊆ S) (hn : xs.length = n) :
  xs ∈ tuples S n := by simp [tuples]; exact ⟨hS, hn⟩

/-- Elimination rule for `tuples`. -/
theorem tuplesE {α : Type*} {S : Set α} {n : ℕ} {xs : List α} {P : Prop}
  (h : xs ∈ tuples S n)
  (hcase : listToSet xs ⊆ S → xs.length = n → P) :
  P := by simp [tuples] at h; exact hcase h.1 h.2

/-- The only 0‐tuple is the empty list. -/
@[simp] theorem tuples_zero {α : Type*} (S : Set α) :
  tuples S 0 = {[]} := by
  -- 1) Turn set‐equality into element‐wise equivalence
  ext xs
  -- Now the goal is
  --   xs ∈ tuples S 0 ↔ xs ∈ ({[]} : Set (List α))
  -- Unfold your definitions:
  simp [tuples, listToSet]
  -- Now it’s actually
  --   (listToSet xs ⊆ S ∧ xs.length = 0) ↔ xs = []
  -- 2) Split the ↔ into two implications
  constructor
  -- 2a) (→) If both listToSet xs ⊆ S and xs.length = 0, then xs = []
  · rintro ⟨_, hlen⟩
    cases xs with
    | nil       => rfl
    | cons _ _  =>
      -- hlen : Nat.succ _ = 0, contradiction
      cases hlen
  -- 2b) (←) Assume xs = [], substitute, then show the conjunction
  · intro h
    subst h
    -- goal is now `listToSet [] ⊆ S ∧ 0 = 0`
    constructor
    · -- vacuously true
      intros x hx; cases hx
    · rfl


/-- `n+1`‐tuples are obtained by consing an element of `S` to an `n`‐tuple. -/
@[simp] theorem tuples_succ {α : Type*} {S : Set α} {n : ℕ} :
  tuples S (n + 1) = (fun p : α × List α => p.1 :: p.2) '' (S ×ˢ tuples S n) :=
by
  ext xs
  simp [tuples, mem_image, prod_mem_prod_iff, to_set_cons_iff, length_cons]

/-- If `S` is nonempty then `tuples S n` is nonempty. -/
theorem tuples_nonempty {α : Type*} {S : set α} {n : ℕ}
  (h : S.nonempty) :
  (tuples S n).nonempty :=
by
  induction n with n ih
  · simp [tuples, set.nonempty, *]
  · rcases h with ⟨x, hx⟩
    rcases ih with ⟨xs, hxs⟩
    use x :: xs
    simp [tuples] at hxs ⊢
    exact ⟨insert_subset.2 ⟨mem_insert _ _, hxs.1⟩, by simp [hxs.2]⟩

/-- If `S` is a nonempty finite set, then `tuples S n` is finite. -/
theorem tuples_finite {α : Type*} {S : set α} {n : ℕ}
  (hS : S.finite) (hne : S.nonempty) :
  (tuples S n).finite :=
by
  induction n with n ih
  · simp [tuples]; exact finite_singleton []
  · simp [tuples]
    refine (hS.prod (ih hS hne)).image _
    rfl
