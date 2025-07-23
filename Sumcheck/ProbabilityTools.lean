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
