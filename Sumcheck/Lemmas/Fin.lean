import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Fin

import Sumcheck.Lemmas.List
import Sumcheck.Lemmas.Degree

def honest_split_eq_cast {n : ℕ} (i : Fin n) (m : ℕ)
    (hm : honest_num_open_vars (n := n) i = m) :
    i.val + (m + 1) = n :=
by
  exact
    Eq.ndrec
      (motive := fun m => i.val + (m + 1) = n)
      (honest_split_eq (n := n) i)
      hm

lemma foldl_finRange_mul_eq_prod
  {α : Type _} : ∀ {n : ℕ} [CommMonoid α] (g : Fin n → α),
    List.foldl (fun acc i => acc * g i) 1 (List.finRange n)
      = (∏ i : Fin n, g i)
  | 0, _, g => by
      simp
  | (n+1), inst, g => by
      classical
      -- expand finRange (n+1) and the ∏ over Fin (n+1)
      -- after this simp, the goal becomes the “head * tail” shape
      simp [List.finRange_succ]

      -- rewrite foldl over the mapped list using the existing List.foldl_map
      have hmap :
          List.foldl (fun acc j => acc * g j) (g 0) (List.map Fin.succ (List.finRange n))
            =
          List.foldl (fun acc i => acc * g i.succ) (g 0) (List.finRange n) := by
        simpa using
          (List.foldl_map (f := Fin.succ)
            (g := fun acc (j : Fin (n + 1)) => acc * g j)
            (l := List.finRange n) (init := g 0))

      -- factor out the initial g 0
      have hpull :
          List.foldl (fun acc i => acc * g i.succ) (g 0) (List.finRange n)
            =
          g 0 * List.foldl (fun acc i => acc * g i.succ) 1 (List.finRange n) := by
        simpa using
          (List.foldl_mul_pull_out (h := fun i : Fin n => g i.succ)
            (a := g 0) (l := List.finRange n))

      -- IH applied to the tail function i ↦ g i.succ
      have hih :
          List.foldl (fun acc i => acc * g i.succ) 1 (List.finRange n)
            =
          (∏ i : Fin n, g i.succ) := by
        simpa using (foldl_finRange_mul_eq_prod (n := n) (g := fun i : Fin n => g i.succ))

      -- finish: rewrite foldl → product using hih, then use Fin.prod_univ_succ
      calc
        List.foldl (fun acc j => acc * g j) (g 0) (List.map Fin.succ (List.finRange n))
            =
        List.foldl (fun acc i => acc * g i.succ) (g 0) (List.finRange n) := hmap
        _ =
        g 0 * List.foldl (fun acc i => acc * g i.succ) 1 (List.finRange n) := hpull
        _ =
        g 0 * (∏ i : Fin n, g i.succ) := by
              -- bridge the foldl tail to the product tail
              simp [hih]
        _ =
        (∏ i : Fin (n + 1), g i) := by
              -- reverse of `∏ i, g i = g 0 * ∏ i, g i.succ`
              simpa using (Fin.prod_univ_succ (f := g)).symm

theorem cast_split_eq_succ_castSucc {n : ℕ} (i : Fin n) (hlt : i.val.succ < n) (k : Fin n) (t0 : Fin i.val) :
  let j : Fin n := ⟨i.val.succ, hlt⟩
  Fin.cast (honest_split_eq (n := n) j).symm k
      =
    Fin.castAdd (honest_num_open_vars (n := n) j + 1) (Fin.castSucc t0)
  →
  Fin.cast (honest_split_eq (n := n) i).symm k
    =
  Fin.castAdd (honest_num_open_vars (n := n) i + 1) t0 := by
  classical
  dsimp
  intro h
  have hv : k.val = t0.val := by
    -- take values
    have := congrArg Fin.val h
    simpa using this
  -- now ext
  apply Fin.ext
  -- show vals equal
  simp [hv]

theorem cast_split_eq_succ_last {n : ℕ} (i : Fin n) (hlt : i.val.succ < n) (k : Fin n) :
  let j : Fin n := ⟨i.val.succ, hlt⟩
  Fin.cast (honest_split_eq (n := n) j).symm k
      =
    Fin.castAdd (honest_num_open_vars (n := n) j + 1) (Fin.last i.val)
  →
  Fin.cast (honest_split_eq (n := n) i).symm k
    =
  Fin.natAdd i.val (0 : Fin (honest_num_open_vars (n := n) i + 1)) := by
  -- unfold the `let` binder in the statement
  dsimp
  intro h
  have hk : k.val = i.val := by
    have hval := congrArg Fin.val h
    simpa using hval
  apply Fin.ext
  -- Compare values on both sides.
  simp [hk]

theorem cast_split_eq_succ_right {n : ℕ} (i : Fin n) (hlt : i.val.succ < n) (k : Fin n)
  (t : Fin (honest_num_open_vars (n := n) (⟨i.val.succ, hlt⟩ : Fin n) + 1))
  (hm1 :
    honest_num_open_vars (n := n) (⟨i.val.succ, hlt⟩ : Fin n) + 1 + 1
      = honest_num_open_vars (n := n) i + 1) :
  let j : Fin n := ⟨i.val.succ, hlt⟩
  Fin.cast (honest_split_eq (n := n) j).symm k = Fin.natAdd j.val t
  →
  Fin.cast (honest_split_eq (n := n) i).symm k
    =
  Fin.natAdd i.val (Fin.cast hm1 (Fin.succ t)) := by
  classical
  dsimp
  intro hk
  have hkval : k.val = i.val + t.val.succ := by
    have hk' := congrArg Fin.val hk
    -- hk' : (Fin.cast ... k).val = (Fin.natAdd ... t).val
    -- simplify values
    -- first get k.val = i.val.succ + t.val
    have hk'' : k.val = i.val.succ + t.val := by
      simpa using hk'
    -- convert succ_add
    simpa [Nat.succ_add_eq_add_succ] using hk''
  apply Fin.ext
  -- reduce to equality on values
  simpa using hkval
