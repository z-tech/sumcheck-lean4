import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Fin

import Sumcheck.Lemmas.List

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
