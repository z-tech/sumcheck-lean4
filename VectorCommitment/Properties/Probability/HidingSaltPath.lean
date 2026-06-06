/-
Copyright (c) 2026 LeanStuff contributors. All rights reserved.
-/
import VectorCommitment.Src.Merkle.Scheme
import VectorCommitment.Properties.Theorems.Hiding
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Data.Fintype.Vector

/-!
# Operational per-leaf salt path

The non-hiding `commit` salts every leaf with `defaultSalt`.  Hiding needs an
explicit per-leaf-salted commit (`commitWithSalts`, in `Scheme.lean`) and a
*distributional* version that samples one fresh uniform salt per leaf.  The ROM
hiding proofs in H4/H5 run against `commitWithUniformSalts`, never against an
executable seed generator.

The deterministic-salt case (`Subsingleton Salt`, e.g. `Salt = Unit`) is the
book's `remark:mt-no-privacy` no-privacy construction: salts are a no-op, so the
commit root does not depend on the salt vector at all.
-/

namespace MerkleCommitment

variable {H S : Type} [MerkleHasher H] [MerkleShape S]

/-- **Distributional salted commit.**  Sample `numLeaves` independent uniform
    per-leaf salts and commit with them.  This is the experiment the ROM
    root-hiding and privacy proofs distinguish against. -/
noncomputable def commitWithUniformSalts
    [Fintype (MerkleHasher.Salt H)] [Nonempty (MerkleHasher.Salt H)]
    (mc : MerkleCommitment H S) (msg : List (MerkleHasher.Symbol H)) :
    PMF (Committed H S × Trapdoor H S) :=
  haveI : Nonempty (List.Vector (MerkleHasher.Salt H) (MerkleShape.numLeaves mc.shape)) :=
    ⟨List.Vector.replicate _ (Classical.arbitrary _)⟩
  (PMF.uniformOfFintype
      (List.Vector (MerkleHasher.Salt H) (MerkleShape.numLeaves mc.shape))).map
    (fun salts => mc.commitWithSalts msg salts.toList)

/-- The salted-commit root is the vertex-0 label of `labelAt` (the same bridge
    `commit_root_eq_labelAt_zero` gives for the default-salt `commit`). -/
theorem commitWithSalts_root_eq_labelAt_zero
    (mc : MerkleCommitment H PerfectBinary)
    (msg : List (MerkleHasher.Symbol H))
    (salts : List (MerkleHasher.Salt H))
    (h_n_pos : MerkleShape.numLeaves mc.shape > 0) :
    (mc.commitWithSalts msg salts).fst.root = labelAt mc msg salts 0 := by
  have hne : MerkleShape.numLeaves mc.shape ≠ 0 := Nat.pos_iff_ne_zero.mp h_n_pos
  have htotal : 2 * MerkleShape.numLeaves mc.shape - 1 > 0 := by omega
  show (mc.commitWithSalts msg salts).fst.root = _
  unfold MerkleCommitment.commitWithSalts MerkleCommitment.buildLabels MerkleCommitment.listGetD
  simp [hne]
  rw [List.getElem?_range htotal]
  rfl

/-- **No-privacy / deterministic-salt no-op.**  When the salt space is a
    subsingleton (in particular `Salt = Unit`), the commit root is independent of
    the salt vector: any two salt assignments yield the same root.  This is the
    book's `s = 0` case — deterministic salts hide nothing, they are simply a
    no-op on the root. -/
theorem commitWithSalts_root_eq_of_subsingleton
    [Subsingleton (MerkleHasher.Salt H)]
    (mc : MerkleCommitment H PerfectBinary)
    (msg : List (MerkleHasher.Symbol H))
    (h_n_pos : MerkleShape.numLeaves mc.shape > 0)
    (salts₀ salts₁ : List (MerkleHasher.Salt H)) :
    (mc.commitWithSalts msg salts₀).fst.root =
      (mc.commitWithSalts msg salts₁).fst.root := by
  rw [commitWithSalts_root_eq_labelAt_zero mc msg salts₀ h_n_pos,
      commitWithSalts_root_eq_labelAt_zero mc msg salts₁ h_n_pos]
  apply labelAt_eq_of_leaf_hash_eq
  intro v _
  -- Every leaf hash agrees because the two salt entries are equal (subsingleton).
  have heq : (listGetD salts₀ (v - (MerkleShape.numLeaves mc.shape - 1))
            (MerkleHasher.defaultSalt.default : MerkleHasher.Salt H)) =
         (listGetD salts₁ (v - (MerkleShape.numLeaves mc.shape - 1))
            (MerkleHasher.defaultSalt.default : MerkleHasher.Salt H)) :=
    Subsingleton.elim _ _
  simp only [heq]

end MerkleCommitment
