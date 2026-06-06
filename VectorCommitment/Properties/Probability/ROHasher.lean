import VectorCommitment.Src.Merkle.Hasher
import VectorCommitment.Properties.Probability.RandomOracle

/-!
# RO-derived MerkleHasher (with domain separation)

This file is the bridge between the abstract `MerkleHasher` typeclass
(`VectorCommitment/Src/Merkle/Hasher.lean`) and the random-oracle model
(`VectorCommitment/Properties/Probability/RandomOracle.lean`).

Given a deterministic oracle function `ρ : List ByteArray → List.Vector
Bool κ` (the "function view" of an RO), this file constructs a concrete
`MerkleHasher` instance whose leaf-hash and node-hash are domain-separated
queries to `ρ`. The probabilistic-security theorems in
`VectorCommitment/Properties/Probability/Instances/…` quantify over the
random choice of `ρ` and lift this deterministic construction into the
real RO model.

## Domain separation

The encoding distinguishes leaf queries from internal-node queries via
distinct single-byte tags: `Tag.leaf = ⟨#[0]⟩`, `Tag.node = ⟨#[1]⟩`. This
prevents the "tree-shape attack" where an internal-node digest is
reinterpreted as a leaf value (or vice versa) — a structural attack that
no `q²/2^κ` collision bound can cover.

The injectivity of the tagged encoding plus distinctness of the tag
prefixes give the splitting lemma `encodeLeaf_ne_encodeNodes` below:
LEAF-tagged queries and NODE-tagged queries occupy disjoint input
ranges. Combined with the uniform-RO model this yields the formal
"`ρ_LEAF` and `ρ_NODE` are independent oracles" property the binding /
extractability / hiding / equivocation reductions consume.
-/

namespace ROHasher

/-- Single-byte domain-separation tag for leaf hashes. -/
def Tag.leaf : ByteArray := ⟨#[0]⟩

/-- Single-byte domain-separation tag for internal-node hashes. -/
def Tag.node : ByteArray := ⟨#[1]⟩

/-- Serialize a `κ`-bit digest/field element to a `ByteArray`, one `0`/`1` byte
    per bit. Fixed width (`κ` bytes) and injective — the canonical fixed-width
    boundary that the real (Poseidon `F`, bytewise `[u8;S]`) hashers rely on. -/
def vecBytes {κ : Nat} (d : List.Vector Bool κ) : ByteArray :=
  ⟨(d.toList.map (fun b => if b then (1 : UInt8) else (0 : UInt8))).toArray⟩

theorem vecBytes_injective {κ : Nat} : Function.Injective (vecBytes (κ := κ)) := by
  intro d0 d1 h
  unfold vecBytes at h
  have h1 : (d0.toList.map (fun b => if b then (1 : UInt8) else 0)).toArray
          = (d1.toList.map (fun b => if b then (1 : UInt8) else 0)).toArray := by
    injection h
  have h2 : d0.toList.map (fun b => if b then (1 : UInt8) else 0)
          = d1.toList.map (fun b => if b then (1 : UInt8) else 0) := by
    simpa using congrArg Array.toList h1
  have hf : Function.Injective (fun b : Bool => if b then (1 : UInt8) else 0) := by
    intro a b hab; cases a <;> cases b <;> simp_all
  exact List.Vector.toList_injective (List.map_injective_iff.mpr hf h2)

/-- Encode a leaf query as a fixed-width structured triple
    `[LEAF, value-bytes, salt-bytes]`. The value and salt are fixed-width fields
    in distinct positions (not flattened into one ambiguous byte stream), so the
    encoding is injective — `encodeLeaf_inj`. This models the real hashers, whose
    leaf input is a typed `(F, Salt)` / `(Vec<F>, [u8;S])` with canonical
    fixed-width encodings, rather than a variable-length byte concatenation. -/
def encodeLeaf {κ : Nat} (sym salt : List.Vector Bool κ) : List ByteArray :=
  [Tag.leaf, vecBytes sym, vecBytes salt]

/-- The leaf encoding is injective in `(value, salt)` — the fixed-width boundary
    that makes Merkle position binding sound (without it an adversary could open
    one position to two distinct values with no hash collision). -/
theorem encodeLeaf_inj {κ : Nat} {v0 s0 v1 s1 : List.Vector Bool κ}
    (h : encodeLeaf v0 s0 = encodeLeaf v1 s1) : v0 = v1 ∧ s0 = s1 := by
  simp only [encodeLeaf, List.cons.injEq, and_true] at h
  exact ⟨vecBytes_injective h.2.1, vecBytes_injective h.2.2⟩

/-- Encode an internal-node query: `NODE :: serialized children`. Each child is
    serialized to exactly `κ` bytes by `vecBytes`, so boundaries are unambiguous. -/
def encodeNodes {κ : Nat} (children : List (List.Vector Bool κ)) :
    List ByteArray :=
  Tag.node :: children.map vecBytes

/-- Domain separation: a leaf encoding never coincides with a node
    encoding. The two start with distinct tag bytes. -/
theorem encodeLeaf_ne_encodeNodes
    {κ : Nat} (sym salt : List.Vector Bool κ)
    (children : List (List.Vector Bool κ)) :
    encodeLeaf sym salt ≠ encodeNodes children := by
  intro h
  have h_head :
      (encodeLeaf sym salt).head? = (encodeNodes children).head? :=
    congrArg List.head? h
  simp [encodeLeaf, encodeNodes, Tag.leaf, Tag.node, List.head?] at h_head

/-- The hasher value: a thin wrapper around a sampled RO function. -/
structure ROHasherValue (κ : Nat) where
  oracle : List ByteArray → List.Vector Bool κ

/-- `MerkleHasher` instance for the RO-derived hasher.

    Symbol and salt are fixed-width `κ`-bit fields (`List.Vector Bool κ`),
    matching the typed leaf input of the real hashers and giving the injective
    leaf encoding `encodeLeaf_inj` that position binding needs.

    The salt sampler is a placeholder (constant `0^κ`); a hiding instance must
    replace it with a uniform draw of sufficient entropy (for small fields,
    `Salt = F` is insufficient — out of scope here, binding only). -/
noncomputable instance instMerkleHasherROHasher (κ : Nat) :
    MerkleHasher (ROHasherValue κ) where
  Symbol := List.Vector Bool κ
  Digest := List.Vector Bool κ
  Salt := List.Vector Bool κ
  decEqDigest := inferInstance
  defaultSalt := ⟨List.Vector.replicate κ false⟩
  sampleSalt := fun _ _ => List.Vector.replicate κ false
  hashLeaf := fun h sym salt => h.oracle (encodeLeaf sym salt)
  hashNodes := fun h children => h.oracle (encodeNodes children)

/-- The `OracleSpec` corresponding to a Merkle RO with `κ`-bit digests.
    Used by the Layer-3 ROM instance files to run experiments in
    `OracleComp` and reason about query traces. -/
def MerkleROSpec (κ : Nat) : OracleSpec where
  Domain := List ByteArray
  Range  := List.Vector Bool κ
  decEqDomain := inferInstance
  fintypeRange := inferInstance
  inhabitedRange := ⟨List.Vector.replicate κ false⟩

end ROHasher
