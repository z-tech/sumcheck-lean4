# VectorCommitment — Developer Interface Guide

**Entry point:** `VectorCommitment/Interface.lean`

---

## §0 The Map

```
 Layer   Lean layer                     File(s)                          Status
─────────────────────────────────────────────────────────────────────────────────
 L1      Operational trait              Src/Trait.lean                   interface
         VectorCommitment V:            Src/DataStructures.lean
         setup/trim/commit/open/check

 L2      Merkle realization             Src/Merkle/{Hasher,Shape,        instance
         MerkleCommitment H S           Scheme,Instance,...}.lean
         ⊢ VectorCommitment (Merkle…)

 L3      Abstract security classes      Src/Security/{PositionBinding,   classes
         HasPositionBinding             Extractability,Hiding,
         HasStraightlineExtractor       Equivocation}.lean
         HasHiding
         HasEquivocation

 L4      ROM discharge for Merkle       Properties/Probability/          PROOFS
         BindingROM        ✅           Instances/*ROM.lean
         ExtractabilityROM ◐           + Collision/RandomOracle/
         HidingROM         ✗           Coupling/ROHasher/
         EquivocationROM   ✗           CheckOracle/TraceCollision.lean

 L5      Hasher instantiation           Instances/Parameters.lean        CAPSTONE
         MerkleHasherParams
         (field, λ, q_H) → (κ, D, k, S)
         babyBear_binding_secure ✅
```

**Security status:**

| Notion        | Status                                          |
|---------------|-------------------------------------------------|
| Binding       | ✅ proven, axiom-clean                          |
| Extractability | ◐ reduced to `cacheExtract_sound` (1 sorry)   |
| Hiding        | ✗ params computed; ROM proof pending H1–H5     |
| Equivocation  | ✗ out of scope (programmable RO)               |

---

## §1 Operational Trait

```lean
class VectorCommitment (V : Type) where
  setup  : (maxLen maxQueries : Nat) → ULift UInt64 → UniversalParams
  trim   : UniversalParams → (len queries : Nat) → CommitterKey × VerifierKey
  commit : CommitterKey → List Alphabet → Commitment × CommitmentState
  «open» : CommitterKey → List Alphabet → Commitment → List Index →
           List Alphabet → CommitmentState → Proof
  check  : VerifierKey → Commitment → List Index → List Alphabet → Proof → Bool
```

`HidingVectorCommitment V extends VectorCommitment V` adds the salted variants.

**The verification path is `check`.** All security proofs reason about when `check`
returns `true` on a bad input.

---

## §2 Merkle Realization

`MerkleCommitment H S` for a hasher `H` and tree shape `S`:

| Component | File | Role |
|---|---|---|
| `MerkleHasher` | `Src/Merkle/Hasher.lean` | `hashLeaf`, `hashNodes` |
| `MerkleShape` | `Src/Merkle/Shape.lean` | arity / depth / leaf-count |
| `MerkleCommitment` | `Src/Merkle/Scheme.lean` | data type; `commit`/`check` |
| `VectorCommitment` instance | `Src/Merkle/Instance.lean` | wraps the above |

The ROM hasher is `ROHasherValue κ` (`Properties/Probability/ROHasher.lean`), where
`κ` is the digest bit-length. Use `MerkleVC κ S` from `Interface.lean` as the
canonical type.

---

## §3 Security Classes

Each notion is a four-field typeclass:

```lean
class HasPositionBinding (V : Type) where
  BindingAdversary  : Type → Nat → Type   -- (VerifierKey, budget) → adversary type
  bindingAdvantage  : BindingAdversary vk q → ℝ≥0∞   -- win probability
  bindingError      : VerifierKey → Nat → ℝ≥0∞       -- upper bound
  binding_bound     : bindingAdvantage A ≤ bindingError vk q
```

**Anti-vacuity convention.** `BindingAdversary` is non-empty by construction.
The subtype `{ A // QueryBudget (bindingInner A) q }` carries the budget proof.

**Shared-oracle convention.** The advantage is defined over the *shared* oracle:
the adversary and the verifier (`checkOracle`) query the *same* random oracle
instance. This is mandatory — decoupling the verifier's oracle from the
adversary's makes the binding event trivially false.

---

## §4 ROM Discharge

The proof chain for binding:

```
Pr[Merkle binding failure]
  ≤ Pr[trace has a collision]      [binding_win_le_trace_collision,  BindingROM]
  ≤ collisionBound κ q             [coupling_trace_le_collisionBound, Coupling]
  ≤ 2^(-λ)                        [collisionBound_le_inv_pow,        Parameters]
```

Two shared cores:

| Theorem | File | What it proves |
|---|---|---|
| `birthdayBound` | `Collision.lean` | n iid uniform samples from R collide with prob ≤ n(n-1)/(2\|R\|) |
| `coupling_trace_le_collisionBound` | `Coupling.lean` | adaptive lazy-oracle trace collision ≤ collisionBound κ q |

Per-notion reduction pattern:
1. Define the experiment as an `OracleComp` computation.
2. Show: winning experiment output ⇒ colliding trace (structural).
3. Apply `coupling_trace_le_collisionBound`.

| Instance file | Status | Sorry count |
|---|---|---|
| `BindingROM.lean` | **✅ closed** | 0 |
| `ExtractabilityROM.lean` | ◐ | 1 (`cacheExtract_sound` bridge) |
| `HidingROM.lean` | ✗ | 2 (hiding experiment + hiding bound) |
| `EquivocationROM.lean` | ✗ | 2 (equivocation experiment + bound) |

---

## §5 Hasher Instantiation

`MerkleHasherParams` bundles the numbers a developer chooses:

```lean
structure MerkleHasherParams where
  fieldBits   : Nat  -- ⌊log₂ |F|⌋
  digestElems : Nat  -- D
  saltElems   : Nat  -- k (hiding axis)
  saltBytes   : Nat  -- S (hiding axis, byte-oriented hashers)
  lam         : Nat  -- λ
  qBits       : Nat  -- q_H
```

`MerkleHasherParams.kappa p = p.fieldBits * p.digestElems` — the realized digest.

`MeetsBindingTarget p : Prop = (p.lam + 1 + 2 * p.qBits ≤ p.kappa)` — decidable gate.

The constructor `ofField fieldBits lam qBits` computes correct D, k, S via ceiling division:
- `D = ⌈(λ+1+2q_H)/fieldBits⌉`, `k = ⌈λ/fieldBits⌉`, `S = ⌈λ/8⌉`

Concrete fields:

| Name | fieldBits | Examples |
|---|---|---|
| `babyBear lam qBits` | 30 | BabyBear, KoalaBear, M31 |
| `goldilocks lam qBits` | 63 | Goldilocks |
| `bls12_381 lam qBits` | 254 | BLS12-381 scalar |

BabyBear at λ=128, q_H=64: `D=9, κ=270, k=5, S=16`.

Capstone theorems:

```lean
theorem instantiation_binding_secure
    (p : MerkleHasherParams) (htarget : p.MeetsBindingTarget)
    {q : Nat} (hq : q ≤ 2 ^ p.qBits) (A : ...) :
    HasPositionBinding.bindingAdvantage A ≤ ((2 : ENNReal) ^ p.lam)⁻¹

theorem babyBear_binding_secure
    (lam qBits : Nat) {q : Nat} (hq : q ≤ 2 ^ qBits) (A : ...) :
    HasPositionBinding.bindingAdvantage A ≤ ((2 : ENNReal) ^ lam)⁻¹
```

---

## §6 Entry Points

| Goal | Where to start |
|---|---|
| Verify a Merkle opening in Lean | `VectorCommitment.check` (L1) |
| Understand what "binding" means | `Src/Security/PositionBinding.lean` (L3) |
| See the ROM proof of binding | `Properties/Probability/Instances/BindingROM.lean` (L4) |
| Get a concrete security statement | `Instances/Parameters.lean` (L5) |
| Understand the full chain | `Interface.lean` → this guide |

---

## §7 FAQ

**Q: Why four security classes?**
Because they reduce to different axes: binding/extractability reduce to digest collisions
(`2^κ`); hiding reduces to salt entropy (`2^s` plus a simulator term); equivocation
requires a programmable RO. Splitting them avoids cross-contamination of parameters.

**Q: Why `OracleComp` instead of a PMF over all oracle functions?**
Because the Rust implementation runs a finite sequence of hash calls, not an infinite
random function. The inductive `OracleComp` free monad matches that finite-execution model.
It also enables direct structural induction (the `run_coll_le` proof), whereas the bare-function
encoding is *provably false* — see `coupling_unconditional_is_false` on `wip/phase-b-birthday-bound`.

**Q: What is `h_dom` / why the inductive monad?**
`h_dom` was a `QueryLog → PMF` hypothesis in the early eager-seed approach. It was
machine-refuted (`coupling_unconditional_is_false`). The inductive `OracleComp` type exposes
the computation structure that makes `run_coll_le` provable by structural induction.

**Q: Why is hiding separate from binding?**
Binding lives on the digest axis (`|Digest| = 2^κ`). Hiding lives on the salt axis
(`|Salt| ≥ 2^s`) plus an internal-node simulation term. These are independent parameters;
a large `κ` does not imply any hiding if `s = 0` (no salt). The hiding follow-on chain
(H1–H5) adds the salt axis proofs without reopening the closed binding spine.

---

## §8 Maintenance

- Sync the status table in §0 after each PR; update `binding ✅`, `hiding ✗` etc.
- Keep `Interface.lean` ≤ 250 lines; add aliases, not proofs.
- One alias per concept; do not re-export the same theorem under two names.
- When adding a new security notion, add: (a) a class in `Src/Security/`, (b) an
  instance in `Instances/*ROM.lean`, (c) a row in the §0 status table, (d) a §4 entry.
