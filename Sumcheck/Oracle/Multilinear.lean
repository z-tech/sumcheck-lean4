import Mathlib.Algebra.Field.Defs

/-!
# Multilinear sumcheck oracle (MSB half-split)

Reference Lean implementation of the multilinear sumcheck prover from the
Rust `efficient-sumcheck` crate (`src/provers/multilinear.rs`,
`src/multilinear_sumcheck.rs`). Given hypercube evaluations of a multilinear
polynomial `v : {0,1}^k → 𝔽` and a challenge sequence `w_0, …, w_{k-1} ∈ 𝔽`,
produces the prover's round-polynomial messages `(s_0, s_1)` per round and
the final value — matching the Rust semantics bit-for-bit so a differential
fuzzer can compare outputs.

## Protocol

Each round's polynomial is degree 1:
`q(X) = s_0 + X · (s_1 − s_0)` with `s_0 = Σ v_lo`, `s_1 = Σ v_hi`
under the **MSB half-split** layout (round 0 splits `evals[0..L/2]` vs
`evals[L/2..L]` — NOT adjacent-pair `(v[2k], v[2k+1])` as in the LSB
variant). Consistency invariant: `s_0 + s_1 = current_claim`.

After sending `(s_0, s_1)`, the prover folds by the challenge:
`new[k] = evals[k] + (evals[k + L/2] − evals[k]) · w`, halving the array.

After `k` rounds the array has length 1 and its single entry is the
`final_value`.

## Scope

* Requires `evals.size` to be a power of 2. The Rust implementation
  handles arbitrary sizes via implicit zero-padding of the high half;
  adding that here is straightforward if/when the fuzzer needs it.
* Non-fused (computes round poly then folds, two passes per round). The
  Rust fused kernel is a memory-traffic optimisation with identical
  semantics — the fuzzer compares outputs, not intermediate state.
* No SIMD, no parallelism. This module is a reference oracle, not a
  performance target.

## Main declaration

* `multilinearOracle evals challenges` — returns `(round_polys, final_value)`
  where `round_polys : Array (𝔽 × 𝔽)` has one `(s_0, s_1)` per round.
-/

namespace Sumcheck.Oracle.Multilinear

variable {𝔽 : Type} [Field 𝔽]

/-- Sum a subarray `[lo, hi)` of an `Array 𝔽`. Out-of-bounds accesses
default to `0` (never triggered for in-bounds callers below). -/
private def sumRange (evals : Array 𝔽) (lo hi : Nat) : 𝔽 :=
  (List.range (hi - lo)).foldl (fun acc i => acc + evals.getD (lo + i) 0) 0

/-- Compute the round polynomial `(s_0, s_1)` for the MSB half-split layout.
Assumes `evals.size` is a positive power of 2. -/
private def computeRoundPoly (evals : Array 𝔽) : 𝔽 × 𝔽 :=
  let L := evals.size
  let half := L / 2
  (sumRange evals 0 half, sumRange evals half L)

/-- Fold `evals` by the challenge `w` under the MSB half-split layout.
Resulting array has length `evals.size / 2`:
  `new[k] = evals[k] + (evals[k + L/2] − evals[k]) · w`. -/
private def foldMSB (evals : Array 𝔽) (w : 𝔽) : Array 𝔽 :=
  let L := evals.size
  let half := L / 2
  Array.ofFn (n := half) fun k =>
    let lo := evals.getD k.val 0
    let hi := evals.getD (k.val + half) 0
    lo + (hi - lo) * w

/-- One round of the protocol: emit `(s_0, s_1)` and return the folded
evaluations. -/
private def roundStep (evals : Array 𝔽) (w : 𝔽) : (𝔽 × 𝔽) × Array 𝔽 :=
  let poly := computeRoundPoly evals
  let folded := foldMSB evals w
  (poly, folded)

/-- **Multilinear sumcheck oracle (MSB).** Given hypercube evaluations
`evals : Array 𝔽` (size a power of 2) and challenges `challenges : Array 𝔽`,
runs the sumcheck prover protocol one round per challenge, returning the
round polynomial messages `(s_0, s_1)` per round and the `final_value`.

The `final_value` is `evals_final[0]` if the number of rounds equals
`log_2 evals.size` (so that the array collapses to a single entry), else
`0` — matching the Rust behaviour in `MultilinearProver::final_value`. -/
def multilinearOracle (evals : Array 𝔽) (challenges : Array 𝔽) :
    Array (𝔽 × 𝔽) × 𝔽 :=
  let (polys, finalEvals) :=
    challenges.foldl
      (init := (#[], evals))
      (fun (acc : Array (𝔽 × 𝔽) × Array 𝔽) w =>
        let (polys, ev) := acc
        let (poly, ev') := roundStep ev w
        (polys.push poly, ev'))
  let finalValue :=
    if finalEvals.size = 1 then finalEvals.getD 0 0 else (0 : 𝔽)
  (polys, finalValue)

end Sumcheck.Oracle.Multilinear
