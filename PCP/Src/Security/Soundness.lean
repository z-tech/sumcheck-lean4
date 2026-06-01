/-
Copyright (c) 2026 LeanStuff contributors. All rights reserved.
-/
import PCP.Src.Trait

/-!
# Soundness — abstract security obligation for PCPs

This file declares the typeclass `HasSoundness` mirroring
`VectorCommitment.HasPositionBinding`: it bundles the numeric
`soundnessError` bound *together with* the proof that the PCP verifier's
acceptance probability on any candidate string is below that bound for
statements outside the language.

The class is the abstraction layer through which higher-level theorems
(notably Kilian's Theorem 5.1, see
[`Kilian/Properties/Theorem51.lean`](../../../Kilian/Properties/Theorem51.lean))
consume PCP soundness. The numeric `ε_PCP(n)` appearing in the paper
binds to `HasSoundness.soundnessError n` at the use site.

## Information-theoretic vs. computational soundness

Classical PCP soundness is *information-theoretic*: the bound holds
against **any** candidate string `pi : List Alphabet`, not just
poly-time-bounded ones. We accordingly use the soundness adversary
type `List Alphabet` directly, without an `OracleComp` or runtime
budget. This is in contrast to `HasPositionBinding`, which is
parameterised on a computational `BindingAdversary` because the
binding property is reductively-secured (CR-hash assumption / ROM
collision bound). PCPs need no such reduction at this layer.

## References

* A. Chiesa, E. Yogev, *Building Cryptographic Proofs from Hash
  Functions*, Definition 3.13 (PCP soundness).
* A. Chiesa, M. Dall'Agnol, Z. Guan, N. Spooner, E. Yogev,
  *Untangling the Security of Kilian's Protocol*,
  [eprint 2024/1434](https://eprint.iacr.org/2024/1434), §3.3.
-/

/-- A PCP's soundness obligation: a numeric error function plus the
    information-theoretic guarantee that no candidate PCP string makes
    the verifier accept a non-instance with probability above that
    function.

    Concrete PCP instances discharge this typeclass by providing:
      * `soundnessError : ℕ → ENNReal` — the bound, typically `2^{-Ω(n)}`
        after standard amplification.
      * `soundness_bound` — the proof that the verifier's
        `acceptanceProb` on `x ∉ L` is at most `soundnessError n`. -/
class HasSoundness (P : Type) [PCPSystem P] [Inhabited (PCPSystem.Alphabet P)] where
  /-- The numeric soundness-error bound as a function of statement size. -/
  soundnessError : ℕ → ENNReal
  /-- The central information-theoretic guarantee: for statements outside
      the PCP's language, no candidate string makes the verifier accept
      with probability above `soundnessError n`.

      `statementSize` is the size-of-statement function used to index
      `soundnessError`; concrete instances pick this (`|x|`, R1CS-row
      count, CNF-variable count, …). -/
  statementSize : PCPSystem.Statement P → ℕ
  soundness_bound :
    ∀ (x : PCPSystem.Statement P) (_ : ¬ PCPSystem.language P x)
      (pi : List (PCPSystem.Alphabet P)),
    PCPSystem.acceptanceProb (P := P) x pi ≤ soundnessError (statementSize x)
  /-- Monotonicity of the soundness-error bound in the statement-size
      parameter `n`. Required to lift instance-level bounds
      `acceptanceProb x pi ≤ soundnessError (statementSize x)` to a
      uniform bound `soundnessError n` for any `statementSize x ≤ n`.
      Holds for every reasonable PCP: typical bounds like `2^{-Ω(n)}`,
      constants, or polynomial fractions are monotone in `n`. -/
  soundnessError_mono : Monotone soundnessError
