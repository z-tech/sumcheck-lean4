import VectorCommitment.Src.Merkle.Scheme

/-!
# §12.7 — Merkle commitment equivocation

This file used to contain a placeholder `theorem mt_equivocation : … := True := sorry`.
The placeholder has been removed: shipping a vacuous-`True` theorem to a public
spec is a credibility hit and downstream code never bound to the symbol.

The real distributional content lives in two places:

* **Abstract obligation** — the `HasEquivocation` typeclass in
  [`Src/Security/Equivocation.lean`](../../Src/Security/Equivocation.lean).
  Carries the `(RootSim, OpeningSim)` simulator pair, the distinguisher
  advantage, and the error bound as typeclass fields.

* **Merkle ROM instance** — [`Properties/Probability/Instances/EquivocationROM.lean`](../Probability/Instances/EquivocationROM.lean).
  Discharges the typeclass for `MerkleCommitment (ROHasherValue κ) S` under
  the programmable random-oracle model with bound `Q · d · q / 2^κ + Q² / 2^s`.
  Currently has two open sorries (`equivocationAdvantage` + `equivocation_bound`)
  pending the programmable-RO extension to `OracleComp`. See that file's
  `## Open work` section.

A standalone `theorem mt_equivocation : …` would duplicate the typeclass-level
statement with weaker plumbing and no consumers — kept as documentation only.
-/
