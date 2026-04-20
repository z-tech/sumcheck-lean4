import InteractiveProtocol.Src.Protocol
import InteractiveProtocol.Properties.Probability
import InteractiveProtocol.Properties.Soundness

/-!
# The complexity class IP

A formulation of the class `IP` (Interactive Proofs) on top of the generic
`PublicCoinProtocol` framework. A language `L : Input → Prop` is in `IP` if
there exists a public-coin protocol with an encoding of inputs into statements,
an honest prover, and an input-dependent soundness error bounded by `1/3`,
such that:

* honest-prover completeness is perfect (probability 1),
* every (potentially dishonest) prover has accept probability at most `ε x`
  on inputs outside the language.

This is the interface Shamir's theorem (`IP = PSPACE`) will discharge: given
`L ∈ PSPACE`, construct an `IPCertificate L`.

**Scope note.** A single protocol is reused across all inputs. Classical `IP`
allows the protocol to depend on input size; that extension (a protocol family
indexed by input size) is a straightforward generalization when needed.
-/

/-- A witness that a language `L` lies in `IP`: a protocol, encoding, honest
prover, and soundness error function, bundled with the completeness and
soundness proofs. -/
structure IPCertificate {Input : Type} (L : Input → Prop) where
  S : Type
  C : Type
  n : ℕ
  cFin : Fintype C
  ip : PublicCoinProtocol.{0, 0, 0, 0} S C n
  encode : Input → S
  honest : Prover ip
  ε : Input → ℚ
  εbound : ∀ x, ε x ≤ 1/3
  complete : ∀ x, L x → @probAccept S C n cFin ip (encode x) honest = 1
  sound : ∀ x, ¬ L x → ∀ P : Prover ip,
    @probAccept S C n cFin ip (encode x) P ≤ ε x

/-- The language `L` is in `IP`, i.e. admits an interactive proof. Defined as
the mere existence of an `IPCertificate`. -/
def InIP {Input : Type} (L : Input → Prop) : Prop :=
  Nonempty (IPCertificate L)

/-- Smart constructor: package components directly into `InIP L`. -/
theorem InIP.mk {Input : Type} {L : Input → Prop}
    {S C : Type} {n : ℕ} [cFin : Fintype C]
    (ip : PublicCoinProtocol.{0, 0, 0, 0} S C n)
    (encode : Input → S)
    (honest : Prover ip)
    (ε : Input → ℚ)
    (εbound : ∀ x, ε x ≤ 1/3)
    (complete : ∀ x, L x → probAccept ip (encode x) honest = 1)
    (sound : ∀ x, ¬ L x → ∀ P : Prover ip,
      probAccept ip (encode x) P ≤ ε x) :
    InIP L :=
  ⟨{ S := S, C := C, n := n, cFin := cFin, ip := ip, encode := encode,
     honest := honest, ε := ε, εbound := εbound,
     complete := complete, sound := sound }⟩

/-- Bridge constructor: build `InIP L` from an existing `hasPerfectCompleteness`
+ `hasSoundnessError` pair via an encoding that transports language membership
into statement validity. This is the expected call pattern from any protocol
that already proved completeness/soundness in the generic form (as both
`sumcheckProtocol` and `sharpSAT` do). -/
theorem InIP.of_hasProperties
    {Input : Type} {L : Input → Prop}
    {S C : Type} {n : ℕ} [Fintype C]
    (ip : PublicCoinProtocol.{0, 0, 0, 0} S C n)
    (encode : Input → S)
    (honest : Prover ip)
    (isTrue : S → Prop)
    (ε_S : S → ℚ)
    (hcorrespond : ∀ x, L x ↔ isTrue (encode x))
    (hcomplete : hasPerfectCompleteness ip isTrue honest)
    (hsound : hasSoundnessError ip isTrue ε_S)
    (εbound : ∀ x, ε_S (encode x) ≤ 1/3) :
    InIP L := by
  refine InIP.mk ip encode honest (fun x => ε_S (encode x)) εbound ?_ ?_
  · intro x hx
    exact hcomplete (encode x) ((hcorrespond x).mp hx)
  · intro x hx P
    exact hsound (encode x) P (fun h => hx ((hcorrespond x).mpr h))

/-! ### Size-indexed families

For languages whose instances have no fixed bit-length — e.g. #SAT or TQBF,
where formula length or arity is unbounded — a single protocol over a single
field cannot meet the `ε ≤ 1/3` bound simultaneously for all inputs, because
the Schwartz–Zippel bound `d / |𝔽|` grows with instance size. Classical IP
handles this by letting the protocol (in particular, the field) grow with the
input size. The structures below are the size-indexed analogues of
`IPCertificate` / `InIP` / `InIP.of_hasProperties`. -/

/-- Size-indexed IP certificate: the protocol, statement type, challenge type,
and round count all depend on an input size `k : ℕ`. Each input lives at some
specific size, and its accept probability is bounded by `ε k x ≤ 1/3`. -/
structure IPFamilyCertificate {Inputs : ℕ → Type}
    (L : ∀ k, Inputs k → Prop) where
  S : ℕ → Type
  C : ℕ → Type
  n : ℕ → ℕ
  cFin : ∀ k, Fintype (C k)
  ip : ∀ k, PublicCoinProtocol.{0, 0, 0, 0} (S k) (C k) (n k)
  encode : ∀ k, Inputs k → S k
  honest : ∀ k, Prover (ip k)
  ε : ∀ k, Inputs k → ℚ
  εbound : ∀ k x, ε k x ≤ 1/3
  complete : ∀ k x, L k x →
    @probAccept (S k) (C k) (n k) (cFin k) (ip k) (encode k x) (honest k) = 1
  sound : ∀ k x, ¬ L k x → ∀ P : Prover (ip k),
    @probAccept (S k) (C k) (n k) (cFin k) (ip k) (encode k x) P ≤ ε k x

/-- The size-indexed language `L` admits a family of interactive proofs. -/
def InIPFamily {Inputs : ℕ → Type} (L : ∀ k, Inputs k → Prop) : Prop :=
  Nonempty (IPFamilyCertificate L)

/-- Smart constructor for `InIPFamily`. -/
theorem InIPFamily.mk {Inputs : ℕ → Type} {L : ∀ k, Inputs k → Prop}
    {S C : ℕ → Type} {n : ℕ → ℕ} [cFin : ∀ k, Fintype (C k)]
    (ip : ∀ k, PublicCoinProtocol.{0, 0, 0, 0} (S k) (C k) (n k))
    (encode : ∀ k, Inputs k → S k)
    (honest : ∀ k, Prover (ip k))
    (ε : ∀ k, Inputs k → ℚ)
    (εbound : ∀ k x, ε k x ≤ 1/3)
    (complete : ∀ k x, L k x → probAccept (ip k) (encode k x) (honest k) = 1)
    (sound : ∀ k x, ¬ L k x → ∀ P : Prover (ip k),
      probAccept (ip k) (encode k x) P ≤ ε k x) :
    InIPFamily L :=
  ⟨{ S := S, C := C, n := n, cFin := cFin, ip := ip,
     encode := encode, honest := honest, ε := ε, εbound := εbound,
     complete := complete, sound := sound }⟩

/-- Bridge constructor: build `InIPFamily L` from per-size `hasPerfectCompleteness`
+ `hasSoundnessError` pairs and a per-size encoding. -/
theorem InIPFamily.of_hasProperties
    {Inputs : ℕ → Type} {L : ∀ k, Inputs k → Prop}
    {S C : ℕ → Type} {n : ℕ → ℕ} [∀ k, Fintype (C k)]
    (ip : ∀ k, PublicCoinProtocol.{0, 0, 0, 0} (S k) (C k) (n k))
    (encode : ∀ k, Inputs k → S k)
    (honest : ∀ k, Prover (ip k))
    (isTrue : ∀ k, S k → Prop)
    (ε_S : ∀ k, S k → ℚ)
    (hcorrespond : ∀ k x, L k x ↔ isTrue k (encode k x))
    (hcomplete : ∀ k, hasPerfectCompleteness (ip k) (isTrue k) (honest k))
    (hsound : ∀ k, hasSoundnessError (ip k) (isTrue k) (ε_S k))
    (εbound : ∀ k x, ε_S k (encode k x) ≤ 1/3) :
    InIPFamily L := by
  refine InIPFamily.mk ip encode honest (fun k x => ε_S k (encode k x))
    εbound ?_ ?_
  · intro k x hx
    exact hcomplete k (encode k x) ((hcorrespond k x).mp hx)
  · intro k x hx P
    exact hsound k (encode k x) P (fun h => hx ((hcorrespond k x).mpr h))
