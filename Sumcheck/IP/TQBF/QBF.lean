import Sumcheck.IP.SharpSAT.CNF

namespace TQBF

open SharpSAT

/-- A quantifier in a TQBF prefix — either universal or existential. -/
inductive Quantifier
  | «forall»
  | «exists»
  deriving DecidableEq, Repr

/-- A Totally Quantified Boolean Formula over `n` variables: a quantifier
prefix (outermost first, so `quantifiers 0` binds first) wrapping a 3-CNF
matrix. Choosing 3-CNF as the matrix matches the standard PSPACE-complete
formulation of TQBF. -/
structure QBF (n : ℕ) where
  quantifiers : Fin n → Quantifier
  matrix : CNF3 n

/-- Recursive evaluator over a quantifier prefix of length `n` and a Boolean
function on `n`-tuples. Peels off the outermost quantifier by splitting on
the value of the bound variable and recurring on the tail. -/
def valueAt : (n : ℕ) → (Fin n → Quantifier) → ((Fin n → Bool) → Bool) → Bool
  | 0, _, f => f Fin.elim0
  | n + 1, pre, f =>
    let cont (b : Bool) : Bool :=
      valueAt n (fun i => pre i.succ) (fun y => f (Fin.cons b y))
    match pre 0 with
    | .«forall» => cont false && cont true
    | .«exists» => cont false || cont true

/-- The truth value of a closed TQBF formula. -/
def QBF.value {n : ℕ} (Q : QBF n) : Bool :=
  valueAt n Q.quantifiers Q.matrix.eval

/-- A TQBF formula is valid if its closed value is true. This is the predicate
for TQBF language membership. -/
def QBF.Valid {n : ℕ} (Q : QBF n) : Prop :=
  Q.value = true

instance {n : ℕ} (Q : QBF n) : Decidable Q.Valid := by
  unfold QBF.Valid; infer_instance

end TQBF
