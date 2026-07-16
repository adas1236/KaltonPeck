import KaltonPeck.Support.Definitions
import KaltonPeck.Support.Forms
import KaltonPeck.Support.Fredholm
import KaltonPeck.Support.FiniteParity
import KaltonPeck.Support.FiniteCodim
import KaltonPeck.Support.PathParity
import KaltonPeck.Support.GeneralRank
import KaltonPeck.Support.Coordinates
import KaltonPeck.Support.Symplectic
import KaltonPeck.Support.GraphFredholm
import KaltonPeck.Support.TargetSupport

namespace KaltonPeck

noncomputable section

/-- A strong continuous alternating form on a real normed space. -/
structure StrongSymplecticForm (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] where
  /-- The continuous linear equivalence induced by the strong symplectic form. -/
  toDual : X ≃L[ℝ] StrongDual ℝ X
  alternating : ∀ x, toDual x x = 0

/-- The transpose of a bounded linear map between real normed spaces. -/
def transpose {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] (T : X →L[ℝ] Y) :
    StrongDual ℝ Y →L[ℝ] StrongDual ℝ X :=
  (ContinuousLinearMap.flip (ContinuousLinearMap.compL ℝ X Y ℝ)) T

/-- The adjoint of a bounded operator with respect to a strong symplectic form. -/
def StrongSymplecticForm.adjoint {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (ω : StrongSymplecticForm X) (T : X →L[ℝ] X) : X →L[ℝ] X :=
  ω.toDual.symm.toContinuousLinearMap.comp
    ((transpose T).comp ω.toDual.toContinuousLinearMap)

/-- A bounded linear map is Fredholm when it has finite-dimensional kernel, closed range,
and finite-dimensional cokernel. -/
def IsFredholm {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] (T : X →L[ℝ] Y) : Prop :=
  FiniteDimensional ℝ T.toLinearMap.ker ∧
    IsClosed (T.toLinearMap.range : Set Y) ∧
      FiniteDimensional ℝ (Y ⧸ T.toLinearMap.range)

/-- A bounded linear map has finite rank when its algebraic range is finite-dimensional. -/
def HasFiniteRank {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] (T : X →L[ℝ] Y) : Prop :=
  FiniteDimensional ℝ T.toLinearMap.range

/-- The rank of a bounded linear map, used when its range is finite-dimensional. -/
def operatorRank {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] (T : X →L[ℝ] Y) : ℕ :=
  Module.finrank ℝ T.toLinearMap.range

/-- The dimension of the kernel of a bounded linear map, used when the kernel is
finite-dimensional. -/
def nullity {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] (T : X →L[ℝ] Y) : ℕ :=
  Module.finrank ℝ T.toLinearMap.ker

/-- A complex structure on a real normed space is a bounded operator squaring to `-I`. -/
def IsComplexStructure {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (J : X →L[ℝ] X) : Prop :=
  J ^ 2 = -1

/-- A closed codimension-one linear subspace. -/
def IsHyperplane {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (H : Submodule ℝ X) : Prop :=
  IsClosed (H : Set X) ∧ Module.finrank ℝ (X ⧸ H) = 1

/-- A real sequence is square-summable. -/
def IsSquareSummable (x : ℕ → ℝ) : Prop :=
  Summable fun n ↦ x n ^ 2

/-- The usual `ℓ₂` norm, defined on all real sequences and used on square-summable ones. -/
def l2Norm (x : ℕ → ℝ) : ℝ :=
  Real.sqrt (∑' n, x n ^ 2)

/-- The Kalton--Peck centralizer, with Lean's `Real.log 0 = 0` supplying the zero convention. -/
def centralizer (x : ℕ → ℝ) (n : ℕ) : ℝ :=
  2 * x n * Real.log (|x n| / l2Norm x)

/-- The admissible coordinate pairs in the usual real Kalton--Peck presentation. -/
def IsAdmissiblePair (p : (ℕ → ℝ) × (ℕ → ℝ)) : Prop :=
  IsSquareSummable p.2 ∧ IsSquareSummable (p.1 - centralizer p.2)

/-- The standard quasi-norm used to present the real Kalton--Peck space. -/
def kaltonPeckQuasiNorm (p : (ℕ → ℝ) × (ℕ → ℝ)) : ℝ :=
  l2Norm (p.1 - centralizer p.2) + l2Norm p.2

/-- A real Banach space carrying the standard Kalton--Peck coordinate presentation. -/
structure RealKaltonPeckPresentation (X : Type*) [NormedAddCommGroup X]
    [NormedSpace ℝ X] where
  /-- Linear coordinates identifying the space with the admissible Kalton--Peck pairs. -/
  coordinates : X →ₗ[ℝ] (ℕ → ℝ) × (ℕ → ℝ)
  coordinates_injective : Function.Injective coordinates
  coordinates_mem : ∀ z, IsAdmissiblePair (coordinates z)
  coordinates_surjective : ∀ p, IsAdmissiblePair p → ∃ z, coordinates z = p
  norm_equivalent : ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ z,
    c * kaltonPeckQuasiNorm (coordinates z) ≤ ‖z‖ ∧
      ‖z‖ ≤ C * kaltonPeckQuasiNorm (coordinates z)

/- Source: paper.tex, label `thm:rank_parity_general`, lines 131--138, repeated as
`thm:rank-parity` at lines 504--509. Approved representation: a real symplectic Banach space is
unpacked as a complete real normed space with `StrongSymplecticForm`; bounded operators,
Fredholmness, finite rank, rank, nullity, and congruence modulo two use the definitions above.
Approval record: `agent_outputs/AUDIT.md`, decision `DEC-USER-STATEMENT-CONFIRM`. -/
theorem rankParityGeneral {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [CompleteSpace X] (ω : StrongSymplecticForm X) (T : X →L[ℝ] X)
    (hFredholm : IsFredholm (1 + ω.adjoint T * T))
    (hFiniteRank : HasFiniteRank (T ^ 2 + 1)) :
    Nat.ModEq 2 (operatorRank (T ^ 2 + 1)) (nullity (1 + ω.adjoint T * T)) := by
  sorry

/- Source: paper.tex, label `thm:rank_parity_Z2`, lines 109--114. Approved representation: `Z₂`
ranges over complete real normed spaces carrying `RealKaltonPeckPresentation`; `L(Z₂)` is modeled
by bounded real-linear endomorphisms, finite rank by `HasFiniteRank`, and evenness by `Even`.
Approval record: `agent_outputs/AUDIT.md`, decision `DEC-USER-STATEMENT-CONFIRM`. -/
theorem rankParityZ2 {Z₂ : Type*} [NormedAddCommGroup Z₂] [NormedSpace ℝ Z₂]
    [CompleteSpace Z₂] (_hZ₂ : RealKaltonPeckPresentation Z₂) (T : Z₂ →L[ℝ] Z₂)
    (hFiniteRank : HasFiniteRank (T ^ 2 + 1)) : Even (operatorRank (T ^ 2 + 1)) := by
  sorry

/- Source: paper.tex, label `cor:no-hyperplane-complex`, lines 718--720. Approved representation:
`Z₂` carries `RealKaltonPeckPresentation`; a hyperplane is a closed codimension-one submodule via
`IsHyperplane`, and a complex structure is a bounded real-linear endomorphism squaring to `-I` via
`IsComplexStructure`. Approval record: `agent_outputs/AUDIT.md`, decision
`DEC-USER-STATEMENT-CONFIRM`. -/
theorem noHyperplaneComplexStructure {Z₂ : Type*} [NormedAddCommGroup Z₂]
    [NormedSpace ℝ Z₂] [CompleteSpace Z₂] (_hZ₂ : RealKaltonPeckPresentation Z₂) :
    ∀ H : Submodule ℝ Z₂, IsHyperplane H → ¬∃ J : H →L[ℝ] H, IsComplexStructure J := by
  sorry

end

end KaltonPeck
