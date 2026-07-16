import KaltonPeck.Support.Definitions
import Mathlib.Analysis.Normed.Module.DoubleDual
import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient

namespace KaltonPeck.Support.Forms

noncomputable section

/-- Continuous functionals on `X` that vanish on the subspace `W`.

Blueprint support for `lem:double-annihilator` and `lem:quotient-dual`; audit:
`DEF-ANNIHILATOR`. -/
def continuousAnnihilator {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (W : Submodule ℝ X) : Submodule ℝ (StrongDual ℝ X) := by
  exact ((ContinuousLinearMap.compL ℝ W X ℝ).flip W.subtypeL).ker

/-- Hahn--Banach continuous double-annihilator theorem for a closed subspace.

Blueprint: `lem:double-annihilator`; audit: `AUX-CONT-DOUBLE-ANNIHILATOR`. -/
theorem continuousDoubleAnnihilator {X : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] [CompleteSpace X] (W : Submodule ℝ X)
    (hW : IsClosed (W : Set X)) :
    {x : X | ∀ φ : continuousAnnihilator W, (φ : StrongDual ℝ X) x = 0} = (W : Set X) := by
  sorry

/-- Pullback along the quotient map as a continuous equivalence with the annihilator.

Blueprint: `lem:quotient-dual`; audit: `AUX-CONT-QUOTIENT-DUAL-ANNIHILATOR`. -/
def quotientDualEquivAnnihilator {X : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] [CompleteSpace X] (W : Submodule ℝ X)
    [hW : IsClosed (W : Set X)] :
    StrongDual ℝ (X ⧸ W) ≃L[ℝ] continuousAnnihilator W := by
  have hWComplete : IsComplete (W : Set X) := hW.isComplete
  letI : IsClosed (W : Set X) := hWComplete.isClosed
  let pullback : StrongDual ℝ (X ⧸ W) →L[ℝ] continuousAnnihilator W :=
    ((ContinuousLinearMap.compL ℝ X (X ⧸ W) ℝ).flip W.mkQL).codRestrict
      (continuousAnnihilator W) (fun φ => by
        change ((ContinuousLinearMap.compL ℝ W X ℝ).flip W.subtypeL)
          (((ContinuousLinearMap.compL ℝ X (X ⧸ W) ℝ).flip W.mkQL) φ) = 0
        apply ContinuousLinearMap.ext
        intro x
        change φ (Submodule.Quotient.mk (x : X)) = 0
        rw [(Submodule.Quotient.mk_eq_zero W).2 x.property, map_zero])
  let inverseLinear : continuousAnnihilator W →ₗ[ℝ] StrongDual ℝ (X ⧸ W) :=
    { toFun := fun φ => W.liftQL (φ : StrongDual ℝ X) (by
        intro x hx
        have hφ := φ.property
        change ((ContinuousLinearMap.compL ℝ W X ℝ).flip W.subtypeL) φ.val = 0 at hφ
        exact DFunLike.congr_fun hφ ⟨x, hx⟩)
      map_add' := by
        intro φ ψ
        apply ContinuousLinearMap.ext
        rintro ⟨x⟩
        rfl
      map_smul' := by
        intro a φ
        apply ContinuousLinearMap.ext
        rintro ⟨x⟩
        rfl }
  have hinverse_bound : ∀ φ : continuousAnnihilator W, ‖inverseLinear φ‖ ≤ 1 * ‖φ‖ := by
    intro φ
    rw [one_mul]
    apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg φ)
    intro q
    let f : NormedAddGroupHom X ℝ :=
      φ.val.toLinearMap.toAddMonoidHom.mkNormedAddGroupHom ‖φ‖
        (fun x => φ.val.le_opNorm x)
    have hf : ‖f‖ ≤ ‖φ‖ :=
      NormedAddGroupHom.opNorm_le_bound f (norm_nonneg φ) (fun x => φ.val.le_opNorm x)
    have hzero : ∀ x ∈ W.toAddSubgroup, f x = 0 := by
      intro x hx
      have hφ := φ.property
      change ((ContinuousLinearMap.compL ℝ W X ℝ).flip W.subtypeL) φ.val = 0 at hφ
      exact DFunLike.congr_fun hφ ⟨x, hx⟩
    calc
      ‖inverseLinear φ q‖ ≤ ‖f‖ * ‖q‖ := by
        exact QuotientAddGroup.norm_lift_apply_le f hzero q
      _ ≤ ‖φ‖ * ‖q‖ := mul_le_mul_of_nonneg_right hf (norm_nonneg q)
  let inverse : continuousAnnihilator W →L[ℝ] StrongDual ℝ (X ⧸ W) :=
    LinearMap.mkContinuous (E := continuousAnnihilator W) (F := StrongDual ℝ (X ⧸ W))
      (σ := RingHom.id ℝ) inverseLinear 1 hinverse_bound
  let e : StrongDual ℝ (X ⧸ W) ≃ₗ[ℝ] continuousAnnihilator W :=
    { toFun := pullback
      invFun := inverse
      left_inv := by
        intro φ
        apply ContinuousLinearMap.ext
        rintro ⟨x⟩
        rfl
      right_inv := by
        intro φ
        apply Subtype.ext
        apply ContinuousLinearMap.ext
        intro x
        rfl
      map_add' := pullback.map_add
      map_smul' := pullback.map_smul }
  exact ContinuousLinearEquiv.mk e pullback.continuous inverse.continuous

/-- Evaluation formula for pullback along the quotient map.

Blueprint: `lem:quotient-dual`; audit: `AUX-CONT-QUOTIENT-DUAL-ANNIHILATOR`. -/
theorem quotientDualEquivAnnihilator_apply {X : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] [CompleteSpace X] (W : Submodule ℝ X)
    [hW : IsClosed (W : Set X)] (φ : StrongDual ℝ (X ⧸ W)) (x : X) :
    ((quotientDualEquivAnnihilator W φ : continuousAnnihilator W) : StrongDual ℝ X) x =
      φ (Submodule.Quotient.mk x) := by
  sorry

/-- The transpose identity that relates a strong alternating form to the double-dual inclusion.

Blueprint: `lem:strong-reflexive`; audit: `AUX-STRONG-SYMPLECTIC-REFLEXIVE`. -/
theorem strongSymplecticTransposeInclusion {X : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] [CompleteSpace X] (ω : StrongSymplecticForm X) :
    (transpose ω.toDual.toContinuousLinearMap).comp
        (NormedSpace.inclusionInDoubleDual ℝ X) =
      -ω.toDual.toContinuousLinearMap := by
  sorry

/-- Every strong symplectic real Banach space is reflexive.

Blueprint: `lem:strong-reflexive`; audit: `AUX-STRONG-SYMPLECTIC-REFLEXIVE`. -/
theorem strongSymplecticReflexive {X : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] [CompleteSpace X] (ω : StrongSymplecticForm X) :
    Function.Surjective (NormedSpace.inclusionInDoubleDual ℝ X) := by
  sorry

/-- The symplectic adjoint of the identity is the identity.

Blueprint: `lem:adjoint-calculus`; audit: `AUX-SYMPLECTIC-ADJOINT-CALCULUS`. -/
theorem adjoint_one {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [CompleteSpace X] (ω : StrongSymplecticForm X) : ω.adjoint 1 = 1 := by
  sorry

/-- The symplectic adjoint is additive.

Blueprint: `lem:adjoint-calculus`; audit: `AUX-SYMPLECTIC-ADJOINT-CALCULUS`. -/
theorem adjoint_add {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [CompleteSpace X] (ω : StrongSymplecticForm X) (A B : X →L[ℝ] X) :
    ω.adjoint (A + B) = ω.adjoint A + ω.adjoint B := by
  sorry

/-- The symplectic adjoint commutes with real scalar multiplication.

Blueprint: `lem:adjoint-calculus`; audit: `AUX-SYMPLECTIC-ADJOINT-CALCULUS`. -/
theorem adjoint_smul {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [CompleteSpace X] (ω : StrongSymplecticForm X) (a : ℝ) (A : X →L[ℝ] X) :
    ω.adjoint (a • A) = a • ω.adjoint A := by
  sorry

/-- The symplectic adjoint reverses composition.

Blueprint: `lem:adjoint-calculus`; audit: `AUX-SYMPLECTIC-ADJOINT-CALCULUS`. -/
theorem adjoint_mul {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [CompleteSpace X] (ω : StrongSymplecticForm X) (A B : X →L[ℝ] X) :
    ω.adjoint (A * B) = ω.adjoint B * ω.adjoint A := by
  sorry

/-- Taking the symplectic adjoint twice returns the original operator.

Blueprint: `lem:adjoint-calculus`; audit: `AUX-SYMPLECTIC-ADJOINT-CALCULUS`. -/
theorem adjoint_involutive {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [CompleteSpace X] (ω : StrongSymplecticForm X) (A : X →L[ℝ] X) :
    ω.adjoint (ω.adjoint A) = A := by
  sorry

/-- Evaluation identity characterizing the symplectic adjoint.

Blueprint: `lem:adjoint-calculus`; audit: `AUX-SYMPLECTIC-ADJOINT-CALCULUS`. -/
theorem adjoint_apply {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [CompleteSpace X] (ω : StrongSymplecticForm X) (A : X →L[ℝ] X) (x y : X) :
    ω.toDual (ω.adjoint A x) y = ω.toDual x (A y) := by
  sorry

end

end KaltonPeck.Support.Forms
