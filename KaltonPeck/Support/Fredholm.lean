import KaltonPeck.Support.Definitions
import KaltonPeck.Support.Forms
import Mathlib.Analysis.Normed.Module.ContinuousInverse

namespace KaltonPeck.Support.Fredholm

noncomputable section

/-- The canonical linear equivalence from a quotient by a kernel onto the range.

Blueprint: `lem:quotient-range`; audit: `COV-QUOT-KER-RANGE`. -/
def quotientKernelRangeEquiv {X Y : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y] (A : X →L[ℝ] Y) :
    (X ⧸ A.toLinearMap.ker) ≃ₗ[ℝ] A.toLinearMap.range := by
  exact A.toLinearMap.quotKerEquivRange

/-- Evaluation formula for the quotient-by-kernel equivalence.

Blueprint: `lem:quotient-range`; audit: `COV-QUOT-KER-RANGE`. -/
theorem quotientKernelRangeEquiv_apply_mk {X Y : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y] (A : X →L[ℝ] Y)
    (x : X) :
    ((quotientKernelRangeEquiv A (Submodule.Quotient.mk x) : A.toLinearMap.range) : Y) =
      A x := by
  sorry

/-- Finite-rank consequences of the quotient-by-kernel equivalence.

Blueprint: `lem:quotient-range`; audit: `COV-QUOT-KER-RANGE`. -/
theorem quotientKernelRange {X Y : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y] (A : X →L[ℝ] Y)
    (hA : HasFiniteRank A) :
    IsClosed (A.toLinearMap.ker : Set X) ∧
      FiniteDimensional ℝ (X ⧸ A.toLinearMap.ker) ∧
        Module.finrank ℝ (X ⧸ A.toLinearMap.ker) =
          Module.finrank ℝ A.toLinearMap.range ∧
            Module.finrank ℝ (X ⧸ A.toLinearMap.ker) = operatorRank A := by
  sorry

/-- Fredholmness is invariant under bounded equivalences on the source and target.

Blueprint: `lem:fredholm-calculus`, item 1; audit: `INF-FREDHOLM-CALCULUS`. -/
theorem isFredholm_equiv_comp {X Y X' Y' : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] [CompleteSpace X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [CompleteSpace Y] [NormedAddCommGroup X'] [NormedSpace ℝ X'] [CompleteSpace X']
    [NormedAddCommGroup Y'] [NormedSpace ℝ Y'] [CompleteSpace Y'] (A : X →L[ℝ] Y)
    (U : Y ≃L[ℝ] Y') (V : X' ≃L[ℝ] X) :
    IsFredholm A ↔
      IsFredholm (U.toContinuousLinearMap.comp (A.comp V.toContinuousLinearMap)) := by
  sorry

/-- The kernel equivalence induced by bounded equivalences on the source and target.

Blueprint: `lem:fredholm-calculus`, item 1; audit: `INF-FREDHOLM-CALCULUS`. -/
def kernelEquivOfEquivComp {X Y X' Y' : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup X'] [NormedSpace ℝ X'] [NormedAddCommGroup Y']
    [NormedSpace ℝ Y'] (A : X →L[ℝ] Y) (U : Y ≃L[ℝ] Y') (V : X' ≃L[ℝ] X) :
    (U.toContinuousLinearMap.comp (A.comp V.toContinuousLinearMap)).toLinearMap.ker
      ≃ₗ[ℝ] A.toLinearMap.ker := by
  let f :
      (U.toContinuousLinearMap.comp
        (A.comp V.toContinuousLinearMap)).toLinearMap.ker →ₗ[ℝ]
        A.toLinearMap.ker :=
    { toFun := fun x => ⟨V.toLinearEquiv x, by
        have hx := x.property
        change U.toLinearEquiv (A.toLinearMap (V.toLinearEquiv x)) = 0 at hx
        apply U.toLinearEquiv.injective
        simpa only [map_zero] using hx⟩
      map_add' := by
        intro x y
        exact Subtype.ext (V.toLinearEquiv.map_add x y)
      map_smul' := by
        intro c x
        exact Subtype.ext (V.toLinearEquiv.map_smul c x) }
  apply LinearEquiv.ofBijective f
  constructor
  · intro x y h
    exact Subtype.ext (V.toLinearEquiv.injective (congrArg Subtype.val h))
  · intro y
    refine ⟨⟨V.symm.toLinearEquiv y, ?_⟩, ?_⟩
    · change U (A (V (V.symm y))) = 0
      rw [V.apply_symm_apply]
      have hy := y.property
      change A y = 0 at hy
      rw [hy, map_zero]
    · exact Subtype.ext (V.apply_symm_apply (y : X))

/-- The cokernel equivalence induced by bounded equivalences on the source and target.

Blueprint: `lem:fredholm-calculus`, item 1; audit: `INF-FREDHOLM-CALCULUS`. -/
def cokernelEquivOfEquivComp {X Y X' Y' : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup X'] [NormedSpace ℝ X'] [NormedAddCommGroup Y']
    [NormedSpace ℝ Y'] (A : X →L[ℝ] Y) (U : Y ≃L[ℝ] Y') (V : X' ≃L[ℝ] X) :
    (Y' ⧸ (U.toContinuousLinearMap.comp
      (A.comp V.toContinuousLinearMap)).toLinearMap.range) ≃ₗ[ℝ]
        (Y ⧸ A.toLinearMap.range) := by
  refine Submodule.Quotient.equiv
    (U.toContinuousLinearMap.comp
      (A.comp V.toContinuousLinearMap)).toLinearMap.range
    A.toLinearMap.range U.symm.toLinearEquiv ?_
  ext y
  constructor
  · rintro ⟨z, ⟨x, hx⟩, hz⟩
    subst z
    subst y
    refine ⟨V x, ?_⟩
    simp
  · rintro ⟨x, rfl⟩
    refine ⟨U (A x), ?_, U.symm_apply_apply (A x)⟩
    refine ⟨V.symm x, ?_⟩
    simp

/-- Nullity is invariant under bounded equivalences on the source and target.

Blueprint: `lem:fredholm-calculus`, item 1; audit: `INF-FREDHOLM-CALCULUS`. -/
theorem nullity_equiv_comp {X Y X' Y' : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup X'] [NormedSpace ℝ X'] [NormedAddCommGroup Y']
    [NormedSpace ℝ Y'] (A : X →L[ℝ] Y) (U : Y ≃L[ℝ] Y') (V : X' ≃L[ℝ] X) :
    nullity (U.toContinuousLinearMap.comp (A.comp V.toContinuousLinearMap)) = nullity A := by
  sorry

/-- Cokernel dimension is invariant under bounded equivalences on source and target.

Blueprint: `lem:fredholm-calculus`, item 1; audit: `INF-FREDHOLM-CALCULUS`. -/
theorem cokernelFinrank_equiv_comp {X Y X' Y' : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup X'] [NormedSpace ℝ X'] [NormedAddCommGroup Y']
    [NormedSpace ℝ Y'] (A : X →L[ℝ] Y) (U : Y ≃L[ℝ] Y') (V : X' ≃L[ℝ] X) :
    Module.finrank ℝ
        (Y' ⧸ (U.toContinuousLinearMap.comp
          (A.comp V.toContinuousLinearMap)).toLinearMap.range) =
      Module.finrank ℝ (Y ⧸ A.toLinearMap.range) := by
  sorry

/-- Fredholm index is invariant under bounded equivalences on the source and target.

Blueprint: `lem:fredholm-calculus`, item 1; audit: `INF-FREDHOLM-CALCULUS`. -/
theorem fredholmIndex_equiv_comp {X Y X' Y' : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup X'] [NormedSpace ℝ X'] [NormedAddCommGroup Y']
    [NormedSpace ℝ Y'] (A : X →L[ℝ] Y) (U : Y ≃L[ℝ] Y') (V : X' ≃L[ℝ] X) :
    fredholmIndex (U.toContinuousLinearMap.comp (A.comp V.toContinuousLinearMap)) =
      fredholmIndex A := by
  sorry

/-- Multiplication by a nonzero real scalar preserves Fredholmness and index.

Blueprint: `lem:fredholm-calculus`, item 2; audit: `INF-FREDHOLM-CALCULUS`. -/
theorem fredholm_smul {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [CompleteSpace X] [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    (A : X →L[ℝ] Y) (a : ℝ) (ha : a ≠ 0) :
    (IsFredholm (a • A) ↔ IsFredholm A) ∧ fredholmIndex (a • A) = fredholmIndex A := by
  sorry

/-- Injective postcomposition does not change the kernel.

Blueprint: `lem:fredholm-calculus`, item 2; audit: `INF-FREDHOLM-CALCULUS`. -/
theorem ker_comp_of_injective {X Y Z : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] (A : X →L[ℝ] Y) (C : Y →L[ℝ] Z)
    (hC : Function.Injective C) :
    (C.comp A).toLinearMap.ker = A.toLinearMap.ker := by
  sorry

/-- A composition of Fredholm maps is Fredholm.

Blueprint: `lem:fredholm-calculus`, item 3; audit: `INF-FREDHOLM-CALCULUS`. -/
theorem isFredholm_comp {X Y Z : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] [CompleteSpace X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [CompleteSpace Y] [NormedAddCommGroup Z] [NormedSpace ℝ Z] [CompleteSpace Z]
    (A : X →L[ℝ] Y) (B : Y →L[ℝ] Z) (hA : IsFredholm A) (hB : IsFredholm B) :
    IsFredholm (B.comp A) := by
  sorry

/-- Fredholm index is additive under composition.

Blueprint: `lem:fredholm-calculus`, item 3; audit: `INF-FREDHOLM-CALCULUS`. -/
theorem fredholmIndex_comp {X Y Z : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] [CompleteSpace X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [CompleteSpace Y] [NormedAddCommGroup Z] [NormedSpace ℝ Z] [CompleteSpace Z]
    (A : X →L[ℝ] Y) (B : Y →L[ℝ] Z) (hA : IsFredholm A) (hB : IsFredholm B) :
    fredholmIndex (B.comp A) = fredholmIndex B + fredholmIndex A := by
  sorry

/-- A bounded left inverse gives zero kernel, finite-dimensional kernel, and closed range.

Blueprint: `lem:fredholm-calculus`, item 4; audit: `INF-FREDHOLM-CALCULUS`. -/
theorem leftInverseKernelRange {X Y : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] [CompleteSpace X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [CompleteSpace Y] (A : X →L[ℝ] Y) (hA : A.HasLeftInverse) :
    A.toLinearMap.ker = ⊥ ∧
      FiniteDimensional ℝ A.toLinearMap.ker ∧ IsClosed (A.toLinearMap.range : Set Y) := by
  sorry

/-- Range and index theorem for a skew Fredholm operator into the strong dual.

Blueprint: `lem:skew-fredholm-range`; audit: `AUX-SKEW-FREDHOLM-INDEX-RANGE`. -/
theorem skewFredholmRange {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [CompleteSpace X] (S : X →L[ℝ] StrongDual ℝ X)
    (hReflexive : Function.Surjective (NormedSpace.inclusionInDoubleDual ℝ X))
    (hFredholm : IsFredholm S)
    (hSkew : (transpose S).comp (NormedSpace.inclusionInDoubleDual ℝ X) = -S) :
    fredholmIndex S = 0 ∧
      S.toLinearMap.range = Forms.continuousAnnihilator S.toLinearMap.ker ∧
        IsClosed (S.toLinearMap.range : Set (StrongDual ℝ X)) := by
  sorry

end

end KaltonPeck.Support.Fredholm
