import KaltonPeck.Support.FiniteCodim
import KaltonPeck.Support.Forms
import KaltonPeck.Support.FiniteParity
import KaltonPeck.Support.Fredholm

namespace KaltonPeck.Support.GeneralRank

noncomputable section

/-- The kernel of `T ² + I` is closed, finite-codimensional, invariant under `T`, and carries
the restricted complex structure.

Blueprint: `lem:finite-rank-kernel`; audit: `AUX-FINITE-RANK-KERNEL-CODIM`. -/
theorem finiteRankPolynomialKernel {X : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] [CompleteSpace X] (T : X →L[ℝ] X)
    (hFiniteRank : HasFiniteRank (T ^ 2 + 1)) :
    IsClosed ((T ^ 2 + 1).toLinearMap.ker : Set X) ∧
      FiniteDimensional ℝ (X ⧸ (T ^ 2 + 1).toLinearMap.ker) ∧
      Module.finrank ℝ (X ⧸ (T ^ 2 + 1).toLinearMap.ker) =
        operatorRank (T ^ 2 + 1) ∧
      (∀ x : (T ^ 2 + 1).toLinearMap.ker,
        T (x : X) ∈ (T ^ 2 + 1).toLinearMap.ker) ∧
      ∀ x : (T ^ 2 + 1).toLinearMap.ker, T (T (x : X)) = -(x : X) := by
  sorry

/-- The auxiliary alternating Fredholm form, together with every identity used downstream.

Blueprint: `lem:rank-parity-form`; audit: `AUX-RANK-PARITY-FORM`. -/
structure RankParityFormData {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (omega : StrongSymplecticForm X) (T : X →L[ℝ] X) where
  /-- The auxiliary alternating form associated to `I + T⁺T`. -/
  form : ContinuousAlternatingForm X
  form_apply (x y : X) :
    form.toDual x y = omega.toDual ((1 + omega.adjoint T * T) x) y
  form_apply_expanded (x y : X) :
    form.toDual x y = omega.toDual x y + omega.toDual (T x) (T y)
  inducedOperator :
    form.toDual =
      omega.toDual.toContinuousLinearMap.comp (1 + omega.adjoint T * T)
  radical_eq_kernel :
    form.radical = (1 + omega.adjoint T * T).toLinearMap.ker
  isFredholm (hFredholm : IsFredholm (1 + omega.adjoint T * T)) :
    IsFredholm form.toDual

/-- The auxiliary form `eta(x,y) = omega((I + T⁺T)x,y)` and its structural identities.

Blueprint: `lem:rank-parity-form`. -/
def rankParityForm {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [CompleteSpace X] (omega : StrongSymplecticForm X) (T : X →L[ℝ] X) :
    RankParityFormData omega T := by
  let G : X →L[ℝ] X := 1 + omega.adjoint T * T
  have hadjoint (x y : X) :
      omega.toDual (omega.adjoint T x) y = omega.toDual x (T y) := by
    simp [StrongSymplecticForm.adjoint, transpose]
  let eta : ContinuousAlternatingForm X :=
    { toDual := omega.toDual.toContinuousLinearMap.comp G
      alternating := by
        intro x
        change omega.toDual (G x) x = 0
        rw [show G x = x + omega.adjoint T (T x) by simp [G]]
        rw [map_add, add_apply, hadjoint]
        simp [omega.alternating] }
  refine
    { form := eta
      form_apply := ?_
      form_apply_expanded := ?_
      inducedOperator := ?_
      radical_eq_kernel := ?_
      isFredholm := ?_ }
  · intro x y
    change omega.toDual (G x) y = _
    rfl
  · intro x y
    change omega.toDual (G x) y = _
    rw [show G x = x + omega.adjoint T (T x) by simp [G]]
    rw [map_add, add_apply, hadjoint]
  · change omega.toDual.toContinuousLinearMap.comp G = _
    rfl
  · ext x
    simp only [eta, ContinuousAlternatingForm.radical, LinearMap.mem_ker]
    change omega.toDual (G x) = 0 ↔ G x = 0
    constructor
    · intro hx
      apply omega.toDual.injective
      simpa using hx
    · intro hx
      rw [hx, map_zero]
  · intro hFredholm
    rcases hFredholm with ⟨hKernel, hRange, hCokernel⟩
    have hKernelEq :
        (omega.toDual.toContinuousLinearMap.comp G).toLinearMap.ker =
          G.toLinearMap.ker := by
      ext x
      simp only [LinearMap.mem_ker]
      change omega.toDual (G x) = 0 ↔ G x = 0
      constructor
      · intro hx
        apply omega.toDual.injective
        simpa using hx
      · intro hx
        rw [hx, map_zero]
    have hRangeEq :
        (omega.toDual.toContinuousLinearMap.comp G).toLinearMap.range =
          G.toLinearMap.range.map omega.toDual.toLinearEquiv.toLinearMap := by
      ext y
      constructor
      · rintro ⟨x, rfl⟩
        exact ⟨G x, ⟨x, rfl⟩, rfl⟩
      · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
        exact ⟨x, rfl⟩
    refine ⟨?_, ?_, ?_⟩
    · rw [hKernelEq]
      exact hKernel
    · rw [hRangeEq]
      apply IsComplete.isClosed
      change IsComplete (omega.toDual '' (G.toLinearMap.range : Set X))
      exact omega.toDual.isUniformEmbedding.isComplete_iff.mpr hRange.isComplete
    · let eCoker :
          (X ⧸ G.toLinearMap.range) ≃ₗ[ℝ]
            (StrongDual ℝ X ⧸
              (omega.toDual.toContinuousLinearMap.comp G).toLinearMap.range) :=
        Submodule.Quotient.equiv _ _ omega.toDual.toLinearEquiv hRangeEq.symm
      letI : FiniteDimensional ℝ (X ⧸ G.toLinearMap.range) := hCokernel
      exact FiniteDimensional.of_surjective eCoker.toLinearMap eCoker.surjective

/-- The restricted radical is `T`-invariant and has even real dimension.

Blueprint: `lem:restricted-radical-even`; audit: `AUX-ETA-T-INVARIANT-ON-E`,
`AUX-ETA-T-SKEW-ON-E`, `AUX-RESTRICTED-RADICAL-T-INVARIANT`, and
`LEM-COMPLEX-STRUCTURE-EVEN-DIM`. -/
theorem restrictedRadicalEven {X : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] [CompleteSpace X] (omega : StrongSymplecticForm X)
    (T : X →L[ℝ] X) (hFiniteRank : HasFiniteRank (T ^ 2 + 1))
    [FiniteDimensional ℝ
      ((rankParityForm omega T).form.restrictedRadical (T ^ 2 + 1).toLinearMap.ker)] :
    (∀ x : (rankParityForm omega T).form.restrictedRadical
        (T ^ 2 + 1).toLinearMap.ker,
      T (x : X) ∈
        (rankParityForm omega T).form.restrictedRadical (T ^ 2 + 1).toLinearMap.ker) ∧
      Even (Module.finrank ℝ
        ((rankParityForm omega T).form.restrictedRadical
          (T ^ 2 + 1).toLinearMap.ker)) := by
  sorry

end

end KaltonPeck.Support.GeneralRank
