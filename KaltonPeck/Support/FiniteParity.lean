import KaltonPeck.Support.Definitions
import Mathlib.LinearAlgebra.BilinearForm.Properties

namespace KaltonPeck.Support.FiniteParity

noncomputable section

/-- A finite-dimensional real alternating bilinear form has even rank, and its radical has the
same parity as the ambient space.

Blueprint: `lem:finite-alt-even`; audit: `LEM-FINITE-ALT-RANK-EVEN`. -/
theorem finiteAlternatingRankEven {V : Type*} [AddCommGroup V] [Module ℝ V]
    [FiniteDimensional ℝ V] (c : LinearMap.BilinForm ℝ V) (hc : c.IsAlt) :
    Even (Module.finrank ℝ c.range) ∧
      Nat.ModEq 2 (Module.finrank ℝ c.ker) (Module.finrank ℝ V) := by
  sorry

/-- Continuous finite-dimensional wrapper for even rank of an alternating form.

Blueprint: `lem:finite-alt-even`; audit: `LEM-FINITE-ALT-RANK-EVEN`. -/
theorem finiteContinuousAlternatingRankEven {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [FiniteDimensional ℝ V] (c : ContinuousAlternatingForm V) :
    Even (Module.finrank ℝ c.toDual.toLinearMap.range) ∧
      Nat.ModEq 2 (Module.finrank ℝ c.radical) (Module.finrank ℝ V) := by
  sorry

/-- A finite-dimensional real vector space carrying an endomorphism squaring to `-I` has even
dimension.

Blueprint: `lem:finite-complex-even`; audit: `LEM-COMPLEX-STRUCTURE-EVEN-DIM`. -/
theorem finiteComplexDimensionEven {V : Type*} [AddCommGroup V] [Module ℝ V]
    [FiniteDimensional ℝ V] (J : Module.End ℝ V) (hJ : J ^ 2 = -1) :
    Even (Module.finrank ℝ V) := by
  sorry

/-- Continuous-linear wrapper for finite complex structures.

Blueprint: `lem:finite-complex-even`; audit: `LEM-COMPLEX-STRUCTURE-EVEN-DIM`. -/
theorem finiteContinuousComplexDimensionEven {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [FiniteDimensional ℝ V] (J : V →L[ℝ] V)
    (hJ : IsComplexStructure J) : Even (Module.finrank ℝ V) := by
  sorry

/-- A finite-dimensional invariant subspace of a real complex structure has even dimension.

Blueprint: `lem:finite-complex-even`; audit: `LEM-COMPLEX-STRUCTURE-EVEN-DIM`. -/
theorem finiteInvariantSubmoduleComplexDimensionEven {V : Type*} [AddCommGroup V]
    [Module ℝ V] (J : Module.End ℝ V) (W : Submodule ℝ V) [FiniteDimensional ℝ W]
    (hW : ∀ x : W, J x ∈ W) (hJ : ∀ x : W, J (J x) = -(x : V)) :
    Even (Module.finrank ℝ W) := by
  sorry

end

end KaltonPeck.Support.FiniteParity
