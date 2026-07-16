import KaltonPeck.Support.Definitions

set_option autoImplicit false

namespace KaltonPeck.Support.TargetSupport

noncomputable section

/-- A codimension-one complex structure extends by the identity on a one-dimensional topological
complement, and its square defect has exactly rank one.
Blueprint label: `lem:hyperplane-extension`; audit IDs `HID-HYPERPLANE-BLOCK-EXTENSION`,
`HID-RANK-ONE-COMPUTATION`, and `COV-HYPERPLANE-EXT`. -/
theorem hyperplaneExtension {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [CompleteSpace X] (H : Submodule ℝ X) (hH : IsHyperplane H) (J : H →L[ℝ] H)
    (hJ : IsComplexStructure J) :
    ∃ F : Submodule ℝ X,
      H.IsTopCompl F ∧ IsClosed (F : Set X) ∧ Module.finrank ℝ F = 1 ∧
        ∃ T : X →L[ℝ] X,
          (∀ h : H, T h = (J h : X)) ∧
            (∀ f : F, T f = (f : X)) ∧
            (∀ (h : H) (f : F),
              T ((h : X) + (f : X)) = (J h : X) + (f : X)) ∧
            (∀ (h : H) (f : F),
              (T ^ 2 + (1 : X →L[ℝ] X)) ((h : X) + (f : X)) = 2 • (f : X)) ∧
            (T ^ 2 + 1).toLinearMap.range = F ∧
              HasFiniteRank (T ^ 2 + 1) ∧ operatorRank (T ^ 2 + 1) = 1 := by
  sorry

end


end KaltonPeck.Support.TargetSupport
