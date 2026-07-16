import KaltonPeck.Support.Fredholm
import KaltonPeck.Support.FiniteParity

namespace KaltonPeck.Support.PathParity

noncomputable section

/-- A closed kernel complement, continuous dual coordinates, and the invertible range block.

The continuous equivalence `dualCoordinates` supplies the two continuous coordinate projections.
Blueprint: `lem:kernel-splitting`; audit: `AUX-FREDHOLM-KERNEL-COMPLEMENT` and
`AUX-ANNIHILATOR-DUAL-SPLIT`. -/
structure KernelSplittingData {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (eta : ContinuousAlternatingForm X) where
  kernelFiniteDimensional : FiniteDimensional ℝ eta.radical
  /-- A closed topological complement to the radical. -/
  complement : Submodule ℝ X
  complementClosed : IsClosed (complement : Set X)
  kernel_disjoint_complement : Disjoint eta.radical complement
  kernel_sup_complement : eta.radical ⊔ complement = ⊤
  /-- Continuous coordinates for the dual splitting induced by the complement. -/
  dualCoordinates :
    StrongDual ℝ X ≃L[ℝ]
      (Forms.continuousAnnihilator complement × Forms.continuousAnnihilator eta.radical)
  dualCoordinates_symm_apply
      (p : Forms.continuousAnnihilator complement ×
        Forms.continuousAnnihilator eta.radical) :
    (dualCoordinates.symm p : StrongDual ℝ X) =
      (p.1 : StrongDual ℝ X) + (p.2 : StrongDual ℝ X)
  /-- Restriction identifies the annihilator of the complement with the radical dual. -/
  annihilatorComplementEquivKernelDual :
    Forms.continuousAnnihilator complement ≃L[ℝ] StrongDual ℝ eta.radical
  annihilatorComplementEquivKernelDual_apply
      (phi : Forms.continuousAnnihilator complement) (f : eta.radical) :
    annihilatorComplementEquivKernelDual phi f = (phi : StrongDual ℝ X) (f : X)
  range_eq_annihilator :
    eta.toDual.toLinearMap.range = Forms.continuousAnnihilator eta.radical
  /-- The nondegenerate range block on the chosen complement. -/
  restrictionEquiv : complement ≃L[ℝ] Forms.continuousAnnihilator eta.radical
  restrictionEquiv_apply (y : complement) :
    (restrictionEquiv y : StrongDual ℝ X) = eta.toDual (y : X)

/-- The splitting package at a Fredholm alternating operator.

Blueprint: `lem:kernel-splitting`. -/
def kernelSplitting {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [CompleteSpace X] (eta : ContinuousAlternatingForm X)
    (hReflexive : Function.Surjective (NormedSpace.inclusionInDoubleDual ℝ X))
    (hFredholm : IsFredholm eta.toDual) : KernelSplittingData eta := by
  have hRange :
      eta.toDual.toLinearMap.range = Forms.continuousAnnihilator eta.radical := by
    letI : FiniteDimensional ℝ eta.radical := hFredholm.1
    let hComplemented :=
      Submodule.ClosedComplemented.of_finiteDimensional eta.radical
    let Y : Submodule ℝ X := hComplemented.complement
    let hTop : Submodule.IsTopCompl eta.radical Y :=
      hComplemented.isTopCompl_complement
    letI : CompleteSpace Y :=
      hComplemented.isClosed_complement.completeSpace_coe
    let e : (eta.radical × Y) ≃L[ℝ] X :=
      Submodule.prodEquivOfIsTopCompl eta.radical Y hTop
    have hRadical (f : eta.radical) : eta.toDual (f : X) = 0 := f.property
    have hDecomp (x : X) :
        ((e.symm x).1 : X) + ((e.symm x).2 : X) = x := by
      change e (e.symm x) = x
      exact e.apply_symm_apply x
    have hSkew (x y : X) : eta.toDual x y = -eta.toDual y x := by
      have h := eta.alternating (x + y)
      have hsum : eta.toDual x y + eta.toDual y x = 0 := by
        simpa [eta.alternating, add_assoc, add_left_comm, add_comm] using h
      exact eq_neg_of_add_eq_zero_left hsum
    let SY : Y →L[ℝ] StrongDual ℝ X := eta.toDual.comp Y.subtypeL
    have hSY_injective : Function.Injective SY := by
      intro y z hyz
      apply Subtype.ext
      have hzero : eta.toDual ((y - z : Y) : X) = 0 := by
        simpa [SY, sub_eq_zero] using sub_eq_zero.mpr hyz
      have hmemRadical : ((y - z : Y) : X) ∈ eta.radical := hzero
      have hmemY : ((y - z : Y) : X) ∈ Y := (y - z).property
      have hzmem : ((y - z : Y) : X) ∈ (⊥ : Submodule ℝ X) :=
        hTop.isCompl.disjoint.le_bot ⟨hmemRadical, hmemY⟩
      exact (Submodule.mem_bot ℝ).mp hzmem |> sub_eq_zero.mp
    have hSY_range : SY.toLinearMap.range = eta.toDual.toLinearMap.range := by
      apply le_antisymm
      · rintro phi ⟨y, rfl⟩
        exact ⟨(y : X), rfl⟩
      · rintro phi ⟨x, rfl⟩
        refine ⟨(e.symm x).2, ?_⟩
        change eta.toDual ((e.symm x).2 : X) = eta.toDual x
        calc
          eta.toDual ((e.symm x).2 : X) =
              eta.toDual (((e.symm x).1 : X) + ((e.symm x).2 : X)) := by
                rw [map_add, hRadical, zero_add]
          _ = eta.toDual x := congrArg eta.toDual (hDecomp x)
    have hSY_closed : IsClosed (Set.range SY) := by
      change IsClosed (SY.toLinearMap.range : Set (StrongDual ℝ X))
      rw [hSY_range]
      exact hFredholm.2.1
    let eRange : Y ≃L[ℝ] SY.toLinearMap.range :=
      ContinuousLinearMap.equivRange hSY_injective hSY_closed
    apply le_antisymm
    · rintro phi ⟨x, rfl⟩
      change ((ContinuousLinearMap.compL ℝ eta.radical X ℝ).flip
        eta.radical.subtypeL) (eta.toDual x) = 0
      apply ContinuousLinearMap.ext
      intro f
      change eta.toDual x (f : X) = 0
      rw [hSkew, hRadical f]
      exact neg_zero
    · intro phi hphi
      let phiY : StrongDual ℝ Y := (phi : StrongDual ℝ X).comp Y.subtypeL
      let g : StrongDual ℝ SY.toLinearMap.range :=
        phiY.comp eRange.symm.toContinuousLinearMap
      obtain ⟨G, hG, _⟩ := exists_extension_norm_eq SY.toLinearMap.range g
      obtain ⟨x, hx⟩ := hReflexive G
      refine ⟨-x, ?_⟩
      apply ContinuousLinearMap.ext
      intro z
      let y : Y := (e.symm z).2
      have hG_on_y : G (eta.toDual (y : X)) = phi (y : X) := by
        have heRange : eRange y = SY.rangeRestrict y :=
          congrFun (ContinuousLinearMap.coe_equivRange hSY_injective hSY_closed) y
        calc
          G (eta.toDual (y : X)) =
              G ((eRange y : SY.toLinearMap.range) : StrongDual ℝ X) := by
                rw [heRange]
                rfl
          _ = g (eRange y) := hG (eRange y)
          _ = phiY (eRange.symm (eRange y)) := rfl
          _ = phiY y := by rw [eRange.symm_apply_apply]
          _ = phi (y : X) := rfl
      have hphi_radical : phi (((e.symm z).1 : eta.radical) : X) = 0 := by
        have hzero := DFunLike.congr_fun hphi (e.symm z).1
        exact hzero
      calc
        eta.toDual (-x) z = -eta.toDual x z := by
          simp only [map_neg, neg_apply]
        _ = eta.toDual z x := by rw [hSkew]; simp
        _ = G (eta.toDual z) := by
          have h := DFunLike.congr_fun hx (eta.toDual z)
          change (eta.toDual z) x = G (eta.toDual z) at h
          exact h
        _ = G (eta.toDual (y : X)) := by
          congr 1
          change eta.toDual z = eta.toDual ((e.symm z).2 : X)
          calc
            eta.toDual z =
                eta.toDual (((e.symm z).1 : X) + ((e.symm z).2 : X)) :=
              congrArg eta.toDual (hDecomp z).symm
            _ = eta.toDual ((e.symm z).2 : X) := by
              rw [map_add, hRadical, zero_add]
        _ = phi (y : X) := hG_on_y
        _ = phi z := by
          rw [← hDecomp z, map_add, hphi_radical, zero_add]
  letI : FiniteDimensional ℝ eta.radical := hFredholm.1
  let hComplemented :=
    Submodule.ClosedComplemented.of_finiteDimensional eta.radical
  let Y : Submodule ℝ X := hComplemented.complement
  let hTop : Submodule.IsTopCompl eta.radical Y :=
    hComplemented.isTopCompl_complement
  letI : CompleteSpace Y :=
    hComplemented.isClosed_complement.completeSpace_coe
  let pF : X →L[ℝ] eta.radical :=
    eta.radical.projectionOntoL Y hTop
  let pY : X →L[ℝ] Y :=
    Y.projectionOntoL eta.radical hTop.symm
  have hProj (x : X) : (pF x : X) + (pY x : X) = x := by
    exact Submodule.projectionL_add_projectionL_eq_self hTop x
  let rF : StrongDual ℝ X →L[ℝ] StrongDual ℝ eta.radical :=
    (ContinuousLinearMap.compL ℝ eta.radical X ℝ).flip eta.radical.subtypeL
  let rY : StrongDual ℝ X →L[ℝ] StrongDual ℝ Y :=
    (ContinuousLinearMap.compL ℝ Y X ℝ).flip Y.subtypeL
  let lF : StrongDual ℝ eta.radical →L[ℝ] StrongDual ℝ X :=
    (ContinuousLinearMap.compL ℝ X eta.radical ℝ).flip pF
  let lY : StrongDual ℝ Y →L[ℝ] StrongDual ℝ X :=
    (ContinuousLinearMap.compL ℝ X Y ℝ).flip pY
  let lFA : StrongDual ℝ eta.radical →L[ℝ]
      Forms.continuousAnnihilator Y :=
    lF.codRestrict (Forms.continuousAnnihilator Y) (fun a => by
      change rY (lF a) = 0
      apply ContinuousLinearMap.ext
      intro y
      change a (pF (y : X)) = 0
      simp [pF])
  let lYA : StrongDual ℝ Y →L[ℝ]
      Forms.continuousAnnihilator eta.radical :=
    lY.codRestrict (Forms.continuousAnnihilator eta.radical) (fun a => by
      change rF (lY a) = 0
      apply ContinuousLinearMap.ext
      intro f
      change a (pY (f : X)) = 0
      simp [pY])
  let annYToF : Forms.continuousAnnihilator Y →L[ℝ]
      StrongDual ℝ eta.radical :=
    rF.comp (Forms.continuousAnnihilator Y).subtypeL
  let annYLinearEquiv :
      Forms.continuousAnnihilator Y ≃ₗ[ℝ] StrongDual ℝ eta.radical :=
    { toFun := annYToF
      invFun := lFA
      left_inv := by
        intro a
        apply Subtype.ext
        apply ContinuousLinearMap.ext
        intro x
        have haY : (a : StrongDual ℝ X) (pY x : X) = 0 := by
          have ha := a.property
          change rY (a : StrongDual ℝ X) = 0 at ha
          exact DFunLike.congr_fun ha (pY x)
        change (a : StrongDual ℝ X) (pF x : X) =
          (a : StrongDual ℝ X) x
        calc
          (a : StrongDual ℝ X) (pF x : X) =
              (a : StrongDual ℝ X) (pF x : X) +
                (a : StrongDual ℝ X) (pY x : X) := by rw [haY, add_zero]
          _ = (a : StrongDual ℝ X) ((pF x : X) + (pY x : X)) := by
            rw [map_add]
          _ = (a : StrongDual ℝ X) x :=
            congrArg (a : StrongDual ℝ X) (hProj x)
      right_inv := by
        intro a
        apply ContinuousLinearMap.ext
        intro f
        change a (pF (f : X)) = a f
        simp [pF]
      map_add' := annYToF.map_add
      map_smul' := annYToF.map_smul }
  let annYEquivF :
      Forms.continuousAnnihilator Y ≃L[ℝ] StrongDual ℝ eta.radical :=
    ContinuousLinearEquiv.mk annYLinearEquiv annYToF.continuous lFA.continuous
  let coordF : StrongDual ℝ X →L[ℝ] Forms.continuousAnnihilator Y :=
    lFA.comp rF
  let coordY : StrongDual ℝ X →L[ℝ]
      Forms.continuousAnnihilator eta.radical :=
    lYA.comp rY
  let coordinates : StrongDual ℝ X →L[ℝ]
      (Forms.continuousAnnihilator Y ×
        Forms.continuousAnnihilator eta.radical) :=
    coordF.prod coordY
  let sumCoordinates :
      (Forms.continuousAnnihilator Y ×
        Forms.continuousAnnihilator eta.radical) →L[ℝ] StrongDual ℝ X :=
    (Forms.continuousAnnihilator Y).subtypeL.coprod
      (Forms.continuousAnnihilator eta.radical).subtypeL
  let dualLinearEquiv :
      StrongDual ℝ X ≃ₗ[ℝ]
        (Forms.continuousAnnihilator Y ×
          Forms.continuousAnnihilator eta.radical) :=
    { toFun := coordinates
      invFun := sumCoordinates
      left_inv := by
        intro phi
        apply ContinuousLinearMap.ext
        intro x
        change phi (pF x : X) + phi (pY x : X) = phi x
        rw [← map_add, hProj]
      right_inv := by
        rintro ⟨a, b⟩
        apply Prod.ext
        · have hbF : rF (b : StrongDual ℝ X) = 0 := b.property
          change lFA (rF ((a : StrongDual ℝ X) + (b : StrongDual ℝ X))) = a
          rw [map_add, hbF, add_zero]
          exact annYLinearEquiv.left_inv a
        · have haY : rY (a : StrongDual ℝ X) = 0 := a.property
          change lYA (rY ((a : StrongDual ℝ X) + (b : StrongDual ℝ X))) = b
          rw [map_add, haY, zero_add]
          apply Subtype.ext
          apply ContinuousLinearMap.ext
          intro x
          have hbF : (b : StrongDual ℝ X) (pF x : X) = 0 := by
            have hb := b.property
            change rF (b : StrongDual ℝ X) = 0 at hb
            exact DFunLike.congr_fun hb (pF x)
          change (b : StrongDual ℝ X) (pY x : X) =
            (b : StrongDual ℝ X) x
          calc
            (b : StrongDual ℝ X) (pY x : X) =
                (b : StrongDual ℝ X) (pF x : X) +
                  (b : StrongDual ℝ X) (pY x : X) := by rw [hbF, zero_add]
            _ = (b : StrongDual ℝ X) ((pF x : X) + (pY x : X)) := by
              rw [map_add]
            _ = (b : StrongDual ℝ X) x :=
              congrArg (b : StrongDual ℝ X) (hProj x)
      map_add' := coordinates.map_add
      map_smul' := coordinates.map_smul }
  let dualEquiv :
      StrongDual ℝ X ≃L[ℝ]
        (Forms.continuousAnnihilator Y ×
          Forms.continuousAnnihilator eta.radical) :=
    ContinuousLinearEquiv.mk dualLinearEquiv coordinates.continuous
      sumCoordinates.continuous
  have hRadical (f : eta.radical) : eta.toDual (f : X) = 0 := f.property
  let SY : Y →L[ℝ] StrongDual ℝ X := eta.toDual.comp Y.subtypeL
  have hSY_injective : Function.Injective SY := by
    intro y z hyz
    apply Subtype.ext
    have hzero : eta.toDual ((y - z : Y) : X) = 0 := by
      simpa [SY, sub_eq_zero] using sub_eq_zero.mpr hyz
    have hzmem : ((y - z : Y) : X) ∈ (⊥ : Submodule ℝ X) :=
      hTop.isCompl.disjoint.le_bot ⟨hzero, (y - z).property⟩
    exact (Submodule.mem_bot ℝ).mp hzmem |> sub_eq_zero.mp
  have hSY_range : SY.toLinearMap.range = eta.toDual.toLinearMap.range := by
    apply le_antisymm
    · rintro phi ⟨y, rfl⟩
      exact ⟨(y : X), rfl⟩
    · rintro phi ⟨x, rfl⟩
      refine ⟨pY x, ?_⟩
      change eta.toDual (pY x : X) = eta.toDual x
      calc
        eta.toDual (pY x : X) =
            eta.toDual ((pF x : X) + (pY x : X)) := by
              rw [map_add, hRadical, zero_add]
        _ = eta.toDual x := congrArg eta.toDual (hProj x)
  have hSY_closed : IsClosed (Set.range SY) := by
    change IsClosed (SY.toLinearMap.range : Set (StrongDual ℝ X))
    rw [hSY_range]
    exact hFredholm.2.1
  let eRange : Y ≃L[ℝ] SY.toLinearMap.range :=
    ContinuousLinearMap.equivRange hSY_injective hSY_closed
  let hSYAnn : SY.toLinearMap.range =
      Forms.continuousAnnihilator eta.radical := hSY_range.trans hRange
  let restrictionEquiv :
      Y ≃L[ℝ] Forms.continuousAnnihilator eta.radical :=
    eRange.trans (ContinuousLinearEquiv.ofEq SY.toLinearMap.range
      (Forms.continuousAnnihilator eta.radical) hSYAnn)
  refine
    { kernelFiniteDimensional := inferInstance
      complement := Y
      complementClosed := hComplemented.isClosed_complement
      kernel_disjoint_complement := hTop.isCompl.disjoint
      kernel_sup_complement := hTop.isCompl.sup_eq_top
      dualCoordinates := dualEquiv
      dualCoordinates_symm_apply := ?_
      annihilatorComplementEquivKernelDual := annYEquivF
      annihilatorComplementEquivKernelDual_apply := ?_
      range_eq_annihilator := hRange
      restrictionEquiv := restrictionEquiv
      restrictionEquiv_apply := ?_ }
  · intro p
    change sumCoordinates p =
      (p.1 : StrongDual ℝ X) + (p.2 : StrongDual ℝ X)
    rfl
  · intro a f
    change (a : StrongDual ℝ X) (f : X) = (a : StrongDual ℝ X) (f : X)
    rfl
  · intro y
    change ((eRange y : SY.toLinearMap.range) : StrongDual ℝ X) =
      eta.toDual (y : X)
    have heRange : eRange y = SY.rangeRestrict y :=
      congrFun (ContinuousLinearMap.coe_equivRange hSY_injective hSY_closed) y
    rw [heRange]
    rfl

/-- The local kernel parametrization and reduced alternating form at one nearby parameter. -/
structure LocalSchurPointData {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (eta0 eta : ContinuousAlternatingForm X) where
  /-- The bounded injection parametrizing the nearby kernel from the fixed kernel. -/
  kernelMap : eta0.radical →L[ℝ] X
  kernelMap_injective : Function.Injective kernelMap
  /-- The finite-dimensional alternating Schur complement on the fixed kernel. -/
  reducedForm : ContinuousAlternatingForm eta0.radical
  reducedForm_apply (f g : eta0.radical) :
    reducedForm.toDual f g = eta.toDual (kernelMap f) (kernelMap g)
  /-- The reduced radical is linearly equivalent to the moving kernel. -/
  radicalEquivKernel : reducedForm.radical ≃ₗ[ℝ] eta.radical
  radicalEquivKernel_apply (f : reducedForm.radical) :
    ((radicalEquivKernel f : eta.radical) : X) = kernelMap (f : eta0.radical)

/-- Local Schur reduction relative to an arbitrary real parameter set.

For all sufficiently close `t` in `J`, the bounded injection from the fixed kernel restricts to
the displayed linear equivalence from the reduced radical to the moving kernel.
Blueprint: `lem:schur-reduction`; audit: `AUX-LOWER-BLOCK-INVERTIBLE`,
`AUX-SCHUR-KERNEL-PARAMETRIZATION`, `AUX-REDUCED-ALTERNATING-FORM`, and
`AUX-REDUCED-RADICAL-KERNEL`. -/
theorem localSchurReduction {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [CompleteSpace X] (J : Set ℝ) (t0 : J) (eta : J → ContinuousAlternatingForm X)
    (hContinuous : Continuous fun t ↦ (eta t).toDual)
    (hReflexive : Function.Surjective (NormedSpace.inclusionInDoubleDual ℝ X))
    (hFredholm : IsFredholm (eta t0).toDual) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ ∀ t : J, |(t : ℝ) - (t0 : ℝ)| < epsilon →
      Nonempty (LocalSchurPointData (eta t0) (eta t)) := by
  sorry

/-- Kernel parity is constant along a norm-continuous Fredholm path of alternating forms.

Blueprint: `thm:mod2-path`; audit: `LEM-MOD2-PATH` and `AUX-LOCAL-PARITY-GLOBAL`. -/
theorem mod2Path {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [CompleteSpace X] (eta : Set.Icc (0 : ℝ) 1 → ContinuousAlternatingForm X)
    (hContinuous : Continuous fun t ↦ (eta t).toDual)
    (hReflexive : Function.Surjective (NormedSpace.inclusionInDoubleDual ℝ X))
    (hFredholm : ∀ t, IsFredholm (eta t).toDual) :
    ∀ s t, Nat.ModEq 2 (Module.finrank ℝ (eta s).radical)
      (Module.finrank ℝ (eta t).radical) := by
  sorry

end

end KaltonPeck.Support.PathParity
