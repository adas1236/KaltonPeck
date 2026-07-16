import KaltonPeck.Support.Symplectic
import KaltonPeck.Support.Fredholm
import KaltonPeck.Support.PathParity

set_option autoImplicit false

namespace KaltonPeck.Support.GraphFredholm

noncomputable section

open Coordinates Symplectic

/-- A bounded operator is upper semi-Fredholm when its kernel is finite-dimensional and its
range is closed.
Blueprint label: `def:upper-semi`; audit ID `INF-UPPER-SEMI-FREDHOLM`. -/
def IsUpperSemiFredholm {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] (A : X →L[ℝ] Y) : Prop := by
  exact FiniteDimensional ℝ A.toLinearMap.ker ∧ IsClosed (A.toLinearMap.range : Set Y)

/-- The pinned canonical Castillo--González--Pino theorem (arXiv:2207.01069v1, Lemma 5.4).
Blueprint label: `thm:cgp-primary`; audit ID `EXT-CGP-UPPER-SEMI-PRIMARY`. -/
theorem cgpPrimary (A : CanonicalRealKaltonPeck →L[ℝ] CanonicalRealKaltonPeck)
    (hA : IsUpperSemiFredholm A) :
    IsFredholm (canonicalKaltonSwansonForm.adjoint A * A) := by
  sorry

/-- The CGP theorem transported to an arbitrary complete presented real Kalton--Peck model.
Blueprint label: `thm:cgp-transport`; audit ID `EXT-CGP-UPPER-SEMI`. -/
theorem cgpTransport {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [CompleteSpace X] (hX : RealKaltonPeckPresentation X) (A : X →L[ℝ] X)
    (hA : IsUpperSemiFredholm A) :
    IsFredholm ((transportedKaltonSwansonForm hX).adjoint A * A) := by
  sorry

/-- The normalized sequence `n ↦ e₂ₙ`.
Support definition for blueprint label `lem:even-odd-blocks`. -/
def evenBlockSequence : ℕ → ℕ → ℝ := by
  exact fun n ↦ standardBasisSequence (2 * n)

/-- The normalized sequence `n ↦ e₂ₙ₊₁`.
Support definition for blueprint label `lem:even-odd-blocks`. -/
def oddBlockSequence : ℕ → ℕ → ℝ := by
  exact fun n ↦ standardBasisSequence (2 * n + 1)

/-- The even and odd sequences are successive normalized blocks and mutually support-disjoint.
Support theorem for blueprint label `lem:even-odd-blocks`. -/
theorem evenOddBlockSequences :
    IsSuccessiveNormalizedBlockSequence evenBlockSequence ∧
      IsSuccessiveNormalizedBlockSequence oddBlockSequence ∧
        AreMutuallySupportDisjoint evenBlockSequence oddBlockSequence := by
  sorry

/-- The transported even-coordinate block embedding.
Support definition for blueprint label `lem:even-odd-blocks`. -/
def evenBlockEmbedding {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [CompleteSpace X] (hX : RealKaltonPeckPresentation X) : X →L[ℝ] X := by
  exact transportedBlockOperator hX evenBlockSequence evenOddBlockSequences.1

/-- The transported odd-coordinate block embedding.
Support definition for blueprint label `lem:even-odd-blocks`. -/
def oddBlockEmbedding {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [CompleteSpace X] (hX : RealKaltonPeckPresentation X) : X →L[ℝ] X := by
  exact transportedBlockOperator hX oddBlockSequence evenOddBlockSequences.2.1

/-- The graph operator `R₀ + R₁T` on a presented model.
Support definition for blueprint labels `lem:even-odd-blocks` and `prop:graph-fredholm`. -/
def graphBlockOperator {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [CompleteSpace X] (hX : RealKaltonPeckPresentation X) (T : X →L[ℝ] X) :
    X →L[ℝ] X := by
  exact evenBlockEmbedding hX + oddBlockEmbedding hX * T

/-- The four even--odd adjoint relations and the two graph-operator identities.
Blueprint label: `lem:even-odd-blocks`; audit IDs `HID-EVEN-ODD-BLOCK-RELATIONS`,
`HID-LEFT-INVERSE-UPPER-SEMI`, and `HID-ADJOINT-EXPANSION`. -/
theorem evenOddBlocks {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [CompleteSpace X] (hX : RealKaltonPeckPresentation X) :
    let ω := transportedKaltonSwansonForm hX
    let R₀ := evenBlockEmbedding hX
    let R₁ := oddBlockEmbedding hX
    ω.adjoint R₀ * R₀ = 1 ∧
      ω.adjoint R₁ * R₁ = 1 ∧
      ω.adjoint R₀ * R₁ = 0 ∧
      ω.adjoint R₁ * R₀ = 0 ∧
      ∀ T : X →L[ℝ] X,
        let W := graphBlockOperator hX T
        ω.adjoint R₀ * W = 1 ∧
          ω.adjoint W * W = 1 + ω.adjoint T * T ∧ IsUpperSemiFredholm W := by
  sorry

/-- Every graph operator `I + T⁺T` on a complete presented real Kalton--Peck model is Fredholm.
Blueprint label: `prop:graph-fredholm`; audit ID `PROP-GRAPH-FREDHOLM`. -/
theorem graphFredholm {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [CompleteSpace X] (hX : RealKaltonPeckPresentation X) (T : X →L[ℝ] X) :
    IsFredholm (1 + (transportedKaltonSwansonForm hX).adjoint T * T) := by
  sorry

/-- The weak alternating form `bₜ(x,y) = Ω(x,y) + t Ω(Tx,Ty)`.
Blueprint label: `lem:kp-alternating-path`; audit ID `HID-ALTERNATING-PATH`. -/
def kaltonPeckAlternatingPath {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [CompleteSpace X] (hX : RealKaltonPeckPresentation X) (T : X →L[ℝ] X) (t : ℝ) :
    ContinuousAlternatingForm X := by
  let omega := transportedKaltonSwansonForm hX
  refine
    { toDual := omega.toDual.toContinuousLinearMap +
        t • (transpose T).comp (omega.toDual.toContinuousLinearMap.comp T)
      alternating := ?_ }
  intro x
  change omega.toDual x x + t * omega.toDual (T x) (T x) = 0
  rw [omega.alternating, omega.alternating, mul_zero, add_zero]

/-- Evaluation, induced-operator formula, norm continuity, and Fredholmness of the path.
Blueprint label: `lem:kp-alternating-path`; audit IDs `HID-ALTERNATING-PATH`,
`HID-SQRT-SCALING`, and `HID-D-COMPOSITION`. -/
theorem kaltonPeckAlternatingPath_spec {X : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] [CompleteSpace X] (hX : RealKaltonPeckPresentation X)
    (T : X →L[ℝ] X) :
    let ω := transportedKaltonSwansonForm hX
    (∀ t x y, (kaltonPeckAlternatingPath hX T t).toDual x y =
        ω.toDual x y + t * ω.toDual (T x) (T y)) ∧
      (∀ t, (kaltonPeckAlternatingPath hX T t).toDual =
        ω.toDual.toContinuousLinearMap.comp (1 + t • (ω.adjoint T * T))) ∧
      Continuous (fun t : Set.Icc (0 : ℝ) 1 ↦
        (kaltonPeckAlternatingPath hX T t.1).toDual) ∧
      ∀ t : Set.Icc (0 : ℝ) 1, IsFredholm (kaltonPeckAlternatingPath hX T t.1).toDual := by
  sorry

/-- The graph Fredholm operator has finite, even-dimensional kernel.
Blueprint label: `prop:even-kernel`; audit ID `PROP-EVEN-KERNEL`. -/
theorem evenGraphKernel {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [CompleteSpace X] (hX : RealKaltonPeckPresentation X) (T : X →L[ℝ] X) :
    let G := 1 + (transportedKaltonSwansonForm hX).adjoint T * T
    IsFredholm G ∧ Even (nullity G) := by
  sorry

end


end KaltonPeck.Support.GraphFredholm
