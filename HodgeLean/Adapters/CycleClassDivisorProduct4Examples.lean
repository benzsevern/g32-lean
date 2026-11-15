import HodgeLean.Adapters.CycleClassDivisorProduct4
import HodgeLean.Adapters.CycleClassDivisorProduct4NormalizationExamples
import HodgeLean.RealDefs.ComplexFundamentalClassParts.F_Euclidean

/-! # Constructed supported examples and point instantiations

The nonzero construction checks use base results. Instantiations of the three
new public laws retain their open comparison obligations.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxRecDepth 4000
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
open AlgebraicTopology.Singular HodgeLean.RealDefs HodgeLean.Foundations
namespace HodgeLean.Adapters

/-- The identity supplies an actual complex point.
Source: the terminal scheme over itself. -/
local instance ccm16_pointNonempty : Nonempty (ComplexPoint ccm16_point) := ⟨𝟙 _⟩

/-- Absolute cohomology as full-support relative cohomology, using the actual projection.
Source: Hatcher, Algebraic Topology, §3.1; the base's empty-subspace chain isomorphism. -/
def ccm16_wholeRelativeEquiv (Y : TopCat.{0}) (n : ℕ) :
    RelativeCohomology ℚ (TopPair.ofSubset (X := Y) (Set.univ : Set Y)ᶜ) n ≃ₗ[ℚ]
      Cohomology ℚ Y n := by
  letI := F_relativeChainProjection_isIso_of_isEmpty Y (Set.univ : Set Y)ᶜ
    ⟨fun x => x.2 (Set.mem_univ _)⟩
  exact (HomologicalComplex.homologyMapIso
    (HomologicalComplex.linearDualIso
      (asIso (relativeChainProjection ℚ (TopPair.ofSubset (X := Y) (Set.univ : Set Y)ᶜ)))) n).toLinearEquiv

example : ccm16_wholeRelativeEquiv (TopCat.of PUnit) 0 0 = 0 := map_zero _

/-- A supported class on the actual scheme point, lifting the singular unit.
Source: inverse of the constructed supported comparison and the empty-subspace equivalence. -/
def ccm16_pointSupportedUnit : H_[(⊤ : Closeds (ComplexPoint ccm16_point))]^0(ccm16_point; ℚ) :=
  (ccm16_supportedComparison ccm16_point ⊤ 0).symm
    ((ccm16_wholeRelativeEquiv (TopCat.of (ComplexPoint ccm16_point)) 0).symm
      (Singular.unit (R := ℚ) (TopCat.of (ComplexPoint ccm16_point))))

/-- The constructed point input is nonzero independently of the new comparison laws.
Source: injectivity of the two linear equivalences and nonvanishing of the singular unit. -/
theorem ccm16_pointSupportedUnit_ne_zero : ccm16_pointSupportedUnit ≠ 0 := by
  unfold ccm16_pointSupportedUnit
  exact (LinearEquiv.map_ne_zero_iff _).mpr ((LinearEquiv.map_ne_zero_iff _).mpr (Singular.unit_ne_zero _))

example : ccm16_pointSupportedUnit ≠ 0 := ccm16_pointSupportedUnit_ne_zero

example : ccm16_supportedLinearEquiv ccm16_point ⊤ 0 0 = 0 := map_zero _
example : ccm16_supportedComparison ccm16_point ⊤ 0 0 = 0 := map_zero _
example : ccm16_supportedCup ccm16_point ⊤ ⊤ 1 2 0 0 = 0 := by
  exact map_zero _

/-- The transport cancels exactly on the actual product of two nonzero point inputs.
Source: the inverse-comparison construction, independent of the new absolute laws. -/
example : ccm16_supportedComparison ccm16_point (⊤ ⊓ ⊤) (0 + 0)
    (ccm16_supportedCup ccm16_point ⊤ ⊤ 0 0 ccm16_pointSupportedUnit ccm16_pointSupportedUnit) =
  ccm15_relativeCup (TopCat.of (ComplexPoint ccm16_point)) ⊤ ⊤ 0 0
    (ccm16_supportedComparison ccm16_point ⊤ 0 ccm16_pointSupportedUnit)
    (ccm16_supportedComparison ccm16_point ⊤ 0 ccm16_pointSupportedUnit) := by
  exact (ccm16_supportedComparison ccm16_point (⊤ ⊓ ⊤) 0).apply_symm_apply _

/-- The constructed cup of the two nonzero supported point inputs is nonzero.
Source: ccm15's absolute law and the singular unit law; no new comparison obligation. -/
theorem ccm16_pointSupportedCup_ne_zero :
    ccm16_supportedCup ccm16_point ⊤ ⊤ 0 0 ccm16_pointSupportedUnit
      ccm16_pointSupportedUnit ≠ 0 := by
  change (ccm16_supportedComparison ccm16_point (⊤ ⊓ ⊤) 0).symm
    (ccm15_relativeCup (TopCat.of (ComplexPoint ccm16_point)) ⊤ ⊤ 0 0
      (ccm16_supportedComparison ccm16_point ⊤ 0 ccm16_pointSupportedUnit)
      (ccm16_supportedComparison ccm16_point ⊤ 0 ccm16_pointSupportedUnit)) ≠ 0
  apply (LinearEquiv.map_ne_zero_iff _).mpr
  intro h
  have h' := congrArg (relativeCohomologyToAbsolute ℚ
    (TopPair.ofSubset (X := TopCat.of (ComplexPoint ccm16_point))
      (((⊤ ⊓ ⊤ : Closeds (ComplexPoint ccm16_point))) : Set (ComplexPoint ccm16_point))ᶜ) 0) h
  rw [ccm15_relativeCup_absolute (TopCat.of (ComplexPoint ccm16_point)) ⊤ ⊤ 0 0,
    map_zero] at h'
  have hu : relativeCohomologyToAbsolute ℚ
      (TopPair.ofSubset (X := TopCat.of (ComplexPoint ccm16_point))
        ((⊤ : Closeds (ComplexPoint ccm16_point)) : Set (ComplexPoint ccm16_point))ᶜ) 0
      (ccm16_supportedComparison ccm16_point ⊤ 0 ccm16_pointSupportedUnit) =
      Singular.unit (R := ℚ) (TopCat.of (ComplexPoint ccm16_point)) := by
    change ccm16_wholeRelativeEquiv (TopCat.of (ComplexPoint ccm16_point)) 0
      ((ccm16_supportedComparison ccm16_point ⊤ 0)
        ((ccm16_supportedComparison ccm16_point ⊤ 0).symm
          ((ccm16_wholeRelativeEquiv (TopCat.of (ComplexPoint ccm16_point)) 0).symm _))) = _
    rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  rw [hu, Singular.one_cup] at h'
  exact Singular.unit_ne_zero _ h'

example : ccm16_supportedCup ccm16_point ⊤ ⊤ 0 0 ccm16_pointSupportedUnit
    ccm16_pointSupportedUnit ≠ 0 := ccm16_pointSupportedCup_ne_zero

example : rationalCohomologyLinearEquivSingular ccm16_point 0
    (HQ.linearEquiv ccm16_point 0 (cupUnit ccm16_point)) =
    Singular.unit (TopCat.of (ComplexPoint ccm16_point)) := ccm16_rawComparison_unit _

example : relativeCohomologyToAbsolute ℚ
    (TopPair.ofSubset (X := TopCat.of (ComplexPoint ccm16_point))
      ((⊤ : Closeds (ComplexPoint ccm16_point)) : Set (ComplexPoint ccm16_point))ᶜ) 0
    (ccm16_supportedComparison ccm16_point ⊤ 0 ccm16_pointSupportedUnit) =
  rationalCohomologyLinearEquivSingular ccm16_point 0
    (AlgebraicGeometry.ComplexPoint.forgetSupport ℚ ccm16_point ⊤ 0 ccm16_pointSupportedUnit) :=
  ccm16_supportedComparison_forget _ _ _ _

example : (HQ.linearEquiv ccm16_point (0 + 0)).symm
    (AlgebraicGeometry.ComplexPoint.forgetSupport ℚ ccm16_point (⊤ ⊓ ⊤) (0 + 0)
      (ccm16_supportedCup ccm16_point ⊤ ⊤ 0 0 ccm16_pointSupportedUnit ccm16_pointSupportedUnit)) =
  (cupProductOf ccm16_point).cup rfl
    ((HQ.linearEquiv ccm16_point 0).symm
      (AlgebraicGeometry.ComplexPoint.forgetSupport ℚ ccm16_point ⊤ 0 ccm16_pointSupportedUnit))
    ((HQ.linearEquiv ccm16_point 0).symm
      (AlgebraicGeometry.ComplexPoint.forgetSupport ℚ ccm16_point ⊤ 0 ccm16_pointSupportedUnit)) :=
  ccm16_supportedCup_forget _ _ _ _ _ _ _

end HodgeLean.Adapters
