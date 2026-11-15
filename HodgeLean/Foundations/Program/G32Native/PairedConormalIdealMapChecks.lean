import HodgeLean.Foundations.Program.G32Native.PairedConormalIdealMapTwisting

/-! # The actual hyperplane inclusion retains its original coordinate section -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Modules Scheme.Modules.GlueOfCocycle
attribute [local instance] MvPolynomial.gradedAlgebra
namespace HodgeLean.Foundations.Program.G32Native

/-- The original ideal inclusion gives the coordinate-zero twisting section,
retaining its index and its original scale. -/
theorem paired_nativeIdealMapTwistingSection_inclusion (k : ℕ) :
    paired_nativeIdealMapTwistingSection k
      (kernel.ι (SheafOfModules.unitToPushforwardObjUnit
        (paired_nativeHyperplaneIdeal k).subschemeι.toRingCatSheafHom)) =
      ProjSpace.twistingCoordinateSection ℂ k 0 := by
  apply glue_ext
  intro i
  rw [paired_nativeIdealMapTwistingSection_component]
  change rO inf_le_right
    ((kernel.ι (SheafOfModules.unitToPushforwardObjUnit
      (paired_nativeHyperplaneIdeal k).subschemeι.toRingCatSheafHom)).val.app
        (Opposite.op (ProjSpace.standardOpen ℂ k i.down))
        (paired_nativeHyperplaneStandardGenerator k i.down)) = _
  rw [paired_nativeHyperplaneStandardGenerator_inclusion]
  rfl

/-- The original ideal generator has a nonzero image, rejecting a zero relation. -/
theorem paired_nativeHyperplaneGeneratorSection_ne_zero (k : ℕ) (i : Fin (k + 1)) :
    paired_nativeHyperplaneGeneratorSection k i ≠ 0 := by
  intro h
  have he := paired_nativeHyperplaneGeneratorSection_inclusion k i
  rw [h, map_zero] at he
  apply paired_nativeRatio_ne_zero ℂ k i 0
  have h' := congrArg (paired_nativeHyperplaneChartEquiv k i) he.symm
  simpa only [RingEquiv.apply_symm_apply, map_zero] using h'

end HodgeLean.Foundations.Program.G32Native
