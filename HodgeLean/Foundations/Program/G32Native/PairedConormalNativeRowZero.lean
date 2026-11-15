import HodgeLean.Foundations.Program.G32Native.PairedConormalNativeFrameScalar
import HodgeLean.Foundations.Program.G32Native.PairedConormalLocalUnitScalar
import HodgeLean.Foundations.Program.G32Native.PairedConormalSectionSpecializationIso
import HodgeLean.Foundations.Program.G32Native.PairedConormalUnitMapDetection

/-! # Actual ideal row vanishing detected by its literal regular coefficient -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Program HodgeLean.Foundations.Curves.Picard.LineBundles
open HodgeLean.Foundations.BundleThom
attribute [local instance] MvPolynomial.gradedAlgebra
variable (k : ℕ)
local notation "N" => Proj (MvPolynomial.homogeneousSubmodule (Fin (k + 1)) ℂ)
abbrev conormalPolynomialModelOver (k : ℕ) : Over (Spec ↧ℂ) :=
  Over.mk ((s2_polynomialProjectiveSpaceIso ℂ (Fin (k + 1))).hom ≫
    ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ))

/-- An actual native ideal row vanishes on the supplied complex fibre exactly
when its literal normalized regular coefficient has value zero there. -/
theorem conormal_native_ideal_row_pullback_zero_iff (i : Fin (k + 1))
    (φ : idealModule (conormalNativeHyperplaneIdeal ℂ k) ⟶ SheafOfModules.unit (N).ringCatSheaf)
    (x : ComplexPoint (conormalPolynomialModelOver k)) (hx : x ∈ Point.overOpen (conormalNativeCoordinateOpen ℂ k i).1) :
    (Scheme.Modules.pullback x.left).map φ = 0 ↔
      Point.evaluate (conormalNativeCoordinateOpen ℂ k i).1
        (conormalIdealMapCoefficient (conormalNativeHyperplaneIdeal ℂ k) φ
          (conormalNativeCoordinateOpen ℂ k i) (ProjSpace.coordinateRatioSection ℂ k i 0)
          (conormal_native_hyperplane_coordinate_mem ℂ k i)) x = 0 := by
  let U := conormalNativeCoordinateOpen ℂ k i
  let s := (conormalNativeHyperplaneNormalizedPullbackFrame k i).hom
  let t := i1_localModuleSectionSpecialization (Q := conormalPolynomialModelOver k)
    (SheafOfModules.unit (N).ringCatSheaf) U.1
      (s ≫ (Scheme.Modules.pullback U.1.ι).map φ) x hx
  have hz := conormal_local_section_specialization_detects_zero (Q := conormalPolynomialModelOver k) φ U.1 s x hx
  have hu : t = 0 ↔ t ≫ (pullbackUnit x.left).hom = 0 := by
    constructor
    · intro h
      rw [h, zero_comp]
    · intro h
      apply (cancel_mono (pullbackUnit x.left).hom).mp
      simpa only [zero_comp] using h
  have hunit : t ≫ (pullbackUnit x.left).hom = 0 ↔
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom
        ((t ≫ (pullbackUnit x.left).hom).val.app (Opposite.op ⊤)
          (1 : Γ(Spec ↧ℂ, ⊤))) = 0 := by
    rw [conormal_unit_map_eq_zero_iff_top_one]
    constructor
    · intro h
      rw [h, map_zero]
    · intro h
      apply (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom).injective
      exact h.trans (map_zero _).symm
  have hsc := conormal_local_unit_section_scalar (Q := conormalPolynomialModelOver k) U.1
    (s ≫ (Scheme.Modules.pullback U.1.ι).map φ) x hx
  have hcoef := conormal_native_normalized_frame_scalar k i φ
  simp only [Category.assoc] at hsc
  rw [hcoef] at hsc
  dsimp only [U] at hsc
  have hcancel := (conormalNativeCoordinateOpen ℂ k i).1.topIso.inv_hom_id_apply
    (conormalIdealMapCoefficient (conormalNativeHyperplaneIdeal ℂ k) φ
      (conormalNativeCoordinateOpen ℂ k i) (ProjSpace.coordinateRatioSection ℂ k i 0)
      (conormal_native_hyperplane_coordinate_mem ℂ k i))
  have hsc' := hsc.trans (congrArg (fun r => Point.evaluate U.1 r x) hcancel)
  refine hz.symm.trans (hu.trans (hunit.trans ?_))
  convert! Iff.of_eq (congrArg (fun z : ℂ => z = 0) hsc') using 1

end HodgeLean.Foundations.Program.G32Native
