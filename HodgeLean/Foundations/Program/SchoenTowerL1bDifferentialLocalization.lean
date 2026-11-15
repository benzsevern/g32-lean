import HodgeLean.Foundations.Program.SchoenTowerL1bDifferentialCriterion
import Mathlib.RingTheory.Localization.Away.Basic

/-! Localizing the determinant of a specified coordinate differential family.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace HodgeLean.Foundations.Program
open KaehlerDifferential

/-- Inverting the coordinate differential determinant makes the actual evaluation homomorphism etale. -/
theorem s2v_l1b_evaluation_etale_away_differential_determinant
    {R A ι : Type*} [CommRing R] [CommRing A] [Fintype ι] [DecidableEq ι]
    [Algebra R A] [Algebra.Smooth R A]
    (c : ι → A) (b : Module.Basis ι A Ω[A⁄R]) :
    let d := b.det (fun i => D R A (c i))
    (MvPolynomial.aeval (R := R)
      (fun i => algebraMap A (Localization.Away d) (c i))).toRingHom.Etale := by
  let d := b.det (fun i => D R A (c i))
  let L := Localization.Away d
  letI : Algebra.Etale A L := Algebra.Etale.of_isLocalizationAway d
  letI : Algebra.Smooth R L := Algebra.Smooth.comp R A L
  let e := KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R A L
  let B := (b.baseChange L).map e
  have hcoord (i j : ι) : B.repr (D R L (algebraMap A L (c j))) i =
      algebraMap A L (b.repr (D R A (c j)) i) := by
    change (b.baseChange L).repr (e.symm (D R L (algebraMap A L (c j)))) i = _
    rw [KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_symm_D_algebraMap,
      Module.Basis.baseChange_repr_tmul, Algebra.smul_def, mul_one]
  have hdet : B.det (fun i => D R L (algebraMap A L (c i))) = algebraMap A L d := by
    change B.det (fun i => D R L (algebraMap A L (c i))) =
      algebraMap A L (b.det (fun i => D R A (c i)))
    rw [Module.Basis.det_apply, Module.Basis.det_apply, RingHom.map_det]
    congr 1
    ext i j
    exact hcoord i j
  apply s2v_l1b_evaluation_etale_of_unit_differential_determinant _ B
  rw [hdet]
  exact IsLocalization.Away.algebraMap_isUnit d

end HodgeLean.Foundations.Program
