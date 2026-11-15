import HodgeLean.Foundations.Program.CompensationAssemblyFiniteSmoothEtale
import Mathlib.RingTheory.Flat.TorsionFree

noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 10000
set_option maxRecDepth 2048
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

set_option backward.isDefEq.respectTransparency false in
theorem cq_finite_smooth_affine_integral_etale {X Y : Scheme.{0}}
    [IsAffine X] [IsAffine Y] [IsIntegral X] [IsIntegral Y]
    (sY : Y ⟶ Spec ↧ℂ) (f : X ⟶ Y) [IsFinite f] [Smooth f] : Etale f := by
  let R := Γ(Y, ⊤)
  let B := Γ(X, ⊤)
  letI : Algebra R B := f.appTop.hom.toAlgebra
  letI : Algebra ℂ R := ((Scheme.ΓSpecIso ↧ℂ).inv ≫ sY.appTop).hom.toAlgebra
  letI : CharZero R := charZero_of_injective_algebraMap (algebraMap ℂ R).injective
  letI : Module.Finite R B := f.finite_appTop
  letI : Algebra.Smooth R B := HasRingHomProperty.appTop (P := @Smooth) f inferInstance
  letI : Module.Flat R B := inferInstance
  letI : Module.IsTorsionFree R B := Module.Flat.isTorsionFree
  letI : FaithfulSMul R B := Module.IsTorsionFree.to_faithfulSMul
  have he : Algebra.Etale R B := cq_finite_smooth_domain_etale R B
    (FaithfulSMul.algebraMap_injective R B)
  exact (HasRingHomProperty.iff_of_isAffine (P := @Etale) (f := f)).mpr he

end HodgeLean.Foundations.Program
