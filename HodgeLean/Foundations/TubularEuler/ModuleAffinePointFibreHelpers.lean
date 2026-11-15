import HodgeLean.Foundations.BundleThom.ConormalFibre
import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.Open

/-! # Actual point fibres through an affine scheme chart

The original point is retained through its lift to the open and the specified affine isomorphism.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.TubularEuler

def moduleAffinePointFibreIso {Q : Over (Spec ↧ℂ)} (M : Q.left.Modules)
    (U : Q.left.Opens) (hU : IsAffineOpen U) (x : ComplexPoint Q)
    (hx : x ∈ Point.overOpen U) :
    (moduleSpecΓFunctor (R := CommRingCat.of ℂ)).obj ((Scheme.Modules.pullback x.left).obj M) ≅
      (moduleSpecΓFunctor (R := CommRingCat.of ℂ)).obj
        ((Scheme.Modules.pullback (ComplexPoint.liftToOpen Q U x hx ≫ hU.isoSpec.hom)).obj
          ((Scheme.Modules.pullback hU.isoSpec.inv).obj ((Scheme.Modules.pullback U.ι).obj M))) := by
  let a := ComplexPoint.liftToOpen Q U x hx
  let b := a ≫ hU.isoSpec.hom
  let c := hU.isoSpec.inv ≫ U.ι
  have hbc : b ≫ c = x.left := by
    dsimp only [b, c]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    exact ComplexPoint.liftToOpen_fac Q U x hx
  exact (moduleSpecΓFunctor (R := CommRingCat.of ℂ)).mapIso
    (((Scheme.Modules.pullback b).mapIso ((Scheme.Modules.pullbackComp hU.isoSpec.inv U.ι).app M) ≪≫
      (Scheme.Modules.pullbackComp b c).app M ≪≫
      (Scheme.Modules.pullbackCongr hbc).app M).symm)

#print axioms moduleAffinePointFibreIso

end HodgeLean.Foundations.TubularEuler
