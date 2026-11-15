import HodgeLean.Foundations.Program.SchoenTransferQ3FibreIdealSquare
import HodgeLean.Foundations.AlgebraicGeometry.SingularCycles.RamifiedDegreePointLength

/-! Unrestricted point-fibre length on an actual open source. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Restricting the source to an actual open immersion preserves the full
point-fibre length without a choice of maximal-ideal generators. -/
theorem s4_q3_point_fibre_length_comp_open
    {Y X Z : Scheme} (j : Y ⟶ X) [IsOpenImmersion j] (f : X ⟶ Z) (y : Y) :
    SingularCycles.pointFibreLength (j ≫ f) y =
      SingularCycles.pointFibreLength f (j y) := by
  let b := j.stalkMap y
  have hb := ConcreteCategory.bijective_of_isIso b
  have hcomm : b.hom.comp (f.stalkMap (j y)).hom =
      ((j ≫ f).stalkMap y).hom.comp (RingHom.id _) := by
    rw [RingHom.comp_id]
    exact congrArg CommRingCat.Hom.hom (Scheme.Hom.stalkMap_comp j f y).symm
  have hker : RingHom.ker b.hom ≤
      (IsLocalRing.maximalIdeal (Z.presheaf.stalk (f (j y)))).map
        (f.stalkMap (j y)).hom := by
    intro r hr
    change b.hom r = 0 at hr
    have hz : r = 0 := hb.1 (hr.trans (map_zero b.hom).symm)
    rw [hz]
    exact Ideal.zero_mem _
  exact (s4_q3_fibre_length_surjective_square (f.stalkMap (j y)).hom (RingHom.id _)
    b.hom ((j ≫ f).stalkMap y).hom Function.surjective_id hb.2 hcomm hker).symm

end HodgeLean.Foundations.Program
