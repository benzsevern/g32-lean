import HodgeLean.Foundations.Program.SchoenTransferQ3CartesianFibreLength
import HodgeLean.Foundations.Program.SchoenTransferQ3OpenFibreLength

/-! Unreduced point-fibre length in the specified closed base-change square. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Actual cartesian closed restriction preserves fibre length, without
replacing the specified support scheme by a chosen pullback object. -/
theorem s4_q3_point_fibre_length_of_closed_base_change
    {K X D W : Scheme} (i : K ⟶ X) (κ : K ⟶ D) (q : X ⟶ W) (j : D ⟶ W)
    [IsClosedImmersion j] (hsquare : IsPullback i κ q j) (p : K) :
    SingularCycles.pointFibreLength κ p = SingularCycles.pointFibreLength q (i p) := by
  let e := hsquare.isoPullback
  have hκ : e.hom ≫ pullback.snd q j = κ := hsquare.isoPullback_hom_snd
  have hi : e.hom ≫ pullback.fst q j = i := hsquare.isoPullback_hom_fst
  calc
    SingularCycles.pointFibreLength κ p =
        SingularCycles.pointFibreLength (e.hom ≫ pullback.snd q j) p := by rw [hκ]
    _ = SingularCycles.pointFibreLength (pullback.snd q j) (e.hom p) :=
      s4_q3_point_fibre_length_comp_open e.hom (pullback.snd q j) p
    _ = SingularCycles.pointFibreLength q ((pullback.fst q j) (e.hom p)) :=
      s4_q3_cartesian_point_fibre_length q j (e.hom p)
    _ = SingularCycles.pointFibreLength q (i p) := by
      rw [← Scheme.Hom.comp_apply, hi]

/-- The canonical map on the unreduced inverse-image subscheme retains
the original ambient point-fibre length. -/
theorem s4_q3_inverse_support_point_fibre_length
    {X W : Scheme} (q : X ⟶ W) (I : W.IdealSheafData) (p : (I.comap q).subscheme) :
    SingularCycles.pointFibreLength
        (Scheme.IdealSheafData.subschemeMap (I.comap q) I q (I.le_map_comap q)) p =
      SingularCycles.pointFibreLength q ((I.comap q).subschemeι p) := by
  let e := I.comapIso q
  rw [← I.comapIso_hom_snd q,
    s4_q3_point_fibre_length_comp_open e.hom (pullback.snd q I.subschemeι) p,
    s4_q3_cartesian_point_fibre_length q I.subschemeι (e.hom p)]
  change SingularCycles.pointFibreLength q ((e.hom ≫ pullback.fst q I.subschemeι) p) = _
  rw [Scheme.IdealSheafData.comapIso_hom_fst]

end HodgeLean.Foundations.Program
