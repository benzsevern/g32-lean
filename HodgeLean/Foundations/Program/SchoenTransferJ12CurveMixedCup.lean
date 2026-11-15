import HodgeLean.Foundations.Program.SchoenTransferJ12CurveMixedDivisor
import HodgeLean.Foundations.Program.SchoenTransferSuppliers

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000
open CategoryTheory AlgebraicGeometry MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj
open HodgeLean.RealDefs HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- On two degree-one classes the actual curve mixed divisor is the alternating cross term.
Source: Birkenhake–Lange, Complex Abelian Varieties, §2.5;
Hatcher, Algebraic Topology, §3.2, naturality and graded commutativity of cup. -/
theorem s4_selected_curve_mixed_divisor_cup
    (A Y : Over (Spec ↧ℂ)) [GrpObj A] [IsCommMonObj A]
    [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (f : Y ⟶ A) (v w : HQ A 1) :
    s4_selected_curve_mixed_divisor A Y f ((cupProductOf A).cup rfl v w) =
      (cupProductOf (A ⊗ Y)).cup rfl
        (homPullback (fst A Y) 1 v)
        (homPullback (snd A Y) 1 (homPullback f 1 w)) -
      (cupProductOf (A ⊗ Y)).cup rfl
        (homPullback (fst A Y) 1 w)
        (homPullback (snd A Y) 1 (homPullback f 1 v)) := by
  have hadd : s4_selected_curve_add_map A Y f = (snd A Y ≫ f) * fst A Y := by
    simp [s4_selected_curve_add_map, cfd_shear, MonObj.comp_mul]
  have hc := (cupProductOf (A ⊗ Y)).graded_comm rfl rfl
    (homPullback (fst A Y) 1 w)
    (homPullback (snd A Y) 1 (homPullback f 1 v))
  simp only [Nat.mul_one, pow_one, neg_one_smul] at hc
  unfold s4_selected_curve_mixed_divisor
  rw [hadd]
  simp only [spec_homPullback_cup, s4_homPullback_mul, spec_homPullback_comp,
    LinearMap.comp_apply, LinearMap.add_apply, map_add]
  rw [hc]
  abel

#print axioms s4_selected_curve_mixed_divisor_cup
end HodgeLean.Foundations.Program
