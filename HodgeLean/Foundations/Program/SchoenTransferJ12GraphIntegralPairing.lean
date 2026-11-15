import HodgeLean.Foundations.Program.SchoenTransferJ12GraphShearIntegral
import HodgeLean.Foundations.Program.SchoenTransferJ12ProductIntegralPoint
import HodgeLean.Foundations.Program.SchoenTransferJ12PointTranslateMap

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj
open HodgeLean.RealDefs HodgeLean.Adapters
namespace HodgeLean.Foundations.Program
attribute [local irreducible] cupProductOf homPullback s4_selected_projection

/-- The actual graph-normal top integral pairs a pulled-back target class with the original source class.
Source: the difference shear change of variables and normalized restriction to an actual point section. -/
theorem s4_selected_graph_integral_pairing
    (A Y : Over (Spec ↧ℂ)) [GrpObj A] [IsCommMonObj A]
    [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (a d p q : ℕ) (hA : TopologicalSpace.dim A.left = a) (hY : TopologicalSpace.dim Y.left = d)
    (hpq : q + p = d)
    (IA : HQ A (2 * a) ≃ₗ[ℚ] ℚ) (IY : HQ Y (2 * d) ≃ₗ[ℚ] ℚ)
    (e : ComplexPoint A) (hec : Order.coheight e.underlying = a)
    (he : IA (cycleComponentSheafClass A e.underlying hec) = 1)
    (f : Y ⟶ A) (w : HQ A (2 * q)) (b : HQ Y (2 * p)) :
    s4_selected_product_integral A Y a d IA IY
      ((cupProductOf (A ⊗ Y)).cup (by omega : 2 * q + (2 * a + 2 * p) = 2 * a + 2 * d)
        (homPullback (fst A Y) (2 * q) w)
        ((cupProductOf (A ⊗ Y)).cup rfl
          (homPullback ((s4_selected_graph_shear A Y f).hom ≫ fst A Y) (2 * a)
            (cycleComponentSheafClass A e.underlying hec))
          (homPullback (snd A Y) (2 * p) b))) =
    IY ((cupProductOf Y).cup (by omega : 2 * q + 2 * p = 2 * d)
      (homPullback f (2 * q) w) b) := by
  let σ := s4_selected_graph_shear A Y f
  let t := cycleComponentSheafClass A e.underlying hec
  let T := s4_selected_product_integral A Y a d IA IY
  let u := homPullback σ.inv (2 * q) (homPullback (fst A Y) (2 * q) w)
  let v := (cupProductOf (A ⊗ Y)).cup (by omega : 2 * q + 2 * p = 2 * d)
    u (homPullback (snd A Y) (2 * p) b)
  let z := (cupProductOf (A ⊗ Y)).cup (by omega : 2 * q + (2 * a + 2 * p) = 2 * a + 2 * d)
    u ((cupProductOf (A ⊗ Y)).cup rfl
      (homPullback (fst A Y) (2 * a) t) (homPullback (snd A Y) (2 * p) b))
  have hu : homPullback σ.hom (2 * q) u = homPullback (fst A Y) (2 * q) w := by
    change homPullback σ.hom (2 * q)
      (homPullback σ.inv (2 * q) (homPullback (fst A Y) (2 * q) w)) = _
    rw [← LinearMap.comp_apply, ← spec_homPullback_comp, σ.hom_inv_id,
      spec_homPullback_id, LinearMap.id_apply]
  have ht : homPullback σ.hom (2 * a) (homPullback (fst A Y) (2 * a) t) =
      homPullback (σ.hom ≫ fst A Y) (2 * a) t := by
    rw [spec_homPullback_comp, LinearMap.comp_apply]
  have hb : homPullback σ.hom (2 * p) (homPullback (snd A Y) (2 * p) b) =
      homPullback (snd A Y) (2 * p) b := by
    rw [← LinearMap.comp_apply, ← spec_homPullback_comp, s4_selected_graph_shear_snd]
  have hz : homPullback σ.hom (2 * a + 2 * d) z =
      (cupProductOf (A ⊗ Y)).cup (by omega : 2 * q + (2 * a + 2 * p) = 2 * a + 2 * d)
        (homPullback (fst A Y) (2 * q) w)
        ((cupProductOf (A ⊗ Y)).cup rfl
          (homPullback (σ.hom ≫ fst A Y) (2 * a) t)
          (homPullback (snd A Y) (2 * p) b)) := by
    dsimp only [z]
    rw [spec_homPullback_cup, spec_homPullback_cup, hu, ht, hb]
  have htrace : T (homPullback σ.hom (2 * a + 2 * d) z) = T z :=
    s4_selected_graph_shear_top_integral A Y a d hA hY IA IY f z
  have hcomm : (cupProductOf (A ⊗ Y)).cup (by omega : 2 * q + 2 * a = 2 * a + 2 * q)
      u (homPullback (fst A Y) (2 * a) t) =
      (cupProductOf (A ⊗ Y)).cup rfl (homPullback (fst A Y) (2 * a) t) u := by
    have hs : (-1 : ℚ) ^ ((2 * q) * (2 * a)) = 1 := by
      rw [show (2 * q) * (2 * a) = 2 * (q * (2 * a)) by ring, pow_mul]
      norm_num
    have h := (cupProductOf (A ⊗ Y)).graded_comm (by omega : 2 * q + 2 * a = 2 * a + 2 * q)
      rfl u (homPullback (fst A Y) (2 * a) t)
    simpa only [hs, one_smul] using h.symm
  have hzpoint : z = (cupProductOf (A ⊗ Y)).cup rfl
      (homPullback (fst A Y) (2 * a) t) v := by
    dsimp only [z, v]
    rw [← (cupProductOf (A ⊗ Y)).assoc (by omega : 2 * q + 2 * a = 2 * a + 2 * q)
      rfl (by omega) (by omega), hcomm,
      (cupProductOf (A ⊗ Y)).assoc rfl (by omega : 2 * q + 2 * p = 2 * d) (by omega) rfl]
  let c : Y ⟶ A := (Over.homMk Y.hom : Y ⟶ Over.mk (𝟙 (Spec ↧ℂ))) ≫ e
  let s : Y ⟶ A ⊗ Y := lift c (𝟙 Y)
  have hsection : (s ≫ σ.inv) ≫ fst A Y = c * f := by
    simp [s, σ, s4_selected_graph_shear, cfd_shear, MonObj.comp_mul, mul_comm]
  have hsw : homPullback s (2 * q) u = homPullback f (2 * q) w := by
    change homPullback s (2 * q)
      (homPullback σ.inv (2 * q) (homPullback (fst A Y) (2 * q) w)) = _
    rw [← LinearMap.comp_apply, ← spec_homPullback_comp,
      ← LinearMap.comp_apply, ← spec_homPullback_comp, hsection,
      s4_selected_point_translate_map_pullback A Y e f (2 * q)]
  have hsb : homPullback s (2 * p) (homPullback (snd A Y) (2 * p) b) = b := by
    rw [← LinearMap.comp_apply, ← spec_homPullback_comp, lift_snd,
      spec_homPullback_id, LinearMap.id_apply]
  calc
    _ = T (homPullback σ.hom (2 * a + 2 * d) z) := congrArg T hz.symm
    _ = T z := htrace
    _ = T ((cupProductOf (A ⊗ Y)).cup rfl (homPullback (fst A Y) (2 * a) t) v) := congrArg T hzpoint
    _ = IY (homPullback s (2 * d) v) :=
      s4_selected_product_integral_point_cup A Y a d hA hY IA IY e t he v
    _ = _ := by
      dsimp only [v]
      rw [spec_homPullback_cup, hsw, hsb]

#print axioms s4_selected_graph_integral_pairing
end HodgeLean.Foundations.Program
