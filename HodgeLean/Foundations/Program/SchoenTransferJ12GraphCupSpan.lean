import HodgeLean.Foundations.Program.SchoenTransferJ12GraphShear
import HodgeLean.Foundations.Program.SchoenTransferJ12PointExternalSpan
import HodgeLean.Foundations.Program.CompensationAssemblyPullback

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint MonoidalCategory TopologicalSpace
open CategoryTheory.CartesianMonoidalCategory
open HodgeLean.RealDefs HodgeLean.Adapters
namespace HodgeLean.Foundations.Program
attribute [local irreducible] cupProductOf homPullback

/-- A graph normal class cupped with a source cycle class is algebraic over an abelian target.
Source: the actual group shear, smooth pullback of cycles, and point external support purity. -/
theorem s4_selected_graph_cup_span
    (A Y : Over (Spec ↧ℂ)) [GrpObj A]
    [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (a : ℕ) (hA : TopologicalSpace.dim A.left = a)
    (e : ComplexPoint A) (hec : Order.coheight e.underlying = a)
    (f : Y ⟶ A) (p : ℕ) (b : HQ Y (2 * p)) (hb : b ∈ cfd_cycleSpan Y p) :
    (cupProductOf (A ⊗ Y)).cup (by omega : 2 * a + 2 * p = 2 * (a + p))
      (homPullback ((s4_selected_graph_shear A Y f).hom ≫ fst A Y) (2 * a)
        (cycleComponentSheafClass A e.underlying hec))
      (homPullback (snd A Y) (2 * p) b) ∈ cfd_cycleSpan (A ⊗ Y) (a + p) := by
  let σ := s4_selected_graph_shear A Y f
  letI : Smooth σ.hom.left := inferInstance
  have hext := s4_selected_point_external_span A Y a hA e hec p b hb
  have hpb := cq_smooth_pullback_span_core σ.hom (a + p) (Submodule.mem_map_of_mem hext)
  have hsnd : homPullback σ.hom (2 * p) (homPullback (snd A Y) (2 * p) b) =
      homPullback (snd A Y) (2 * p) b := by
    rw [← LinearMap.comp_apply, ← spec_homPullback_comp, s4_selected_graph_shear_snd]
  have hfst : homPullback σ.hom (2 * a)
      (homPullback (fst A Y) (2 * a) (cycleComponentSheafClass A e.underlying hec)) =
      homPullback (σ.hom ≫ fst A Y) (2 * a) (cycleComponentSheafClass A e.underlying hec) := by
    rw [spec_homPullback_comp, LinearMap.comp_apply]
  change (cupProductOf (A ⊗ Y)).cup (by omega : 2 * a + 2 * p = 2 * (a + p))
    (homPullback ((s4_selected_graph_shear A Y f).hom ≫ fst A Y) (2 * a)
      (cycleComponentSheafClass A e.underlying hec))
    (homPullback (snd A Y) (2 * p) b) ∈ algebraicCycleClassSpan (A ⊗ Y) (a + p)
  simpa only [spec_homPullback_cup, hsnd, hfst, σ] using hpb

#print axioms s4_selected_graph_cup_span
end HodgeLean.Foundations.Program
