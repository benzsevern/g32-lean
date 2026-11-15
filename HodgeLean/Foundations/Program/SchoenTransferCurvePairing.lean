import HodgeLean.Foundations.Program.SchoenTransferE1
import HodgeLean.Foundations.Program.SchoenTransferCharacterProducts

noncomputable section
set_option maxHeartbeats 200000
set_option maxRecDepth 2048
set_option synthInstance.maxHeartbeats 200000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open scoped TensorProduct
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Foundations
namespace HodgeLean.Foundations.Program
attribute [local irreducible] cupProductOf homPullback

/-- Equal nonquadratic eigencharacters pair trivially on a smooth projective curve.
Source: Hatcher, Algebraic Topology, §3.2, naturality of cup products and top orientation. -/
theorem s4_curve_equal_character_cup_zero
    (Y : Over (Spec ↧ℂ)) [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (hdim : TopologicalSpace.dim Y.left = 1) (δ : Y ⟶ Y) [IsIso δ]
    (c : ℂ) (hc : c * c ≠ 1)
    {x y : ℂ ⊗[ℚ] HQ Y 1}
    (hx : (homPullback δ 1).baseChange ℂ x = c • x)
    (hy : (homPullback δ 1).baseChange ℂ y = c • y) :
    (cupProductOf Y).cupC (show 1 + 1 = 2 from rfl) x y = 0 := by
  apply invariant_bilinear_equal_character_zero
    ((cupProductOf Y).cupC rfl) ((homPullback δ 1).baseChange ℂ) c hc _ hx hy
  intro u v
  have hn : (homPullback δ 2).baseChange ℂ ((cupProductOf Y).cupC rfl u v) =
      (cupProductOf Y).cupC rfl ((homPullback δ 1).baseChange ℂ u)
        ((homPullback δ 1).baseChange ℂ v) := by
    induction u using TensorProduct.inductionOn with
    | add u u' hu hu' =>
      simp only [map_add, LinearMap.add_apply, hu, hu']
    | tmul z u =>
      induction v using TensorProduct.inductionOn with
      | add v v' hv hv' => simp only [map_add, hv, hv']
      | tmul w v =>
        simp only [CupProduct.cupC_tmul, LinearMap.baseChange_tmul,
          spec_homPullback_cup]
  letI : SmoothOfRelativeDimension 1 Y.hom := by
    rw [← hdim]
    infer_instance
  have ht : homPullback δ 2 = LinearMap.id := s4_e1_top_rational_action Y 1 (asIso δ)
  rw [ht, LinearMap.baseChange_id, LinearMap.id_apply] at hn
  exact hn.symm

end HodgeLean.Foundations.Program
