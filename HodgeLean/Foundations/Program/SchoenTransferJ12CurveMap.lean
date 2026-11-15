import HodgeLean.Foundations.Program.SchoenTransferJ12AbelComparison
import HodgeLean.Foundations.Program.SchoenTransferJ12AbelFactorH1
import HodgeLean.Foundations.Program.SchoenTransferJ12SquareRealization

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.Adapters HodgeLean.RealDefs HodgeLean.Foundations
open HodgeLean.Foundations.Curves.AbelAdapter
open scoped Manifold ContDiff CategoryTheory.MonObj
namespace HodgeLean.Foundations.Program
attribute [local irreducible] homPullback

/-- An injective native curve square realizes its specified rational upper map by an actual morphism. -/
theorem s4_selected_curve_map_of_square
    (X Y P : Over (Spec ↧ℂ)) [GrpObj P] [IsCommMonObj P]
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    [IsIntegral P.left] [Smooth P.hom] [IsProjective P.hom]
    (hdimX : TopologicalSpace.dim X.left = 1)
    (hdimY : TopologicalSpace.dim Y.left = 1)
    (q : X ⟶ Y) (hq : Function.Injective (homPullback q 1))
    (jP : X ⟶ P) (T : HQ P 1 →ₗ[ℚ] HQ Y 1)
    (hsq : (homPullback q 1).comp T = homPullback jP 1) :
    ∃ (N : ℕ) (u : Y ⟶ P), 0 < N ∧
      ∀ v, homPullback u 1 v = (N : ℚ) • T v := by
  letI := connectedSpace_complexPoint X
  letI := connectedSpace_complexPoint Y
  let pX : ComplexPoint X := Classical.choice inferInstance
  let pY : ComplexPoint Y := Point.map q pX
  have hX : Module.finrank ℂ (Fin (TopologicalSpace.dim X.left) → ℂ) = 1 := by
    simpa only [Module.finrank_pi, Module.finrank_self, Fintype.card_fin,
      smul_eq_mul, mul_one] using hdimX
  have hY : Module.finrank ℂ (Fin (TopologicalSpace.dim Y.left) → ℂ) = 1 := by
    simpa only [Module.finrank_pi, Module.finrank_self, Fintype.card_fin,
      smul_eq_mul, mul_one] using hdimY
  obtain ⟨jX, hjX, hbijX⟩ := s4_selected_algebraic_abel_exists X hdimX pX
  obtain ⟨jY, hjY, hbijY⟩ := s4_selected_algebraic_abel_exists Y hdimY pY
  let D := model (C := ComplexPoint X) hX
  let B := model (C := ComplexPoint Y) hY
  letI : IsCommMonObj D := isCommMonObj_of_complexSelfProductIntegral D
    (complexSelfProductIntegral_of_isIntegral D)
  letI : IsCommMonObj B := isCommMonObj_of_complexSelfProductIntegral B
    (complexSelfProductIntegral_of_isIntegral B)
  obtain ⟨π, hπ, hπeq⟩ := s4_selected_abel_factor_H1 X B hX pX jX hjX (q ≫ jY)
  obtain ⟨α, hα, hαeq⟩ := s4_selected_abel_factor_H1 X P hX pX jX hjX jP
  letI := hπ
  letI := hα
  have hπeq' : (homPullback jX 1).comp (homPullback π 1) =
      (homPullback q 1).comp (homPullback jY 1) :=
    hπeq.trans (spec_homPullback_comp q jY 1)
  have hπinj : Function.Injective (homPullback π 1) := by
    intro v w hvw
    apply hbijY.1
    apply hq
    calc
      homPullback q 1 (homPullback jY 1 v) =
          homPullback jX 1 (homPullback π 1 v) := (LinearMap.congr_fun hπeq' v).symm
      _ = homPullback jX 1 (homPullback π 1 w) := congrArg (homPullback jX 1) hvw
      _ = homPullback q 1 (homPullback jY 1 w) := LinearMap.congr_fun hπeq' w
  let EY := LinearEquiv.ofBijective (homPullback jY 1) hbijY
  let TB := EY.symm.toLinearMap.comp T
  have hTB (v) : homPullback jY 1 (TB v) = T v := EY.apply_symm_apply (T v)
  have hsqB : (homPullback π 1).comp TB = homPullback α 1 := by
    ext v
    apply hbijX.1
    calc
      homPullback jX 1 (homPullback π 1 (TB v)) =
          homPullback q 1 (homPullback jY 1 (TB v)) := LinearMap.congr_fun hπeq' (TB v)
      _ = homPullback q 1 (T v) := congrArg (homPullback q 1) (hTB v)
      _ = homPullback jP 1 v := LinearMap.congr_fun hsq v
      _ = homPullback jX 1 (homPullback α 1 v) := (LinearMap.congr_fun hαeq v).symm
  obtain ⟨N, u, hN, hu⟩ := s4_selected_square_realization B D P π α hπinj TB hsqB Y jY
  exact ⟨N, u, hN, fun v => (hu v).trans (congrArg (fun z => (N : ℚ) • z) (hTB v))⟩

#print axioms s4_selected_curve_map_of_square

end HodgeLean.Foundations.Program
