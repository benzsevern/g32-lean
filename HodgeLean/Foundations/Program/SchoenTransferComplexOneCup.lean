import HodgeLean.Foundations.Program.SchoenTransferTensorBaseChange
import HodgeLean.Foundations.Program.SchoenTransferComplexPullback
import HodgeLean.Foundations.Program.SchoenTransferAlternatingCupInjection

noncomputable section
set_option maxHeartbeats 200000
set_option maxRecDepth 2048
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open scoped TensorProduct
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Foundations
namespace HodgeLean.Foundations.Program
attribute [local irreducible] cupProductOf homPullback

/-- The actual ordered coordinate cup product on complex tensor factors.
Source: Schoen (1988), Lemma 1.2, pp. 5–6; Hatcher, Algebraic Topology, §3.2. -/
def s4_complexOneCup (Y : Over (Spec ↧ℂ))
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom] (h : ℕ)
    [IsIntegral (g3_power Y h).left] [Smooth (g3_power Y h).hom]
    [IsProjective (g3_power Y h).hom] :
    (⨂[ℂ] i : Fin h, ℂ ⊗[ℚ] HQ Y 1) →ₗ[ℂ] ℂ ⊗[ℚ] HQ (g3_power Y h) h :=
  PiTensorProduct.lift (((cupProductOf (g3_power Y h)).cupMultiC h).compLinearMap
    (fun i => (homPullback (g3_proj Y h i) 1).baseChange ℂ))

example (Y : Over (Spec ↧ℂ)) [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (h : ℕ) [IsIntegral (g3_power Y h).left] [Smooth (g3_power Y h).hom]
    [IsProjective (g3_power Y h).hom] : s4_complexOneCup Y h 0 = 0 := map_zero _

/-- Scalar extension identifies the rational and complex ordered tensor cup maps. -/
theorem s4_complexOneCup_scalarExtension
    (Y : Over (Spec ↧ℂ)) [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (h : ℕ) [IsIntegral (g3_power Y h).left] [Smooth (g3_power Y h).hom]
    [IsProjective (g3_power Y h).hom]
    {B : Type*} (b : Module.Basis B ℚ (HQ Y 1)) :
    (s4_complexOneCup Y h).comp (s4_tensorBaseChangeEquiv (L := ℂ) (I := Fin h) b).toLinearMap =
      (s4_e1_oneCup Y h).baseChange ℂ := by
  apply ((Basis.piTensorProduct (fun _ : Fin h => b)).baseChange ℂ).ext
  intro v
  simp only [Module.Basis.baseChange_apply, Basis.piTensorProduct_apply,
    LinearMap.comp_apply, LinearEquiv.coe_coe, s4_tensorBaseChangeEquiv_basis,
    s4_complexOneCup, PiTensorProduct.lift.tprod, MultilinearMap.compLinearMap_apply,
    LinearMap.baseChange_tmul, CupProduct.cupMultiC_tmul,
    s4_e1_oneCup]

/-- The actual complex ordered cup map is injective for a curve. -/
theorem s4_complexOneCup_injective
    (Y : Over (Spec ↧ℂ)) [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (hdim : TopologicalSpace.dim Y.left = 1)
    (h : ℕ) [IsIntegral (g3_power Y h).left] [Smooth (g3_power Y h).hom]
    [IsProjective (g3_power Y h).hom] : Function.Injective (s4_complexOneCup Y h) := by
  letI := (finbetti_finiteBetti Y).finite 1
  let E := s4_tensorBaseChangeEquiv (L := ℂ) (I := Fin h) (Module.finBasis ℚ (HQ Y 1))
  have hi : Function.Injective ((s4_e1_oneCup Y h).baseChange ℂ) :=
    Module.Flat.lTensor_preserves_injective_linearMap _ (s4_oneCup_injective Y hdim h)
  intro x y hxy
  apply E.symm.injective
  apply hi
  rw [← s4_complexOneCup_scalarExtension Y h (Module.finBasis ℚ (HQ Y 1))]
  simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, E, LinearEquiv.apply_symm_apply] using hxy

end HodgeLean.Foundations.Program
