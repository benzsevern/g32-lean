import HodgeLean.Foundations.Program.SchoenTransferE2ChainDefs

noncomputable section
set_option maxHeartbeats 200000
set_option maxRecDepth 2048
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open scoped TensorProduct
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Foundations
namespace HodgeLean.Foundations.Program
attribute [local irreducible] cupProductOf homPullback

/-- Exterior scalar extension realizes the actual complex multilinear cup product.
Source: Hatcher, Algebraic Topology, §3.2, extension of scalars and cup products. -/
theorem s4_complex_cup_linearization
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    [Module.Finite ℚ (HQ X 1)] (h : ℕ) :
    ((((cupProductOf X).cupWedgeMap h).baseChange ℂ ∘ₗ
      (HodgeBlocks.WeilAction.exteriorPowerBaseChangeEquiv
        (V := HQ X 1) h).symm.toLinearMap).compAlternatingMap
      (exteriorPower.ιMulti ℂ h)).toMultilinearMap = (cupProductOf X).cupMultiC h := by
  let b := Module.finBasis ℚ (HQ X 1)
  refine Module.Basis.ext_multilinear (fun _ => b.baseChange ℂ) fun σ => ?_
  simp only [Module.Basis.baseChange_apply, AlternatingMap.coe_multilinearMap,
    LinearMap.compAlternatingMap_apply, LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [CupProduct.cupMultiC_tmul,
    ← HodgeBlocks.complexifyWedge_ιMulti (V := HQ X 1) h (fun i => b (σ i)),
    ← HodgeBlocks.WeilAction.exteriorPowerBaseChangeEquiv_tmul,
    LinearEquiv.symm_apply_apply, LinearMap.baseChange_tmul,
    CupProduct.cupWedgeMap_ιMulti]

/-- Permuting complex degree-one cup factors multiplies by the permutation sign.
Source: Hatcher, Algebraic Topology, §3.2, graded commutativity. -/
theorem s4_complex_cup_permutation
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    [Module.Finite ℚ (HQ X 1)] (h : ℕ)
    (v : Fin h → ℂ ⊗[ℚ] HQ X 1) (σ : Equiv.Perm (Fin h)) :
    (cupProductOf X).cupMultiC h (v ∘ σ) =
      σ.sign • (cupProductOf X).cupMultiC h v := by
  rw [← s4_complex_cup_linearization X h]
  exact AlternatingMap.map_perm _ v σ

end HodgeLean.Foundations.Program
