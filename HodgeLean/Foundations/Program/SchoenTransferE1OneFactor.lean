import HodgeLean.Foundations.Program.SchoenTransferE1Defs

/-! The degree-one cup for a single curve factor. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option maxRecDepth 4000

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open scoped TensorProduct
open HodgeLean.RealDefs HodgeLean.Adapters

namespace HodgeLean.Foundations.Program

/-- Pullback along an actual scheme isomorphism is bijective in each degree.
Source: Hatcher, Algebraic Topology, §3.1, functoriality of cohomology. -/
theorem s4_e1_pullback_iso_bijective
    {Y T : Over (Spec ↧ℂ)}
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    [IsIntegral T.left] [Smooth T.hom] [IsProjective T.hom]
    (e : T ≅ Y) (n : ℕ) : Function.Bijective (homPullback e.hom n) := by
  have hl : (homPullback e.inv n).comp (homPullback e.hom n) = LinearMap.id := by
    rw [← spec_homPullback_comp, e.inv_hom_id, spec_homPullback_id]
  have hr : (homPullback e.hom n).comp (homPullback e.inv n) = LinearMap.id := by
    rw [← spec_homPullback_comp, e.hom_inv_id, spec_homPullback_id]
  constructor
  · apply Function.LeftInverse.injective (g := homPullback e.inv n)
    intro x
    simpa only [LinearMap.comp_apply, LinearMap.id_apply] using LinearMap.congr_fun hl x
  · apply Function.RightInverse.surjective (g := homPullback e.inv n)
    intro x
    simpa only [LinearMap.comp_apply, LinearMap.id_apply] using LinearMap.congr_fun hr x

/-- The single-factor indexed cup is the coordinate pullback after the singleton tensor equivalence.
Source: Hatcher, Algebraic Topology, §3.2, the unit of the cup product. -/
theorem s4_e1_oneCup_one_factor
    (Y : Over (Spec ↧ℂ)) [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    [IsIntegral (g3_power Y 1).left] [Smooth (g3_power Y 1).hom]
    [IsProjective (g3_power Y 1).hom] :
    s4_e1_oneCup Y 1 = (homPullback (g3_proj Y 1 0) 1).comp
      (PiTensorProduct.subsingletonEquiv (R := ℚ)
        (s := fun _ : Fin 1 => HQ Y 1) 0).toLinearMap := by
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro v
  simp only [LinearMap.compMultilinearMap_apply, s4_e1_oneCup,
    PiTensorProduct.lift.tprod, MultilinearMap.compLinearMap_apply,
    LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
    PiTensorProduct.subsingletonEquiv_apply_tprod]
  exact (cupProductOf (g3_power Y 1)).cup_one _

/-- The single-factor degree-one cup is bijective.
Source: Hatcher, Algebraic Topology, §3.2; the scheme product unitor. -/
theorem s4_e1_oneCup_one_bijective
    (Y : Over (Spec ↧ℂ)) [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    [IsIntegral (g3_power Y 1).left] [Smooth (g3_power Y 1).hom]
    [IsProjective (g3_power Y 1).hom] : Function.Bijective (s4_e1_oneCup Y 1) := by
  let e : g3_power Y 1 ≅ Y := ρ_ Y
  have hp : g3_proj Y 1 0 = e.hom := (CartesianMonoidalCategory.rightUnitor_hom Y).symm
  rw [s4_e1_oneCup_one_factor, hp]
  exact (s4_e1_pullback_iso_bijective e 1).comp
    (PiTensorProduct.subsingletonEquiv (R := ℚ)
      (s := fun _ : Fin 1 => HQ Y 1) 0).bijective

#print axioms s4_e1_pullback_iso_bijective
#print axioms s4_e1_oneCup_one_factor
#print axioms s4_e1_oneCup_one_bijective
end HodgeLean.Foundations.Program
