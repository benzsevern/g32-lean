import HodgeLean.Foundations.Program.CompensationAssemblyContraction
import HodgeLean.Foundations.Program.CompensationAssemblyCycleLinear

noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 2048
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj TensorProduct
open HodgeLean.RealDefs HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

variable (A Y : Over (Spec ↧ℂ))
    [GrpObj A] [IsCommMonObj A] [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    [GrpObj Y] [IsCommMonObj Y] [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]

theorem cq_degree_one_product_equiv_unique
    (e e' : (HQ A 1 × HQ Y 1) ≃ₗ[ℚ] HQ (A ⊗ Y) 1)
    (heA : ∀ a, e (a, 0) = homPullback (fst A Y) 1 a)
    (heY : ∀ b, e (0, b) = homPullback (snd A Y) 1 b)
    (heA' : ∀ a, e' (a, 0) = homPullback (fst A Y) 1 a)
    (heY' : ∀ b, e' (0, b) = homPullback (snd A Y) 1 b) : e = e' := by
  apply LinearEquiv.ext
  rintro ⟨a, b⟩
  have hpair : (a, b) = (a, 0) + (0, b) := by
    rw [Prod.mk_add_mk, add_zero, zero_add]
  rw [hpair, map_add, map_add, heA, heY, heA', heY']

theorem cq_surface_integration_point
    (I : HQ Y 4 ≃ₗ[ℚ] ℚ)
    (hI : ∀ c : AlgebraicCycle Y.left ℚ,
      (∀ x, c x ≠ 0 → Order.coheight x = 2) →
      I (ccm3_cycleClass Y 2 c) = AlgebraicCycle.degree Y.hom c)
    (x : Y.left) (hx : Order.coheight x = 2) (hxc : IsClosed ({x} : Set Y.left)) :
    I (cycleComponentSheafClass Y x hx) = 1 := by
  classical
  let c : AlgebraicCycle Y.left ℚ :=
    (Function.locallyFinsuppWithin.single x 1).restrict (Set.subset_univ _)
  have hc : ∀ z, c z ≠ 0 → Order.coheight z = 2 := by
    intro z hz
    by_cases hzx : z = x
    · exact hzx ▸ hx
    · exfalso
      apply hz
      simp only [c, Function.locallyFinsuppWithin.restrict_apply, Set.mem_univ,
        ↓reduceIte, Function.locallyFinsuppWithin.single_apply, if_neg hzx]
  have hclass : ccm3_cycleClass Y 2 c = cycleComponentSheafClass Y x hx := by
    simpa only [one_smul] using cq_cycle_single_eq 2 x hx (1 : ℚ)
  have hdeg : AlgebraicCycle.degree Y.hom c = 1 := by
    rw [show c = Function.locallyFinsuppWithin.single x (1 : ℚ) from
      cq_single_restrict_univ Y.left x 1, AlgebraicCycle.degree_single,
      Curves.residueDegree_eq_one hxc, one_smul]
  rw [← hclass, hI c hc, hdeg]

theorem cq_surface_integration_unique
    (hY : TopologicalSpace.dim Y.left = 2)
    (I J : HQ Y 4 ≃ₗ[ℚ] ℚ)
    (hI : ∀ c : AlgebraicCycle Y.left ℚ,
      (∀ x, c x ≠ 0 → Order.coheight x = 2) →
      I (ccm3_cycleClass Y 2 c) = AlgebraicCycle.degree Y.hom c)
    (hJ : ∀ c : AlgebraicCycle Y.left ℚ,
      (∀ x, c x ≠ 0 → Order.coheight x = 2) →
      J (ccm3_cycleClass Y 2 c) = AlgebraicCycle.degree Y.hom c) : I = J := by
  classical
  letI : SmoothOfRelativeDimension 2 Y.hom := by
    have h := SmoothOfRelativeDimension.of_isIntegral (X := Y.left) (f := Y.hom)
    rwa [hY] at h
  obtain ⟨x, _, hxc⟩ := isClosed_univ.exists_closed_singleton
    (Set.univ_nonempty (α := Y.left))
  have hx : Order.coheight x = 2 :=
    SmoothOfRelativeDimension.coheight_eq_dimension_of_isClosed (f := Y.hom) x hxc
  let v : HQ Y 4 := cycleComponentSheafClass Y x hx
  have hIv : I v = 1 := cq_surface_integration_point Y I hI x hx hxc
  have hJv : J v = 1 := cq_surface_integration_point Y J hJ x hx hxc
  apply LinearEquiv.ext
  intro w
  have hw : w = I w • v := by
    apply I.injective
    rw [map_smul, hIv, smul_eq_mul, mul_one]
  rw [hw, map_smul, map_smul, hIv, hJv]

theorem cq_projectionMap_independent
    (hY : TopologicalSpace.dim Y.left = 2)
    (I J : HQ Y 4 ≃ₗ[ℚ] ℚ)
    (hI : ∀ c : AlgebraicCycle Y.left ℚ,
      (∀ x, c x ≠ 0 → Order.coheight x = 2) →
      I (ccm3_cycleClass Y 2 c) = AlgebraicCycle.degree Y.hom c)
    (hJ : ∀ c : AlgebraicCycle Y.left ℚ,
      (∀ x, c x ≠ 0 → Order.coheight x = 2) →
      J (ccm3_cycleClass Y 2 c) = AlgebraicCycle.degree Y.hom c)
    (e e' : (HQ A 1 × HQ Y 1) ≃ₗ[ℚ] HQ (A ⊗ Y) 1)
    (heA : ∀ a, e (a, 0) = homPullback (fst A Y) 1 a)
    (heY : ∀ b, e (0, b) = homPullback (snd A Y) 1 b)
    (heA' : ∀ a, e' (a, 0) = homPullback (fst A Y) 1 a)
    (heY' : ∀ b, e' (0, b) = homPullback (snd A Y) 1 b) :
    cq_projectionMap A Y I e = cq_projectionMap A Y J e' := by
  rw [cq_surface_integration_unique Y hY I J hI hJ,
    cq_degree_one_product_equiv_unique A Y e e' heA heY heA' heY']

end HodgeLean.Foundations.Program
