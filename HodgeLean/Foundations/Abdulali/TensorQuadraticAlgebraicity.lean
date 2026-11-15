import HodgeLean.Foundations.Abdulali.TensorProductAlgebraicity
import HodgeLean.Foundations.Abdulali.ScalarSpan

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open scoped CategoryTheory.MonObj TensorProduct
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Foundations
open HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.Abdulali
attribute [local irreducible] cupProductOf algebraicCycleClassSpan complexCupEquiv

variable {V : Type*} [AddCommGroup V] [Module ℂ V]
variable (Y : Over (Spec ↧ℂ)) [GrpObj Y] [IsCommMonObj Y]
  [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]

/-- Products of quadratic tensors with algebraic alternating images remain
algebraic, with arbitrary permutations of all slots and the scalar degree.
Source: Fulton, Intersection Theory, Corollary 19.2. -/
theorem tensor_quadratic_products_algebraic
    (f : V →ₗ[ℂ] (ℂ ⊗[ℚ] HQ Y 1))
    (Q : Submodule ℂ (⨂[ℂ]^2 V))
    (hQ : ∀ t ∈ Q, complexCupEquiv Y 2 (exteriorPower.map 2 f
      (InvariantsExterior.wedgeQuotient 2 t)) ∈ (algebraicCycleClassSpan Y 1).baseChange ℂ)
    (p : ℕ) : ∀ t ∈ m1b_products Q (2*p),
      complexCupEquiv Y (2*p) (exteriorPower.map (2*p) f
        (InvariantsExterior.wedgeQuotient (2*p) t)) ∈
          (algebraicCycleClassSpan Y p).baseChange ℂ := by
  let F (n : ℕ) : (⨂[ℂ]^n V) →ₗ[ℂ] (ℂ ⊗[ℚ] HQ Y n) :=
    (complexCupEquiv Y n).toLinearMap.comp
      ((exteriorPower.map n f).comp (InvariantsExterior.wedgeQuotient n))
  change ∀ t ∈ m1b_products Q (2*p), F (2*p) t ∈
    (algebraicCycleClassSpan Y p).baseChange ℂ
  induction p with
  | zero =>
    intro t ht
    exact mem_complex_span_of_eq_top (algebraicCycleClassSpan Y 0)
      (algebraicCycleClassSpan_zero_eq_top_unconditional Y)
      (F 0 t)
  | succ p ih =>
    intro t ht
    change t ∈ Submodule.span ℂ _ at ht
    induction ht using Submodule.span_induction with
    | mem t ht =>
      obtain ⟨σ, a, b, ha, hb, rfl⟩ := ht
      dsimp only [F, LinearMap.comp_apply, LinearEquiv.coe_coe]
      erw [m3_wedgeQuotient_permRep, map_zsmul, map_zsmul, tensorCup_append]
      erw [← Int.cast_smul_eq_zsmul ℂ]
      apply Submodule.smul_mem
      have ha' : complexCupEquiv Y (2*p)
          (exteriorPower.map (2*p) f (InvariantsExterior.wedgeQuotient (2*p) a)) ∈
          (algebraicCycleClassSpan Y p).baseChange ℂ := ih a ha
      have hb' := hQ b hb
      have hmul := g32c_cupC_span Y p 1 (p+1) rfl _ _ ha' hb'
      convert hmul using 1
    | zero =>
      rw [map_zero]
      exact Submodule.zero_mem _
    | add a b ha hb hia hib =>
      rw [map_add]
      exact Submodule.add_mem _ hia hib
    | smul c a ha hia =>
      rw [map_smul]
      exact Submodule.smul_mem _ c hia

end HodgeLean.Foundations.Abdulali
