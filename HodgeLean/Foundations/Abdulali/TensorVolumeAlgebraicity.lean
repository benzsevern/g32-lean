import HodgeLean.Foundations.Abdulali.TensorEvenAlgebraicity
import HodgeLean.Foundations.Abdulali.SpecialOrthogonalGeneration

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000
set_option Elab.async false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open scoped CategoryTheory.MonObj TensorProduct
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Foundations
open HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.Abdulali
attribute [local irreducible] cupProductOf algebraicCycleClassSpan
variable (Y : Over (Spec ↧ℂ)) [GrpObj Y] [IsCommMonObj Y]
  [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]

/-- A quadratic product times a labelled six-dimensional volume has an algebraic
alternating image whenever both generator families do.
Source: Weyl, The Classical Groups, II.17; Fulton, Corollary 19.2. -/
theorem tensor_volume_products_algebraic (r : ℕ)
    (B : LinearMap.BilinForm ℂ (Fin 6 → ℂ)) (hB : B.Nondegenerate)
    (hs : ∀ x y, B x y = B y x)
    (f : (Fin r → Fin 6 → ℂ) →ₗ[ℂ] (ℂ ⊗[ℚ] HQ Y 1))
    (hQ : ∀ t ∈ Submodule.span ℂ (Set.range (labeledInverseForm B hB hs r)),
      complexCupEquiv Y 2 (exteriorPower.map 2 f (InvariantsExterior.wedgeQuotient 2 t)) ∈
        (algebraicCycleClassSpan Y 1).baseChange ℂ)
    (hV : ∀ c : Fin (Module.finrank ℂ (Fin 6 → ℂ)) → Fin r,
      complexCupEquiv Y (Module.finrank ℂ (Fin 6 → ℂ))
        (exteriorPower.map _ f (InvariantsExterior.wedgeQuotient _ (labeledVolume r c))) ∈
          f1575EvenCohomologySpan (algebraicCycleClassSpan Y) (Module.finrank ℂ (Fin 6 → ℂ)))
    (n : ℕ) (t : ⨂[ℂ]^n (Fin r → Fin 6 → ℂ))
    (ht : t ∈ inverseFormVolumeProducts B hB hs r n) :
    complexCupEquiv Y n (exteriorPower.map n f (InvariantsExterior.wedgeQuotient n t)) ∈
      f1575EvenCohomologySpan (algebraicCycleClassSpan Y) n := by
  induction ht using Submodule.span_induction with
  | mem t ht =>
    obtain ⟨k, h, σ, a, c, ha, rfl⟩ := ht
    subst n
    rw [m3_wedgeQuotient_permRep, map_zsmul, map_zsmul]
    rw [← Int.cast_smul_eq_zsmul ℂ]
    apply Submodule.smul_mem
    rw [tensorCup_append]
    exact algebraic_even_span_cup Y rfl
      (tensor_quadratic_products_even Y f _ hQ k a ha) (hV c)
  | zero =>
    rw [map_zero, map_zero, map_zero]
    exact Submodule.zero_mem _
  | add a b ha hb hia hib =>
    rw [map_add, map_add, map_add]
    exact Submodule.add_mem _ hia hib
  | smul c a ha hia =>
    rw [map_smul, map_smul, map_smul]
    exact Submodule.smul_mem _ c hia

end HodgeLean.Foundations.Abdulali
