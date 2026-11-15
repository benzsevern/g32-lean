import HodgeLean.Foundations.Abdulali.TensorVolumeAlgebraicity

noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open scoped CategoryTheory.MonObj TensorProduct
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Foundations
open HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.Abdulali
attribute [local irreducible] cupProductOf algebraicCycleClassSpan complexCupEquiv

/-- Algebraicity of the two explicit generator families implies algebraicity of
all SO-fixed tensors after alternating cup comparison.
Source: Weyl, The Classical Groups, II.9 and II.17; Fulton, Corollary 19.2. -/
theorem orthogonal_tensor_images_algebraic
    (Y : Over (Spec ↧ℂ)) [GrpObj Y] [IsCommMonObj Y]
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (r : ℕ) (B : LinearMap.BilinForm ℂ (Fin 6 → ℂ)) (hB : B.Nondegenerate)
    (hs : ∀ x y, B x y = B y x)
    (f : (Fin r → Fin 6 → ℂ) →ₗ[ℂ] (ℂ ⊗[ℚ] HQ Y 1))
    (hQ : ∀ t ∈ Submodule.span ℂ (Set.range (labeledInverseForm B hB hs r)),
      complexCupEquiv Y 2 (exteriorPower.map 2 f (InvariantsExterior.wedgeQuotient 2 t)) ∈
        (algebraicCycleClassSpan Y 1).baseChange ℂ)
    (hV : ∀ c : Fin (Module.finrank ℂ (Fin 6 → ℂ)) → Fin r,
      complexCupEquiv Y (Module.finrank ℂ (Fin 6 → ℂ))
        (exteriorPower.map _ f (InvariantsExterior.wedgeQuotient _ (labeledVolume r c))) ∈
          f1575EvenCohomologySpan (algebraicCycleClassSpan Y) (Module.finrank ℂ (Fin 6 → ℂ)))
    (p : ℕ) (t : ⨂[ℂ]^(2*p) (Fin r → Fin 6 → ℂ))
    (ht : t ∈ m1b_fixed (m1b_copies r '' {u ∈ m1b_isometries B | u.det = 1}) (2*p)) :
    complexCupEquiv Y (2*p) (exteriorPower.map (2*p) f
      (InvariantsExterior.wedgeQuotient (2*p) t)) ∈
        (algebraicCycleClassSpan Y p).baseChange ℂ := by
  rw [special_orthogonal_tensor_generation B hB hs r (2*p)] at ht
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp ht
  rw [map_add, map_add, map_add]
  apply Submodule.add_mem
  · exact tensor_quadratic_products_algebraic Y f _ hQ p a ha
  · have h := tensor_volume_products_algebraic Y r B hB hs f hQ hV (2*p) b hb
    erw [f1575EvenCohomologySpan_even] at h
    exact h

end HodgeLean.Foundations.Abdulali
