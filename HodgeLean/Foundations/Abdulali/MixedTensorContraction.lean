import HodgeLean.Foundations.Abdulali.MixedTensorEquivariance

noncomputable section
open scoped TensorProduct
open HodgeLean.Foundations HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.Abdulali
variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- Contract the recovered extra block by an arbitrary covector. -/
def mixedTensorContraction (r n d : ℕ) (ℓ : (⨂[ℂ]^d V) →ₗ[ℂ] ℂ) :
    (⨂[ℂ]^(n + d) (Fin (r + 1) → V)) →ₗ[ℂ] (⨂[ℂ]^n (Fin r → V)) :=
  ((TensorProduct.rid ℂ _).toLinearMap.comp (TensorProduct.map LinearMap.id ℓ)).comp
    (mixedTensorOut r n d)

/-- The enlarged-space contraction agrees with contraction of the original mixed tensor. -/
theorem mixedTensorContraction_in (r n d : ℕ) (ℓ : (⨂[ℂ]^d V) →ₗ[ℂ] ℂ)
    (z : (⨂[ℂ]^n (Fin r → V)) ⊗[ℂ] (⨂[ℂ]^d V)) :
    mixedTensorContraction r n d ℓ (mixedTensorIn r n d z) =
      (TensorProduct.rid ℂ _) (TensorProduct.map LinearMap.id ℓ z) := by
  simp only [mixedTensorContraction, LinearMap.comp_apply, mixedTensorOut_in,
    LinearEquiv.coe_coe]

/-- The full orthogonal FFT reduces mixed fixed-tensor contraction to quadratic products. -/
theorem mixed_fixed_contraction_le_products [FiniteDimensional ℂ V]
    (B : LinearMap.BilinForm ℂ V) (hB : B.Nondegenerate)
    (hs : ∀ x y, B x y = B y x) (r n d : ℕ)
    (ℓ : (⨂[ℂ]^d V) →ₗ[ℂ] ℂ) :
    (⨅ g : orthogonalUnits B,
      LinearMap.ker (TensorProduct.map (orthogonalTensorRepresentation B r n g)
        (orthogonalBaseTensorRepresentation B d g) - LinearMap.id)).map
      ((TensorProduct.rid ℂ _).toLinearMap.comp (TensorProduct.map LinearMap.id ℓ)) ≤
    (m1b_products (m1b_fixed (m1b_copies (r + 1) '' m1b_isometries B) 2)
      (n + d)).map (mixedTensorContraction r n d ℓ) := by
  rintro t ⟨z, hz, rfl⟩
  exact Submodule.mem_map.mpr ⟨mixedTensorIn r n d z,
    mixedTensorIn_mem_products B hB hs r n d z hz, mixedTensorContraction_in r n d ℓ z⟩

end HodgeLean.Foundations.Abdulali
