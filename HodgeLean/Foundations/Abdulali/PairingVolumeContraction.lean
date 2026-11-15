import HodgeLean.Foundations.Abdulali.OrthogonalEnlargedContraction

noncomputable section
open scoped TensorProduct
open HodgeLean.Foundations HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.Abdulali
variable {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

/-- Contracting a full-orthogonal invariant with a top alternating covector gives
a sum of permuted quadratic products times independently labeled volumes.
The intended calculation embeds the mixed tensor in `r + 1` standard copies,
applies the full orthogonal FFT, and contracts the pairing products. A pairing
between two contracted slots vanishes; the other pairings yield a determinant.
Source: Weyl, The Classical Groups, Chapter II, §§9 and 17; Procesi, Lie Groups,
Chapter 11, §§2–3, contraction of pairing diagrams with an alternating volume. -/
theorem orthogonal_pairing_volume_contraction_aux
    (B : LinearMap.BilinForm ℂ V) (hB : B.Nondegenerate)
    (hs : ∀ x y, B x y = B y x) (r n : ℕ) :
    let C : (⨂[ℂ]^n (Fin r → V)) ⊗[ℂ] (⨂[ℂ]^(Module.finrank ℂ V) V) →ₗ[ℂ]
        (⨂[ℂ]^n (Fin r → V)) :=
      (TensorProduct.rid ℂ _).toLinearMap.comp
        (TensorProduct.map LinearMap.id normalizedVolumeCovector)
    (⨅ g : orthogonalUnits B,
      LinearMap.ker (TensorProduct.map (orthogonalTensorRepresentation B r n g)
        (orthogonalBaseTensorRepresentation B (Module.finrank ℂ V) g) - LinearMap.id)).map C ≤
      orthogonalVolumeProducts B r n := by
  dsimp only
  refine (mixed_fixed_contraction_le_products B hB hs r n
    (Module.finrank ℂ V) normalizedVolumeCovector).trans ?_
  rw [← m1b_orthogonal_tensors_aux V B hB hs (r + 1) (n + Module.finrank ℂ V)]
  exact orthogonal_enlarged_fixed_contraction_le_volumeProducts B hB hs r n

/-- The determinant-character sector is spanned by one volume and quadratic
products. The invariant-lift equality reduces it to the pairing contraction.
Source: Weyl, The Classical Groups, Chapter II, §§9 and 17. -/
theorem orthogonal_determinant_sector_le_volumeProducts
    (B : LinearMap.BilinForm ℂ V) (hB : B.Nondegenerate)
    (hs : ∀ x y, B x y = B y x) (r n : ℕ) :
    (⨅ g : orthogonalUnits B,
      LinearMap.ker (orthogonalTensorRepresentation B r n g -
        orthogonalDeterminant B g • LinearMap.id)) ≤ orthogonalVolumeProducts B r n := by
  rw [← orthogonal_determinant_sector_eq_contracted_fixed B hB r n]
  exact orthogonal_pairing_volume_contraction_aux B hB hs r n

end HodgeLean.Foundations.Abdulali
