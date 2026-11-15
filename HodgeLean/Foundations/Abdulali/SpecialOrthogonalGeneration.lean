import HodgeLean.Foundations.Abdulali.PairingVolumeContraction
import HodgeLean.Foundations.Abdulali.InverseFormGenerators

noncomputable section
open scoped TensorProduct
open HodgeLean.Foundations HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.Abdulali
variable {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

/-- Permuted products of explicitly labeled inverse-form tensors and one volume.
All labels are independent, and the quadratic product may be the scalar unit.
Source: Weyl, The Classical Groups, Chapter II, §§9 and 17. -/
def inverseFormVolumeProducts (B : LinearMap.BilinForm ℂ V) (hB : B.Nondegenerate)
    (hs : ∀ x y, B x y = B y x) (r n : ℕ) :
    Submodule ℂ (⨂[ℂ]^n (Fin r → V)) :=
  Submodule.span ℂ {t | ∃ (k : ℕ) (h : k + Module.finrank ℂ V = n)
      (σ : Equiv.Perm (Fin (k + Module.finrank ℂ V)))
      (a : ⨂[ℂ]^k (Fin r → V)) (c : Fin (Module.finrank ℂ V) → Fin r),
      a ∈ m1b_products (Submodule.span ℂ (Set.range (labeledInverseForm B hB hs r))) k ∧
      t = h ▸ SchurWeyl.permRep ℂ (Fin r → V) _ σ
        (InvariantsExterior.tensorAppend k (Module.finrank ℂ V)
          (a ⊗ₜ[ℂ] labeledVolume r c))}

/-- Replacing the entire quadratic fixed space by the explicit inverse-form
family preserves the single-volume product span.
Source: Weyl, The Classical Groups, Chapter II, §§9 and 17. -/
theorem orthogonalVolumeProducts_eq_inverseFormVolumeProducts
    (B : LinearMap.BilinForm ℂ V) (hB : B.Nondegenerate)
    (hs : ∀ x y, B x y = B y x) (r n : ℕ) :
    orthogonalVolumeProducts B r n = inverseFormVolumeProducts B hB hs r n := by
  unfold orthogonalVolumeProducts inverseFormVolumeProducts
  rw [orthogonal_quadratics_eq_inverseForm_span B hB hs r]

/-- Special orthogonal tensor invariants on any number of standard copies are
spanned by permuted inverse-form products and products with a labeled volume.
The tensor degree and the dimension may both be zero. Two volume factors reduce
to quadratic products, so one volume per product suffices.
Source: Weyl, The Classical Groups, Chapter II, §§9 and 17; Procesi, Lie Groups,
Chapter 11, §§2–3. -/
theorem special_orthogonal_tensor_generation
    (B : LinearMap.BilinForm ℂ V) (hB : B.Nondegenerate)
    (hs : ∀ x y, B x y = B y x) (r n : ℕ) :
    m1b_fixed (m1b_copies r '' {u ∈ m1b_isometries B | LinearMap.det u = 1}) n =
      m1b_products (Submodule.span ℂ (Set.range (labeledInverseForm B hB hs r))) n ⊔
        inverseFormVolumeProducts B hB hs r n := by
  have h := (special_orthogonal_generation_iff_character_spanning B hB hs r n).mpr
    ((orthogonal_determinant_sector_le_volumeProducts B hB hs r n).trans le_sup_right)
  rw [orthogonal_quadratics_eq_inverseForm_span B hB hs r,
    orthogonalVolumeProducts_eq_inverseFormVolumeProducts B hB hs r n] at h
  exact h

end HodgeLean.Foundations.Abdulali
