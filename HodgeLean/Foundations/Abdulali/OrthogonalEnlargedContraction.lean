import HodgeLean.Foundations.Abdulali.OrthogonalBaseContraction
import HodgeLean.Foundations.Abdulali.MixedCopyLabels
import HodgeLean.Foundations.Abdulali.MixedCopyZero
import HodgeLean.Foundations.Program.MilneTensorCopyFixed

noncomputable section
open scoped TensorProduct
open HodgeLean.Foundations HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.Abdulali
variable {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

/-- Each copy component of an enlarged orthogonal fixed tensor has the required contraction. -/
theorem orthogonal_enlarged_labeled_contraction_mem
    (B : LinearMap.BilinForm ℂ V) (hB : B.Nondegenerate)
    (hs : ∀ x y, B x y = B y x) (r n : ℕ)
    (c : Fin (n + Module.finrank ℂ V) → Fin (r + 1))
    (t : ⨂[ℂ]^(n + Module.finrank ℂ V) V)
    (ht : t ∈ m1b_fixed (m1b_isometries B) (n + Module.finrank ℂ V)) :
    mixedTensorContraction r n (Module.finrank ℂ V) normalizedVolumeCovector
      (m1b_copyTensorIn (r + 1) (n + Module.finrank ℂ V) c t) ∈
      orthogonalVolumeProducts B r n := by
  classical
  by_cases h0 : ∃ i : Fin n, c (Fin.castAdd (Module.finrank ℂ V) i) = 0
  · obtain ⟨i, hi⟩ := h0
    rw [mixedTensorContraction_copyTensorIn_eq_zero_of_original _ _ _ _ c i hi]
    exact Submodule.zero_mem _
  by_cases h1 : ∃ j : Fin (Module.finrank ℂ V), c (Fin.natAdd n j) ≠ 0
  · obtain ⟨j, hj⟩ := h1
    rw [mixedTensorContraction_copyTensorIn_eq_zero_of_extra _ _ _ _ c j hj]
    exact Submodule.zero_mem _
  have hsucc (x : Fin (r + 1)) : x ≠ 0 → ∃ a : Fin r, x = a.succ := by
    refine Fin.cases ?_ (fun a _ => ⟨a, rfl⟩) x
    intro h
    exact False.elim (h rfl)
  have halabel (i : Fin n) : ∃ a : Fin r, c (Fin.castAdd (Module.finrank ℂ V) i) = a.succ :=
    hsucc _ (fun hi => h0 ⟨i, hi⟩)
  choose a ha using halabel
  have he (j : Fin (Module.finrank ℂ V)) : c (Fin.natAdd n j) = 0 := by
    by_contra hj
    exact h1 ⟨j, hj⟩
  rw [mixedTensorContraction_copyTensorIn_compatible _ _ _ _ c a ha he]
  exact orthogonal_base_contraction_copy_mem B hB hs r n a t ht

/-- The enlarged full orthogonal fixed subspace contracts into the required volume products. -/
theorem orthogonal_enlarged_fixed_contraction_le_volumeProducts
    (B : LinearMap.BilinForm ℂ V) (hB : B.Nondegenerate)
    (hs : ∀ x y, B x y = B y x) (r n : ℕ) :
    (m1b_fixed (m1b_copies (r + 1) '' m1b_isometries B)
      (n + Module.finrank ℂ V)).map
        (mixedTensorContraction r n (Module.finrank ℂ V) normalizedVolumeCovector) ≤
      orthogonalVolumeProducts B r n := by
  rintro t ⟨z, hz, rfl⟩
  rw [← m1b_sum_copyTensorIn_out (r + 1) (n + Module.finrank ℂ V) z, map_sum]
  apply Submodule.sum_mem
  intro c _
  exact orthogonal_enlarged_labeled_contraction_mem B hB hs r n c _
    (m1b_copyTensorOut_fixed (m1b_isometries B) (r + 1)
      (n + Module.finrank ℂ V) c z hz)

end HodgeLean.Foundations.Abdulali
