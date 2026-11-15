import HodgeLean.Foundations.HodgeGroupDualityGroups

/-! From the equality on the dual representation to the cohomological Lie hypothesis. -/

noncomputable section
namespace HodgeLean.Foundations
open scoped TensorProduct
variable {V : Type*} [AddCommGroup V] [Module ℚ V] {n : ℕ}

/-- A nondegenerate rational form has an invertible complex Gram matrix. -/
theorem g2_isUnit_complexGram (b : Module.Basis (Fin n) ℚ V)
    (E : LinearMap.BilinForm ℚ V) (hE : E.Nondegenerate) :
    IsUnit ((LinearMap.BilinForm.toMatrix b E).map (algebraMap ℚ ℂ)).det := by
  change IsUnit ((algebraMap ℚ ℂ).mapMatrix (LinearMap.BilinForm.toMatrix b E)).det
  rw [← RingHom.map_det]
  exact ((isUnit_iff_ne_zero.mpr
    ((LinearMap.BilinForm.nondegenerate_iff_det_ne_zero b).mp hE)).map (algebraMap ℚ ℂ))

/-- The dual special-unitary group is the inverse-transpose image of the cohomological group. -/
theorem g2_contragredient_gkGroup (b : Module.Basis (Fin n) ℚ V)
    (E : LinearMap.BilinForm ℚ V) (R : Subalgebra ℚ (Module.End ℚ V))
    (J : Module.End ℚ V) {d : ℚ} (hd : 0 < d)
    (hJ : J * J = (-d) • (1 : Module.End ℚ V)) (hE : E.Nondegenerate) :
    g2_contragredient '' g2_gkGroup b E R J d =
      g2_homologySpecialUnitary b E R J d := by
  have hG := g2_isRatAlgSubgroup_gkGroup b E R J hd hJ
  have hΩ := g2_isUnit_complexGram b E hE
  ext g
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (g2_transpose_mem_homologySpecialUnitary_iff b E R J hd hJ hΩ (x⁻¹)).mpr
      ((g2_mem_inverse_iff hG x).mpr hx)
  · intro hg
    refine ⟨g2_contragredient g, ?_, g2_contragredient_twice g⟩
    have ht : g2_dualTranspose (g⁻¹) ∈ g2_gkGroup b E R J d := by
      apply (g2_mem_inverse_iff hG (g2_dualTranspose g)).mpr
      apply (g2_transpose_mem_homologySpecialUnitary_iff b E R J hd hJ hΩ
        (g2_dualTranspose g)).mp
      simpa only [g2_dualTranspose_twice] using hg
    exact ht

/-- Equality of the homological groups implies equality of their cohomological counterparts. -/
theorem g2_cohomology_group_eq_of_homology_group_eq
    (H : ℤ × ℤ → Submodule ℂ (ℂ ⊗[ℚ] V)) (hH : DirectSum.IsInternal H)
    (b : Module.Basis (Fin n) ℚ V) (E : LinearMap.BilinForm ℚ V)
    (R : Subalgebra ℚ (Module.End ℚ V)) (J : Module.End ℚ V)
    {d : ℚ} (hd : 0 < d) (hJ : J * J = (-d) • (1 : Module.End ℚ V))
    (hE : E.Nondegenerate)
    (h : g2_homologyHodgeGroup H hH b = g2_homologySpecialUnitary b E R J d) :
    g2_hodgeGroup H hH b = g2_gkGroup b E R J d := by
  apply Set.image_injective.mpr (g2_contragredient.injective)
  exact (g2_contragredient_hodgeGroup H hH b).trans
    (h.trans (g2_contragredient_gkGroup b E R J hd hJ hE).symm)

/-- The homological group hypothesis supplies the cohomological Lie hypothesis. -/
theorem g2_hodgeLieIsGk_of_homology_group_eq
    (H : ℤ × ℤ → Submodule ℂ (ℂ ⊗[ℚ] V)) (hH : DirectSum.IsInternal H)
    (b : Module.Basis (Fin n) ℚ V) (E : LinearMap.BilinForm ℚ V)
    (R : Subalgebra ℚ (Module.End ℚ V)) (J : Module.End ℚ V)
    {d : ℚ} (hd : 0 < d) (hJ : J * J = (-d) • (1 : Module.End ℚ V))
    (hE : E.Nondegenerate)
    (h : g2_homologyHodgeGroup H hH b = g2_homologySpecialUnitary b E R J d) :
    HodgeLieIsGk H hH E R J :=
  g2_hodgeLieIsGk_of_eq H hH b E R J hd hJ
    (g2_cohomology_group_eq_of_homology_group_eq H hH b E R J hd hJ hE h)

end HodgeLean.Foundations
