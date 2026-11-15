import HodgeLean.Foundations.Program.MilneTensorOrbit

noncomputable section
namespace HodgeLean.Foundations.Program
variable {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

theorem m1b_symmetric_standard_coordinates (B : LinearMap.BilinForm ℂ V)
    (hB : B.Nondegenerate) (hs : ∀ x y, B x y = B y x) :
    ∃ e : V ≃ₗ[ℂ] (Fin (Module.finrank ℂ V) → ℂ),
      B.compl₁₂ e.symm.toLinearMap e.symm.toLinearMap =
        (1 : Matrix (Fin (Module.finrank ℂ V)) (Fin (Module.finrank ℂ V)) ℂ).toBilin' := by
  let b := Module.finBasis ℂ V
  let C := B.compl₁₂ b.equivFun.symm.toLinearMap b.equivFun.symm.toLinearMap
  have hC : C.Nondegenerate := m1b_nondegenerate_transport b.equivFun B hB
  have hsC : ∀ x y, C x y = C y x := fun x y => hs _ _
  have hI : (1 : Matrix (Fin (Module.finrank ℂ V)) (Fin (Module.finrank ℂ V)) ℂ).toBilin'.Nondegenerate :=
    LinearMap.BilinForm.nondegenerate_toBilin'_iff_det_ne_zero.mpr (by simp)
  obtain ⟨d, hd⟩ := m1b_symmetric_forms_same_orbit C _ hC hI hsC
    (Matrix.isSymm_toBilin'_iff_isSymm.mpr (by simp)).eq
  exact ⟨b.equivFun.trans d, hd⟩

end HodgeLean.Foundations.Program
