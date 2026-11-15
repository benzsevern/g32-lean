import HodgeLean.Foundations.Program.MilneTensorFormOrbit

noncomputable section
namespace HodgeLean.Foundations.Program
variable {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

theorem m1b_alternating_standard_coordinates (B : LinearMap.BilinForm ℂ V)
    (hB : B.Nondegenerate) (ha : ∀ x, B x x = 0) :
    ∃ (k : ℕ) (e : V ≃ₗ[ℂ] (Fin k ⊕ Fin k → ℂ)),
      B.compl₁₂ e.symm.toLinearMap e.symm.toLinearMap = (m1b_J k).toBilin' := by
  classical
  obtain ⟨k, b, _, hb⟩ := m1b_alternating_abstract_basis B hB ha
  refine ⟨k, b.equivFun, ?_⟩
  apply (Pi.basisFun ℂ (Fin k ⊕ Fin k)).ext
  intro i
  apply (Pi.basisFun ℂ (Fin k ⊕ Fin k)).ext
  intro j
  simpa [LinearMap.compl₁₂_apply, Module.Basis.equivFun_symm_apply,
    Matrix.toBilin'_single] using hb i j

end HodgeLean.Foundations.Program
