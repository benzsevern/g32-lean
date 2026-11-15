import HodgeLean.Foundations.Program.G32Native.CoefficientKernelFibreEquiv
import Mathlib.Data.Subtype

/-! # The coefficient evaluation topology and the original kernel topology -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry Bundle
open HodgeLean.Foundations.Program
open HodgeLean.Foundations.Program.G32Native.EulerModel
namespace HodgeLean.Foundations.Program.G32Native

/-- The specified component point in the ordered projective model. -/
def coefficientBaseHomeomorph (G : CanonicalAbelGeometry) :
    ComplexPoint G.Q ≃ₜ Projectivization ℂ (ℂ × (Fin G.k → ℂ)) :=
  (Point.isoMapHomeomorph G.eQ).trans (normalProjectiveSchemeHomeomorph G.k).symm

/-- Recover the original covector from a kernel vector over the specified base point. -/
def coefficientKernelTotalInverse (G : CanonicalAbelGeometry)
    (v : ProjectiveNormalTotalSpace G.k) :
    TotalSpace (Fin G.k → ℂ)
      (fun x => (g32n_homogeneousLine G.k G.eQ x).submodule.dualAnnihilator) :=
  ⟨(coefficientBaseHomeomorph G).symm v.1.1,
    ⟨(coefficientModelCoordinates G.k).symm v.1.2, by
      rw [coefficient_line_model]
      change _ ∈ (s2e_projectiveLinearEquiv (normalHomogeneousCoordinates G.k)
        (coefficientBaseHomeomorph G ((coefficientBaseHomeomorph G).symm v.1.1))).submodule.dualAnnihilator
      rw [Homeomorph.apply_symm_apply]
      apply (coefficient_mem_projectiveKernel_iff G.k v.1.1 _).mp
      rw [← coefficientModelCoordinates_apply, LinearEquiv.apply_symm_apply]
      exact v.2⟩⟩

/-- The inverse recovers each original point and covector. -/
theorem coefficientKernelTotalInverse_left (G : CanonicalAbelGeometry)
    (z : TotalSpace (Fin G.k → ℂ)
      (fun x => (g32n_homogeneousLine G.k G.eQ x).submodule.dualAnnihilator)) :
    coefficientKernelTotalInverse G (coefficientKernelTotalMap G z) = z := by
  apply TotalSpace.ext
  · exact (coefficientBaseHomeomorph G).symm_apply_apply z.proj
  · apply (Subtype.heq_iff_coe_eq (fun a => by
      change a ∈ (g32n_homogeneousLine G.k G.eQ
        ((coefficientBaseHomeomorph G).symm (coefficientBaseHomeomorph G z.proj))).submodule.dualAnnihilator ↔ _
      rw [Homeomorph.symm_apply_apply])).mpr
    change (coefficientModelCoordinates G.k).symm
      (z.2.1 (Pi.single 0 1), fun i => z.2.1 (Pi.single i.succ 1)) = z.2.1
    rw [← coefficientModelCoordinates_apply, LinearEquiv.symm_apply_apply]

/-- The reconstructed covector gives back the entire specified kernel vector. -/
theorem coefficientKernelTotalInverse_right (G : CanonicalAbelGeometry)
    (v : ProjectiveNormalTotalSpace G.k) :
    coefficientKernelTotalMap G (coefficientKernelTotalInverse G v) = v := by
  apply Subtype.ext
  apply Prod.ext
  · exact (coefficientBaseHomeomorph G).apply_symm_apply v.1.1
  · change ((coefficientModelCoordinates G.k).symm v.1.2 (Pi.single 0 1),
      fun i => (coefficientModelCoordinates G.k).symm v.1.2 (Pi.single i.succ 1)) = v.1.2
    rw [← coefficientModelCoordinates_apply, LinearEquiv.apply_symm_apply]

/-- The inverse is continuous in every original homogeneous evaluation. -/
theorem continuous_coefficientKernelTotalInverse (G : CanonicalAbelGeometry) :
    @Continuous _ _ inferInstance (coefficientTotalTopology G)
      (coefficientKernelTotalInverse G) := by
  apply (continuous_coefficientTotal_iff G _).mpr
  constructor
  · exact (coefficientBaseHomeomorph G).symm.continuous.comp
      (continuous_fst.comp continuous_subtype_val)
  · intro a
    exact (((Module.Dual.eval ℂ (Fin (G.k + 1) → ℂ) a).comp
      (coefficientModelCoordinates G.k).symm.toLinearMap).continuous_of_finiteDimensional).comp
        (continuous_snd.comp continuous_subtype_val)

/-- The evaluation-topology coefficient family is homeomorphic to the original model family. -/
def coefficientKernelTotalHomeomorph (G : CanonicalAbelGeometry) :
    @Homeomorph (TotalSpace (Fin G.k → ℂ)
      (fun x => (g32n_homogeneousLine G.k G.eQ x).submodule.dualAnnihilator))
      (ProjectiveNormalTotalSpace G.k) (coefficientTotalTopology G) inferInstance := by
  letI := coefficientTotalTopology G
  exact {
  toFun := coefficientKernelTotalMap G
  invFun := coefficientKernelTotalInverse G
  left_inv := coefficientKernelTotalInverse_left G
  right_inv := coefficientKernelTotalInverse_right G
  continuous_toFun := continuous_coefficientKernelTotalMap G
  continuous_invFun := continuous_coefficientKernelTotalInverse G }

end HodgeLean.Foundations.Program.G32Native
