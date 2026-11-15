import HodgeLean.Foundations.Program.G32Native.NormalEvaluationTopology

/-! # Continuous identification transport on the retained component -/
noncomputable section
set_option maxHeartbeats 200000
open CategoryTheory AlgebraicGeometry Bundle
namespace HodgeLean.Foundations.Program.G32Native

/-- Actual conormal transport is a homeomorphism of normal total spaces.
Source: Hartshorne, Algebraic Geometry, II.5 and II.8, local-section evaluation topology. -/
def normalTransportHomeomorph {Q : Over (Spec ↧ℂ)} {M N : Q.left.Modules}
    (E : M ≅ N) (k : ℕ) :
    @Homeomorph (TotalSpace (Fin k → ℂ) (normalFibreOfModule M))
      (TotalSpace (Fin k → ℂ) (normalFibreOfModule N))
      (normalEvaluationTopology M k) (normalEvaluationTopology N k) := by
  letI := normalEvaluationTopology M k
  letI := normalEvaluationTopology N k
  exact {
    toFun z := ⟨z.proj, normalFibreTransport E z.proj z.2⟩
    invFun z := ⟨z.proj, normalFibreTransport E.symm z.proj z.2⟩
    left_inv z := by
      apply TotalSpace.ext
      · rfl
      · apply heq_of_eq
        change normalFibreTransport E.symm z.proj (normalFibreTransport E z.proj z.2) = z.2
        exact (normalFibreTransport E z.proj).symm_apply_apply z.2
    right_inv z := by
      apply TotalSpace.ext
      · rfl
      · apply heq_of_eq
        change normalFibreTransport E z.proj (normalFibreTransport E.symm z.proj z.2) = z.2
        exact (normalFibreTransport E z.proj).apply_symm_apply z.2
    continuous_toFun := normalFibreTransport_continuous E k
    continuous_invFun := normalFibreTransport_continuous E.symm k
  }

/-- Transport retains the exact component point. -/
theorem normalTransportHomeomorph_proj {Q : Over (Spec ↧ℂ)} {M N : Q.left.Modules}
    (E : M ≅ N) (k : ℕ) (z : TotalSpace (Fin k → ℂ) (normalFibreOfModule M)) :
    (normalTransportHomeomorph E k z).proj = z.proj := rfl

/-- A supplied identification into the same model composes with actual normal transport.
Source: Hartshorne, Algebraic Geometry, II.5 and II.8, composition of normal identifications. -/
def transportNormalIdentification {Q : Over (Spec ↧ℂ)} {M N : Q.left.Modules}
    (E : M ≅ N) (k : ℕ) {T : Type*} [TopologicalSpace T]
    (producer : @Homeomorph (TotalSpace (Fin k → ℂ) (normalFibreOfModule N)) T
      (normalEvaluationTopology N k) inferInstance) :
    @Homeomorph (TotalSpace (Fin k → ℂ) (normalFibreOfModule M)) T
      (normalEvaluationTopology M k) inferInstance := by
  letI := normalEvaluationTopology M k
  letI := normalEvaluationTopology N k
  exact (normalTransportHomeomorph E k).trans producer

/-- The transported identification uses the producer's value on the retained normal vector. -/
theorem transportNormalIdentification_apply {Q : Over (Spec ↧ℂ)} {M N : Q.left.Modules}
    (E : M ≅ N) (k : ℕ) {T : Type*} [TopologicalSpace T]
    (producer : @Homeomorph (TotalSpace (Fin k → ℂ) (normalFibreOfModule N)) T
      (normalEvaluationTopology N k) inferInstance)
    (z : TotalSpace (Fin k → ℂ) (normalFibreOfModule M)) :
    transportNormalIdentification E k producer z =
      producer ⟨z.proj, normalFibreTransport E z.proj z.2⟩ := rfl

#print axioms normalTransportHomeomorph
#print axioms normalTransportHomeomorph_proj
#print axioms transportNormalIdentification
#print axioms transportNormalIdentification_apply
end HodgeLean.Foundations.Program.G32Native
