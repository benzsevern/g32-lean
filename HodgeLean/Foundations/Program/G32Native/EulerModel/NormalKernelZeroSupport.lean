import HodgeLean.Foundations.Program.G32Native.EulerModel.NormalSectionHomotopy

/-! # The literal zero-section support in the original kernel total space -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
namespace HodgeLean.Foundations.Program.G32Native.EulerModel

/-- The actual global kernel zero vectors form a closed support in the original total space. -/
theorem isClosed_normalKernelZeroSection (k : ℕ) :
    IsClosed {v : ProjectiveNormalTotalSpace k | v.1.2 = 0} :=
  isClosed_singleton.preimage (continuous_snd.comp continuous_subtype_val)

#print axioms isClosed_normalKernelZeroSection
/-- The actual global zero-section image is precisely the same literal zero-vector support. -/
theorem projectiveNormalZeroSection_range (k : ℕ) :
    Set.range (projectiveNormalZeroSection k) =
      {v : ProjectiveNormalTotalSpace k | v.1.2 = 0} := by
  ext v
  constructor
  · rintro ⟨p, rfl⟩
    rfl
  · intro hv
    refine ⟨v.1.1, ?_⟩
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · exact hv.symm

#print axioms projectiveNormalZeroSection_range
/-- The actual global zero section is a closed embedding into the original kernel total space. -/
theorem isClosedEmbedding_projectiveNormalZeroSection (k : ℕ) :
    Topology.IsClosedEmbedding (projectiveNormalZeroSection k) := by
  have h : Function.LeftInverse (fun v : ProjectiveNormalTotalSpace k => v.1.1)
      (projectiveNormalZeroSection k) := fun _ => rfl
  exact
    { toIsEmbedding := h.isEmbedding (continuous_fst.comp continuous_subtype_val)
        (projectiveNormalZeroSection k).continuous
      isClosed_range := by
        rw [projectiveNormalZeroSection_range]
        exact isClosed_normalKernelZeroSection k }

#print axioms isClosedEmbedding_projectiveNormalZeroSection
end HodgeLean.Foundations.Program.G32Native.EulerModel
