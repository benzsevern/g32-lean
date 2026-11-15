import HodgeLean.Foundations.Program.G32Native.EulerModel.NormalProjectiveChartTopology

/-! # The actual kernel total space over the normalized projective chart -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators
namespace HodgeLean.Foundations.Program.G32Native.EulerModel

/-- The kernel frame is jointly continuous in its actual base and fibre coordinates. -/
theorem continuous_normalKernelChart_vector (k : ℕ) :
    Continuous (fun za : (Fin k → ℂ) × (Fin k → ℂ) =>
      (normalKernelChart k za.1 za.2).1) := by
  simp_rw [normalKernelChart_val]
  fun_prop

#print axioms continuous_normalKernelChart_vector

/-- The actual part of the kernel total space over the specified projective affine chart. -/
abbrev NormalKernelChartDomain (k : ℕ) :=
  {v : ProjectiveNormalTotalSpace k // v.1.1 ∈ Set.range (normalProjectiveChart k)}

/-- The actual kernel vector and its base point in joint chart coordinates. -/
def normalKernelTotalChartForward (k : ℕ) :
    ((Fin k → ℂ) × (Fin k → ℂ)) → NormalKernelChartDomain k :=
  fun za => ⟨⟨(normalProjectiveChart k za.1, (normalKernelChart k za.1 za.2).1), by
    rw [projectiveNormalKernel_chart]
    exact (normalKernelChart k za.1 za.2).2⟩, ⟨za.1, rfl⟩⟩

/-- The full chart parameterization is continuous in the actual induced total-space topology. -/
theorem continuous_normalKernelTotalChartForward (k : ℕ) :
    Continuous (normalKernelTotalChartForward k) := by
  unfold normalKernelTotalChartForward
  apply Continuous.subtype_mk
  apply Continuous.subtype_mk
  exact ((continuous_normalProjectiveChart k).comp continuous_fst).prodMk
    (continuous_normalKernelChart_vector k)

#print axioms continuous_normalKernelTotalChartForward

/-- The actual affine base coordinates and the coefficients of the evaluation-kernel vector. -/
def normalKernelTotalChartInverse (k : ℕ) (v : NormalKernelChartDomain k) :
    (Fin k → ℂ) × (Fin k → ℂ) :=
  (normalProjectiveAffineCoordinate k v.1.1.1, v.1.1.2.2)

/-- Both coordinates of the actual total-space chart inverse are continuous. -/
theorem continuous_normalKernelTotalChartInverse (k : ℕ) :
    Continuous (normalKernelTotalChartInverse k) := by
  have hc : Continuous (fun v : NormalKernelChartDomain k => v.1.1) :=
    continuous_subtype_val.comp continuous_subtype_val
  have hb : Continuous (fun v : NormalKernelChartDomain k =>
      (⟨v.1.1.1, v.2⟩ : Set.range (normalProjectiveChart k))) :=
    (continuous_fst.comp hc).subtype_mk (fun v => v.2)
  exact ((continuous_normalProjectiveAffineCoordinate_on_chart k).comp hb).prodMk
    (continuous_snd.comp (continuous_snd.comp hc))

#print axioms continuous_normalKernelTotalChartInverse

/-- The tail coordinates reconstruct the entire actual vector in the normalized evaluation kernel. -/
theorem normalKernelChart_vector_tail (k : ℕ) (z : Fin k → ℂ) (a : ℂ × (Fin k → ℂ))
    (ha : a ∈ LinearMap.ker (normalEvaluation k z)) :
    (normalKernelChart k z a.2).1 = a := by
  rw [normalKernelChart_val]
  apply Prod.ext
  · have hker := ha
    rw [LinearMap.mem_ker, normalEvaluation_apply] at hker
    exact (eq_neg_iff_add_eq_zero.mpr hker).symm
  · rfl

#print axioms normalKernelChart_vector_tail

/-- The actual total-space chart inverse recovers both specified input coordinates. -/
theorem normalKernelTotalChart_left_inv (k : ℕ) (za : (Fin k → ℂ) × (Fin k → ℂ)) :
    normalKernelTotalChartInverse k (normalKernelTotalChartForward k za) = za := by
  apply Prod.ext
  · exact normalProjectiveAffineCoordinate_chart k za.1
  · rfl

#print axioms normalKernelTotalChart_left_inv
/-- The actual total-space chart reconstructs every vector over its specified base chart. -/
theorem normalKernelTotalChart_right_inv (k : ℕ) (v : NormalKernelChartDomain k) :
    normalKernelTotalChartForward k (normalKernelTotalChartInverse k v) = v := by
  obtain ⟨z, hz⟩ := v.2
  have hb : normalProjectiveChart k (normalProjectiveAffineCoordinate k v.1.1.1) = v.1.1.1 := by
    rw [← hz, normalProjectiveAffineCoordinate_chart]
  apply Subtype.ext
  apply Subtype.ext
  apply Prod.ext
  · exact hb
  · apply normalKernelChart_vector_tail
    change v.1.1.2 ∈ LinearMap.ker
      (normalEvaluation k (normalProjectiveAffineCoordinate k v.1.1.1))
    rw [← projectiveNormalKernel_chart, hb]
    exact v.1.2

#print axioms normalKernelTotalChart_right_inv
/-- The actual kernel total space over the first projective chart has its specified product coordinates. -/
def normalKernelTotalChartHomeomorph (k : ℕ) :
    ((Fin k → ℂ) × (Fin k → ℂ)) ≃ₜ NormalKernelChartDomain k where
  toFun := normalKernelTotalChartForward k
  invFun := normalKernelTotalChartInverse k
  left_inv := normalKernelTotalChart_left_inv k
  right_inv := normalKernelTotalChart_right_inv k
  continuous_toFun := continuous_normalKernelTotalChartForward k
  continuous_invFun := continuous_normalKernelTotalChartInverse k

#print axioms normalKernelTotalChartHomeomorph
/-- The specified total-space chart preserves the actual zero vectors exactly. -/
theorem normalKernelTotalChart_vector_zero_iff (k : ℕ)
    (za : (Fin k → ℂ) × (Fin k → ℂ)) :
    (normalKernelTotalChartForward k za).1.1.2 = 0 ↔ za.2 = 0 := by
  change (normalKernelChart k za.1 za.2).1 = 0 ↔ za.2 = 0
  constructor
  · intro h
    exact congrArg Prod.snd h
  · intro h
    rw [h, map_zero]
    rfl

#print axioms normalKernelTotalChart_vector_zero_iff
/-- The specified kernel total-space chart is an actual open neighborhood in the global model. -/
theorem isOpen_normalKernelChartDomain (k : ℕ) :
    IsOpen {v : ProjectiveNormalTotalSpace k |
      v.1.1 ∈ Set.range (normalProjectiveChart k)} :=
  (isOpen_normalProjectiveChart_range k).preimage
    (continuous_fst.comp continuous_subtype_val)

#print axioms isOpen_normalKernelChartDomain
end HodgeLean.Foundations.Program.G32Native.EulerModel
