import HodgeLean.Foundations.Program.SchoenTransferDefs

/-! Linear extension of the retained finite family. -/

noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- A spanning family controls the image of a submodule under the specified
linear map; no change of generators or comparison map is needed. -/
theorem s4_q3_map_le_of_spanning_family
    {V E : Type*} [AddCommGroup V] [Module ℚ V]
    [AddCommGroup E] [Module ℚ E] {ι : Type*}
    (b : ι → V) (K : Submodule ℚ V)
    (hb : Submodule.span ℚ (Set.range b) = K)
    (P : V →ₗ[ℚ] E) (C : Submodule ℚ E)
    (h : ∀ i, P (b i) ∈ C) : K.map P ≤ C := by
  apply Submodule.map_le_iff_le_comap.mpr
  rw [← hb]
  apply Submodule.span_le.mpr
  rintro _ ⟨i, rfl⟩
  exact h i

end HodgeLean.Foundations.Program
