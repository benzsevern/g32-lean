import HodgeLean.Foundations.Program.SchoenRescaledGrading

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- Rescaling retains the actual homogeneous projection at each selected degree. -/
theorem s2_rescaled_projection {A : Type} [CommRing A]
    (𝒜 : ℕ → AddSubgroup A) [GradedRing 𝒜] (D : ℕ) (hD : 0 < D)
    [GradedRing (fun n => 𝒜 (D * n))] (n : ℕ) :
    GradedRing.proj 𝒜 (D * n) = GradedRing.proj (fun j => 𝒜 (D * j)) n := by
  let ℬ := fun j => 𝒜 (D * j)
  have hcomp : (GradedRing.proj 𝒜 (D * n)).comp (DirectSum.coeAddMonoidHom ℬ) =
      (GradedRing.proj ℬ n).comp (DirectSum.coeAddMonoidHom ℬ) := by
    apply DirectSum.addHom_ext
    intro i a
    simp only [AddMonoidHom.comp_apply, DirectSum.coeAddMonoidHom_of, GradedRing.proj_apply]
    by_cases h : i = n
    · subst i
      rw [DirectSum.decompose_of_mem_same 𝒜 a.property,
        DirectSum.decompose_of_mem_same ℬ a.property]
    · rw [DirectSum.decompose_of_mem_ne 𝒜 a.property
        (fun h' => h (Nat.eq_of_mul_eq_mul_left hD h')),
        DirectSum.decompose_of_mem_ne ℬ a.property h]
  apply AddMonoidHom.ext
  intro a
  obtain ⟨b, rfl⟩ := (DirectSum.Decomposition.isInternal ℬ).surjective a
  exact DFunLike.congr_fun hcomp b

/-- A ring carrying the rescaled grading has zero original projections outside degree multiples. -/
theorem s2_rescaled_outside_projection {A : Type} [CommRing A]
    (𝒜 : ℕ → AddSubgroup A) [GradedRing 𝒜] (D : ℕ)
    [GradedRing (fun n => 𝒜 (D * n))] (n : ℕ) (hn : ¬ D ∣ n) :
    GradedRing.proj 𝒜 n = 0 := by
  let ℬ := fun j => 𝒜 (D * j)
  have hcomp : (GradedRing.proj 𝒜 n).comp (DirectSum.coeAddMonoidHom ℬ) = 0 := by
    apply DirectSum.addHom_ext
    intro i a
    simp only [AddMonoidHom.comp_apply, DirectSum.coeAddMonoidHom_of,
      GradedRing.proj_apply, AddMonoidHom.zero_apply]
    apply DirectSum.decompose_of_mem_ne 𝒜 a.property
    intro h
    exact hn ⟨i, h.symm⟩
  apply AddMonoidHom.ext
  intro a
  obtain ⟨b, rfl⟩ := (DirectSum.Decomposition.isInternal ℬ).surjective a
  exact DFunLike.congr_fun hcomp b

end HodgeLean.Foundations.Program
