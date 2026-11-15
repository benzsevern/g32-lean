import HodgeLean.Foundations.Program.G32Native.EulerModel.NormalPermutationBase

/-! # Specified coordinate actions on the actual global kernel total space -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace HodgeLean.Foundations.Program.G32Native.EulerModel

/-- The specified simultaneous coordinate permutation acts on the same actual kernel total space. -/
def normalPermutationTotalHomeomorph (k : ℕ) (e : Equiv.Perm (Fin (k + 1))) :
    ProjectiveNormalTotalSpace k ≃ₜ ProjectiveNormalTotalSpace k := by
  let A := normalCoordinatePermutation k e
  let B := normalPermutationBaseHomeomorph k e
  have hb : Continuous (fun v : ProjectiveNormalTotalSpace k => v.1.1) :=
    continuous_fst.comp continuous_subtype_val
  have hv : Continuous (fun v : ProjectiveNormalTotalSpace k => v.1.2) :=
    continuous_snd.comp continuous_subtype_val
  have ht (v : ProjectiveNormalTotalSpace k) : A v.1.2 ∈ projectiveNormalKernel k (B v.1.1) :=
    (normalCoordinatePermutation_kernel k e v.1.1 v.1.2).mpr v.2
  have hi (v : ProjectiveNormalTotalSpace k) :
      A.symm v.1.2 ∈ projectiveNormalKernel k (B.symm v.1.1) := by
    apply (normalCoordinatePermutation_kernel k e _ _).mp
    change A (A.symm v.1.2) ∈ projectiveNormalKernel k (B (B.symm v.1.1))
    simpa only [LinearEquiv.apply_symm_apply, Homeomorph.apply_symm_apply] using v.2
  exact
    { toFun := fun v => ⟨(B v.1.1, A v.1.2), ht v⟩
      invFun := fun v => ⟨(B.symm v.1.1, A.symm v.1.2), hi v⟩
      left_inv := fun v => by
        apply Subtype.ext
        apply Prod.ext
        · exact B.symm_apply_apply v.1.1
        · exact A.symm_apply_apply v.1.2
      right_inv := fun v => by
        apply Subtype.ext
        apply Prod.ext
        · exact B.apply_symm_apply v.1.1
        · exact A.apply_symm_apply v.1.2
      continuous_toFun := ((B.continuous.comp hb).prodMk
        (A.toLinearMap.continuous_of_finiteDimensional.comp hv)).subtype_mk ht
      continuous_invFun := ((B.symm.continuous.comp hb).prodMk
        (A.symm.toLinearMap.continuous_of_finiteDimensional.comp hv)).subtype_mk hi }

#print axioms normalPermutationTotalHomeomorph
/-- The actual total-space permutation retains precisely the zero vectors of the kernel family. -/
theorem normalPermutationTotalHomeomorph_zero_iff (k : ℕ)
    (e : Equiv.Perm (Fin (k + 1))) (v : ProjectiveNormalTotalSpace k) :
    (normalPermutationTotalHomeomorph k e v).1.2 = 0 ↔ v.1.2 = 0 := by
  change normalCoordinatePermutation k e v.1.2 = 0 ↔ v.1.2 = 0
  constructor
  · intro hz
    apply (normalCoordinatePermutation k e).injective
    simpa only [map_zero] using hz
  · intro hz
    rw [hz, map_zero]

#print axioms normalPermutationTotalHomeomorph_zero_iff
end HodgeLean.Foundations.Program.G32Native.EulerModel
