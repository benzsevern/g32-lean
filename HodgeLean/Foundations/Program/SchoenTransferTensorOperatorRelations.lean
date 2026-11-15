import HodgeLean.Foundations.Program.SchoenTransferTensorEigenSupport
import HodgeLean.Foundations.Program.SchoenTransferAlternatingTensorRange

noncomputable section
open scoped TensorProduct
namespace HodgeLean.Foundations.Program

/-- Operators at distinct tensor coordinates commute. -/
theorem s4_tensorCoordinate_commute {K V I : Type*} [Field K]
    [AddCommGroup V] [Module K V] [Fintype I] [DecidableEq I]
    (A : Module.End K V) (i j : I) :
    (s4_tensorCoordinate A i).comp (s4_tensorCoordinate A j) =
      (s4_tensorCoordinate A j).comp (s4_tensorCoordinate A i) := by
  classical
  unfold s4_tensorCoordinate
  rw [← PiTensorProduct.map_comp, ← PiTensorProduct.map_comp]
  congr 1
  funext k
  by_cases hki : k = i
  · subst k
    by_cases hij : i = j
    · subst j; rfl
    · simp only [Function.update_self, Function.update_of_ne hij, LinearMap.comp_id,
        LinearMap.id_comp]
  · by_cases hkj : k = j
    · subst k
      simp only [Function.update_self, Function.update_of_ne hki, LinearMap.comp_id,
        LinearMap.id_comp]
    · simp only [Function.update_of_ne hki, Function.update_of_ne hkj]

/-- Tensor permutations carry a coordinate operator to its reindexed coordinate. -/
theorem s4_tensorPermutation_coordinate {K V : Type*} [Field K]
    [AddCommGroup V] [Module K V] (n : ℕ) (A : Module.End K V)
    (σ : Equiv.Perm (Fin n)) (i : Fin n) :
    (s4_tensorPermutation n σ).comp (s4_tensorCoordinate A i) =
      (s4_tensorCoordinate A (σ.symm i)).comp (s4_tensorPermutation n σ) := by
  classical
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro v
  simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply,
    s4_tensorPermutation, PiTensorProduct.lift.tprod, MultilinearMap.domDomCongr_apply,
    s4_tensorCoordinate, PiTensorProduct.map_tprod]
  congr 1
  funext k
  by_cases hk : k = σ.symm i
  · subst k
    rw [show σ (σ.symm i) = i from σ.apply_symm_apply i]
    simp only [Function.update_self]
  · have hki : σ k ≠ i := by
      intro he
      apply hk
      exact σ.injective (he.trans (σ.apply_symm_apply i).symm)
    simp only [Function.comp_apply, Function.update_of_ne hk, Function.update_of_ne hki,
      LinearMap.id_apply]

end HodgeLean.Foundations.Program
