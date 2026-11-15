import HodgeLean.Foundations.Program.SchoenCycleC2SupportedSumHelpers
import HodgeLean.Foundations.Program.SchoenCycleC2LocalSupportHelpers

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicTopology.Singular
open HodgeLean.Adapters
open scoped BigOperators
namespace HodgeLean.Foundations.Program

/-- Near a single component the weighted supported representative restricts to
that component representative multiplied by its coefficient. -/
theorem s2e_weightedSupportedClass_restrict_single
    (X : TopCat.{0}) (m n : ℕ) (S : Fin m → Set X) (T : Set X)
    (a : Fin m → ℚ) (hST : ∀ t, a t ≠ 0 → S t ⊆ T)
    (c : ∀ t, CohomologyWithSupport ℚ X (S t) n)
    (t : Fin m) (ha : a t ≠ 0) (V : Set X)
    (hV : ∀ s, s ≠ t → ∀ x ∈ V, x ∉ S s) :
    relativeCohomologyMap ℚ n (a3b4_neighborhoodPairMap V T)
      (s2e_weightedSupportedClass X m n S T a hST c) =
    a t • relativeCohomologyMap ℚ n
      (s2e_localSupportMap V (S t) T (fun x _ hx => hST t ha hx))
      (relativeCohomologyMap ℚ n (a3b4_neighborhoodPairMap V (S t)) (c t)) := by
  classical
  let f : TopCat.of V ⟶ X := TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩
  change cohomologyWithSupportMap ℚ n f T
    (SupportedClasses.weightedSum X n S T a hST c) = _
  rw [SupportedClasses.pullback_weightedSum]
  unfold SupportedClasses.weightedSum
  rw [Finset.sum_eq_single t]
  · simp only [dite_eq_left ha]
    rfl
  · intro s _ hst
    by_cases hs : a s ≠ 0
    · letI := neighborhoodSupportRelativeCohomology_subsingleton X (S s) n V (hV s hst)
      have hz : relativeCohomologyMap ℚ n (a3b4_neighborhoodPairMap V (S s)) (c s) = 0 :=
        Subsingleton.elim _ _
      change cohomologyWithSupportMap ℚ n f (S s) (c s) = 0 at hz
      simp only [dite_eq_left hs, hz, map_zero, smul_zero]
    · simp only [dite_eq_right hs]
  · intro h
    exact (h (Finset.mem_univ t)).elim

end HodgeLean.Foundations.Program
