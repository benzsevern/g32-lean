import HodgeLean.Foundations.BundleResolution.ChernTensorGeneratorHelpers
import HodgeLean.Foundations.Singular.TensorDegreeSum

/-! # A single nonzero first-factor degree in a tensor grading

The actual total graded tensor group reduces to the unique surviving
bidegree, with insertion given by the specified scalar generator.
HC no distance; AV milestone no distance. -/

noncomputable section
open HodgeLean.Foundations.Singular
open scoped TensorProduct DirectSum
namespace HodgeLean.Foundations.BundleResolution

variable (M N : ℕ → Type) [∀ i, AddCommGroup (M i)] [∀ i, Module ℚ (M i)]
variable [∀ i, AddCommGroup (N i)] [∀ i, Module ℚ (N i)]

def i1_singleDegreeTensorInsertion (d n : ℕ) (u : M d) :
    N n →ₗ[ℚ] ⨁ a : tensorDegreeIndex (d + n), M a.val.1 ⊗[ℚ] N a.val.2 :=
  (DirectSum.lof ℚ (tensorDegreeIndex (d + n))
    (fun a => M a.val.1 ⊗[ℚ] N a.val.2)
    ⟨(d, n), Finset.mem_antidiagonal.mpr rfl⟩).comp (TensorProduct.mk ℚ (M d) (N n) u)

theorem i1_singleDegreeTensorInsertion_bijective (d n : ℕ) (u : M d)
    (hu : Function.Bijective (LinearMap.toSpanSingleton ℚ (M d) u))
    (hz : ∀ p, p ≠ d → Subsingleton (M p)) :
    Function.Bijective (i1_singleDegreeTensorInsertion M N d n u) := by
  classical
  let a : tensorDegreeIndex (d + n) := ⟨(d, n), Finset.mem_antidiagonal.mpr rfl⟩
  have ht := i1_tensorGenerator_bijective (W := N n) u hu
  constructor
  · intro b c h
    apply ht.1
    change DirectSum.of (fun a : tensorDegreeIndex (d + n) => M a.val.1 ⊗[ℚ] N a.val.2)
        a (u ⊗ₜ[ℚ] b) = DirectSum.of _ a (u ⊗ₜ[ℚ] c) at h
    have he := congrArg (fun x => x a) h
    simp only [DirectSum.of_eq_same] at he
    exact he
  · intro x
    obtain ⟨b, hb⟩ := ht.2 (x a)
    refine ⟨b, ?_⟩
    change DirectSum.of (fun a : tensorDegreeIndex (d + n) => M a.val.1 ⊗[ℚ] N a.val.2)
      a (u ⊗ₜ[ℚ] b) = x
    change u ⊗ₜ[ℚ] b = x a at hb
    rw [hb]
    ext c
    by_cases hc : c = a
    · subst c
      exact DirectSum.of_eq_same _ _
    · have hp : c.val.1 ≠ d := by
        intro h
        apply hc
        apply Subtype.ext
        apply Prod.ext h
        have := Finset.mem_antidiagonal.mp c.property
        dsimp [a]
        omega
      letI := hz c.val.1 hp
      have hx : x c = 0 := Subsingleton.elim _ _
      rw [DirectSum.of_eq_of_ne a c _ hc, hx]

end HodgeLean.Foundations.BundleResolution
