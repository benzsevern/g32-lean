import HodgeLean.Foundations.Program.TorusAlgebraizationB52MultiplicationDual
import HodgeLean.Foundations.Program.TorusAlgebraizationB52Avoidance

noncomputable section
namespace HodgeLean.Foundations.Program

theorem b52_analytic_family_mem_of_open
    {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (U : Submodule ℂ (X → ℂ)) [Module.Finite ℂ U]
    (W : Submodule ℂ U) (f : E → U)
    (hf : ∀ x, Differentiable ℂ (fun a ↦ (f a).val x))
    (O : Set E) (hO : IsOpen O) (hne : O.Nonempty)
    (hmem : ∀ a ∈ O, f a ∈ W) : ∀ a, f a ∈ W := by
  intro a
  apply (Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff W (f a)).mp
  intro φ hφ
  obtain ⟨c, hc⟩ := b52_dual_function_space_finite_evaluations U φ
  have hd : Differentiable ℂ (fun b ↦ φ (f b)) := by
    have he : (fun b ↦ φ (f b)) =
        fun b ↦ ∑ x ∈ c.support, c x * (f b).val x := by
      funext b
      exact hc (f b)
    rw [he]
    exact Differentiable.fun_sum fun x _ ↦ (hf x).const_mul (c x)
  have hz : (fun b ↦ φ (f b)) = 0 := by
    by_contra hn
    obtain ⟨b, hb, hbO⟩ := (b52_dense_nonzero hd hn).exists_mem_open hO hne
    exact hb ((Submodule.mem_dualAnnihilator φ).mp hφ _ (hmem b hbO))
  exact congrFun hz a

theorem b52_dense_simultaneous_nonzero
    {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [Fintype ι]
    (f : ι → E → ℂ) (hf : ∀ i, Differentiable ℂ (f i)) (hne : ∀ i, f i ≠ 0) :
    Dense {z | ∀ i, f i z ≠ 0} := by
  classical
  have hd (S : Finset ι) : Dense {z | ∀ i ∈ S, f i z ≠ 0} := by
    induction S using Finset.induction_on with
    | empty => simpa using (dense_univ : Dense (Set.univ : Set E))
    | @insert i S hi ih =>
      have h := (b52_dense_nonzero (hf i) (hne i)).inter_of_isOpen_left ih
        (isOpen_ne.preimage (hf i).continuous)
      convert h using 1
      ext z
      simp
  simpa using hd Finset.univ

end HodgeLean.Foundations.Program
