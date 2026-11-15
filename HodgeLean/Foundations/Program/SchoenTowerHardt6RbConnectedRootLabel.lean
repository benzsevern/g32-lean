import Mathlib.Topology.Connected.Clopen
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Data.Real.Basic

/-! A continuous section of a finite distinct root family has one label on a connected domain. -/
noncomputable section
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_connected_root_label {X ι : Type*}
    [TopologicalSpace X] [ConnectedSpace X] [Fintype ι]
    (f : X → ℝ) (ψ : ι → X → ℝ) (hf : Continuous f)
    (hψ : ∀ i, Continuous (ψ i)) (hinj : ∀ x, Function.Injective (fun i => ψ i x))
    (hcover : ∀ x, ∃ i, f x = ψ i x) :
    ∃ i, ∀ x, f x = ψ i x := by
  classical
  let x₀ : X := Classical.arbitrary X
  obtain ⟨i, hi⟩ := hcover x₀
  let A : Set X := {x | f x = ψ i x}
  have hA : IsClosed A := isClosed_eq hf (hψ i)
  have he : Aᶜ = ⋃ j : {j : ι // j ≠ i}, {x | f x = ψ j.val x} := by
    ext x
    simp only [Set.mem_compl_iff, Set.mem_iUnion, Set.mem_setOf_eq, A]
    constructor
    · intro hx
      obtain ⟨j, hj⟩ := hcover x
      refine ⟨⟨j, ?_⟩, hj⟩
      intro hji
      exact hx (hji ▸ hj)
    · rintro ⟨j, hj⟩ hxi
      exact j.property (hinj x (hj.symm.trans hxi))
  have hAc : IsClosed Aᶜ := by
    rw [he]
    exact isClosed_iUnion_of_finite (fun j => isClosed_eq hf (hψ j.val))
  have hAo : IsOpen A := by simpa only [compl_compl] using hAc.isOpen_compl
  have hcl : IsClopen A := ⟨hA, hAo⟩
  have hAu : A = Set.univ := hcl.eq_univ ⟨x₀, hi⟩
  refine ⟨i, ?_⟩
  intro x
  have hx : x ∈ A := hAu.symm ▸ Set.mem_univ x
  exact hx

end HodgeLean.Foundations.Program
