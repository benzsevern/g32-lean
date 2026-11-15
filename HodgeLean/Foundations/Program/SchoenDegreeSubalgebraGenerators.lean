import HodgeLean.Foundations.Program.SchoenBoundedMonomialGeneration
import HodgeLean.Foundations.Program.SchoenDegreeSubalgebra

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open scoped BigOperators
namespace HodgeLean.Foundations.Program

/-- The actual degree-generated subalgebra has finitely many generators in that same degree. -/
theorem s2_degreeSubalgebra_finite_generators {A ι : Type} [CommRing A] [Fintype ι]
    (𝒜 : ℕ → AddSubgroup A) [GradedRing 𝒜] (v : ι → A) (d : ι → ℕ)
    (hd : ∀ i, 0 < d i) (hv : ∀ i, v i ∈ 𝒜 (d i))
    (hgen : Algebra.adjoin (𝒜 0) (Set.range v) = ⊤) (M : ℕ) :
    ∃ n : ℕ, ∃ w : Fin (n + 1) → A, (∀ i, w i ∈ 𝒜 M) ∧
      Algebra.adjoin (𝒜 0) (Set.range w) = s2_degreeSubalgebra 𝒜 M := by
  classical
  let I := {a : ι → Fin (M + 1) // ∑ i, (a i).val * d i = M}
  let u : I → A := fun a => ∏ i, v i ^ (a.val i).val
  have hu : ∀ a, u a ∈ 𝒜 M := by
    intro a
    have h := SetLike.prod_pow_mem_graded 𝒜 d v (fun i => (a.val i).val)
      (F := Finset.univ) (fun i _ => hv i)
    simpa only [smul_eq_mul, a.property] using h
  let e : Option I ≃ Fin (Fintype.card I + 1) := Fintype.equivFinOfCardEq (by simp)
  let w : Fin (Fintype.card I + 1) → A := fun i => (e.symm i).elim 0 u
  have hw : ∀ i, w i ∈ 𝒜 M := by
    intro i
    dsimp only [w]
    cases e.symm i with
    | none => exact (𝒜 M).zero_mem
    | some a => exact hu a
  refine ⟨Fintype.card I, w, hw, le_antisymm ?_ ?_⟩
  · apply Algebra.adjoin_le
    rintro _ ⟨i, rfl⟩
    exact Algebra.subset_adjoin (hw i)
  · apply Algebra.adjoin_le
    intro x hx
    have hx' := s2_homogeneous_mem_adjoin_boundedMonomials 𝒜 v d hd hv hgen M hx
    apply (Algebra.adjoin_mono (show Set.range u ⊆ Set.range w from ?_)) hx'
    rintro _ ⟨a, rfl⟩
    exact ⟨e (some a), by simp only [w, Equiv.symm_apply_apply, Option.elim_some]⟩

end HodgeLean.Foundations.Program
