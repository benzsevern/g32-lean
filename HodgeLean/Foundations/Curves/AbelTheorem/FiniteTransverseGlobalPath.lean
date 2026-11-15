import HodgeLean.Foundations.Curves.AbelTheorem.FiniteTransverseNeighborhood
import HodgeLean.Foundations.Curves.AbelTheorem.FiniteDenseComplement

noncomputable section
open HodgeLean.Foundations.Program
open Set Filter Manifold
open scoped Topology ContDiff
namespace HodgeLean.Foundations.Curves.AbelTheorem
set_option maxHeartbeats 400000
variable {E C : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [FiniteDimensional ℂ E] [TopologicalSpace C] [ChartedSpace E C]
  [IsManifold 𝓘(ℂ, E) ω C] [ConnectedSpace C]
attribute [local instance] b3Forms_isManifold_real

theorem exists_finitely_transverse_good_path (h : Module.finrank ℂ E = 1)
    {ι : Type} [Fintype ι] (γ : ι → b3_SmoothLoop E C) (p q : C)
    (hp : ∀ i s, (γ i).val s ≠ p) (hq : ∀ i s, (γ i).val s ≠ q) :
    ∃ δ : ℝ → C, b3A_IsGoodPath (E := E) δ p q ∧ ∀ i s t, (γ i).val s = δ t →
      b3_orient E (b3_velocity E C (γ i).val s) (b3_velocity E C δ t) ≠ 0 := by
  let R : Set C := {y | (∀ i s, (γ i).val s ≠ y) ∧ ∃ δ : ℝ → C,
    b3A_IsGoodPath (E := E) δ p y ∧ ∀ i s t, (γ i).val s = δ t →
      b3_orient E (b3_velocity E C (γ i).val s) (b3_velocity E C δ t) ≠ 0}
  have hpR : p ∈ R := ⟨hp, fun _ => p, b3A_isGoodPath_const p,
    fun i s _ he => False.elim (hp i s he)⟩
  have hdense := dense_complement_of_finite_smooth_paths h (fun i => (γ i).val)
    (fun i => (γ i).property.2)
  have hprop (x : C) (hx : x ∈ closure R) :
      ∃ V : Set C, IsOpen V ∧ x ∈ V ∧ V ∩ (⋃ i, range (γ i).val)ᶜ ⊆ R := by
    obtain ⟨V, hV, hxV, hjoin⟩ := finite_transverse_path_neighborhood h γ x
    obtain ⟨a, haV, haR⟩ := mem_closure_iff.mp hx V hV hxV
    obtain ⟨haoff, δ, hδ, hδtr⟩ := haR
    refine ⟨V, hV, hxV, ?_⟩
    intro y hy
    have hyoff : ∀ i s, (γ i).val s ≠ y :=
      fun i s hs => hy.2 (mem_iUnion.mpr ⟨i, s, hs⟩)
    obtain ⟨ε, hε, hεtr⟩ := hjoin a haV y hy.1 haoff hyoff
    exact ⟨hyoff, _, hδ.trans hε, fun i =>
      transverse_path_concat (γ i) δ ε hδ.1 hε.1 (hδtr i) (hεtr i) a hδ.apply_one (haoff i)⟩
  have hopen : IsOpen (closure R) := by
    rw [isOpen_iff_mem_nhds]
    intro x hx
    obtain ⟨V, hV, hxV, hsub⟩ := hprop x hx
    exact mem_of_superset (hV.mem_nhds hxV)
      ((hdense.open_subset_closure_inter hV).trans (closure_mono hsub))
  have hall : closure R = Set.univ :=
    IsClopen.eq_univ ⟨isClosed_closure, hopen⟩ ⟨p, subset_closure hpR⟩
  have hqR : q ∈ closure R := by rw [hall]; trivial
  obtain ⟨V, hV, hqV, hsub⟩ := hprop q hqR
  apply (hsub ⟨hqV, ?_⟩).2
  intro hmem
  obtain ⟨i, hi⟩ := mem_iUnion.mp hmem
  obtain ⟨s, hs⟩ := hi
  exact hq i s hs

end HodgeLean.Foundations.Curves.AbelTheorem
