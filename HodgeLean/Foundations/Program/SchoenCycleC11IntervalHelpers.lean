import Mathlib.Topology.Homotopy.Lifting

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open Topology unitInterval
namespace HodgeLean.Foundations.Program

/-- Local sections through each fibre point give continuous lifts of interval maps.
Source: Hatcher, Algebraic Topology, path lifting by finite interval subdivision. -/
theorem s2e_c11_interval_lift_of_local_sections
    {E B : Type*} [TopologicalSpace E] [TopologicalSpace B] (p : E → B)
    (hloc : ∀ b : B, ∃ U : Set B, b ∈ U ∧ IsOpen U ∧
      ∀ e : E, p e ∈ U → ∃ s : B → E, ContinuousOn s U ∧
        Set.EqOn (p ∘ s) id U ∧ s (p e) = e)
    (γ : C(I, B)) (e : E) (h₀ : γ 0 = p e) :
    ∃ Γ : C(I, E), p ∘ Γ = γ ∧ Γ 0 = e := by
  classical
  choose U hb ho hs using hloc
  obtain ⟨t, ht₀, ht, ⟨N, hN⟩, hcover⟩ :=
    exists_monotone_Icc_subset_open_cover_unitInterval
      (fun b => (ho b).preimage γ.continuous)
      (fun x _ => Set.mem_iUnion.mpr ⟨γ x, hb _⟩)
  have hpartial : ∀ n, ∃ g : I → E, ContinuousOn g (Set.Icc 0 (t n)) ∧
      Set.EqOn (p ∘ g) γ (Set.Icc 0 (t n)) ∧ g 0 = e := by
    intro n
    induction n with
    | zero =>
      refine ⟨fun _ => e, continuous_const.continuousOn, ?_, rfl⟩
      intro x hx
      have hx₀ : x = 0 := by simpa only [ht₀, Set.Icc_self, Set.mem_singleton_iff] using hx
      subst x
      exact h₀.symm
    | succ n ih =>
      obtain ⟨g, hg, hpg, hg₀⟩ := ih
      obtain ⟨b, hseg⟩ := hcover n
      have hgn : p (g (t n)) = γ (t n) := hpg ⟨ht₀ ▸ ht n.zero_le, le_rfl⟩
      obtain ⟨s, hsc, hps, hsg⟩ := hs b (g (t n))
        (hgn ▸ hseg ⟨le_rfl, ht n.le_succ⟩)
      refine ⟨fun x => if x ≤ t n then g x else s (γ x),
        ContinuousOn.if ?_ ?_ ?_, ?_, ?_⟩
      · intro x hx
        have hxn : x = t n := Set.mem_singleton_iff.mp (frontier_Iic_subset _ hx.2)
        subst x
        exact (hgn ▸ hsg).symm
      · apply hg.mono
        intro x hx
        rw [closure_le_eq continuous_id' continuous_const] at hx
        exact ⟨hx.1.1, hx.2⟩
      · apply hsc.comp γ.continuous.continuousOn
        intro x hx
        simp only [not_le] at hx
        apply hseg
        exact ⟨closure_lt_subset_le continuous_const continuous_subtype_val hx.2, hx.1.2⟩
      · intro x hx
        dsimp only [Function.comp_apply]
        split_ifs with h
        · exact hpg ⟨hx.1, h⟩
        · exact hps (hseg ⟨le_of_not_ge h, hx.2⟩)
      · dsimp only
        rw [if_pos (ht₀ ▸ ht n.zero_le)]
        exact hg₀
  obtain ⟨g, hg, hpg, hg₀⟩ := hpartial N
  have htN : t N = 1 := hN N le_rfl
  have hI : Set.Icc (0 : I) (t N) = Set.univ := by
    rw [htN]
    exact Set.eq_univ_iff_forall.mpr (fun x => ⟨bot_le, le_top⟩)
  rw [hI] at hg hpg
  exact ⟨⟨g, continuousOn_univ.mp hg⟩, funext (fun x => hpg (Set.mem_univ x)), hg₀⟩

end HodgeLean.Foundations.Program
