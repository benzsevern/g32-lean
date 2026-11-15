import HodgeLean.Foundations.Curves.AbelTheorem.CompactAvoidingCover

noncomputable section
open HodgeLean.Foundations.Program
open Set Filter Manifold Metric
open scoped Topology ContDiff
namespace HodgeLean.Foundations.Curves.AbelTheorem
set_option maxHeartbeats 400000
variable {E C : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [FiniteDimensional ℂ E] [TopologicalSpace C] [ChartedSpace E C]
  [IsManifold 𝓘(ℂ, E) ω C] [T2Space C]

theorem compact_set_containing_loop_cover {P : ℝ → C} (K : b3Rest_Cover E P)
    (S : Set C)
    (hK : ∀ k, closedBall (chartAt E (K.x k) (K.x k)) (K.r k) ⊆
      (chartAt E (K.x k)).target ∧ (chartAt E (K.x k)).symm ''
        closedBall (chartAt E (K.x k) (K.x k)) (K.r k) ⊆ Sᶜ) :
    ∃ A : Set C, IsCompact A ∧ A ⊆ Sᶜ ∧ ∀ k : ℤ,
      (chartAt E (K.x k)).symm '' ball (chartAt E (K.x k) (K.x k)) (K.r k) ⊆ A := by
  letI : ProperSpace E := FiniteDimensional.proper_real E
  let A : Set C := ⋃ i : Fin K.N, (chartAt E (K.x i)).symm ''
    closedBall (chartAt E (K.x i) (K.x i)) (K.r i)
  refine ⟨A, isCompact_iUnion (fun i => (isCompact_closedBall _ _).image_of_continuousOn
    ((chartAt E (K.x i)).continuousOn_symm.mono (hK i).1)), ?_, ?_⟩
  · rintro z hz
    obtain ⟨i, hi⟩ := mem_iUnion.mp hz
    exact (hK i).2 hi
  · intro k z hz
    have hn : (0 : ℤ) < K.N := Int.natCast_pos.mpr K.pos
    let i : Fin K.N := ⟨(k % (K.N : ℤ)).toNat, by
      have hm := Int.emod_nonneg k hn.ne'
      have hl := Int.emod_lt_of_pos k hn
      omega⟩
    have hi : (i : ℤ) = k % (K.N : ℤ) := Int.toNat_of_nonneg (Int.emod_nonneg k hn.ne')
    apply mem_iUnion.mpr
    refine ⟨i, ?_⟩
    have hx : K.x i = K.x k := by rw [hi]; exact b3Rest_periodic_emod K.x_add k
    have hr : K.r i = K.r k := by rw [hi]; exact b3Rest_periodic_emod K.r_add k
    rw [hx, hr]
    exact image_mono ball_subset_closedBall hz

end HodgeLean.Foundations.Curves.AbelTheorem
