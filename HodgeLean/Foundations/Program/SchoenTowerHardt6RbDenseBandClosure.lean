import HodgeLean.Foundations.Program.SchoenTowerHardt6RbCompactAmbientBand
import Mathlib.Topology.ContinuousOn

/-! The strict part of a continuous band is dense even when boundary fibers collapse. -/
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_dense_band_closure {E : Type*}
    [TopologicalSpace E] [T2Space E]
    (C D : Set E) (hC : IsCompact C) (hD : closure D = C)
    (l u : E → ℝ) (hl : ContinuousOn l C) (hu : ContinuousOn u C)
    (hlu : ∀ x ∈ C, l x ≤ u x) (hstrict : ∀ x ∈ D, l x < u x) :
    closure {p : E × ℝ | p.1 ∈ D ∧ l p.1 < p.2 ∧ p.2 < u p.1} =
      {p : E × ℝ | p.1 ∈ C ∧ l p.1 ≤ p.2 ∧ p.2 ≤ u p.1} := by
  let F : E × ℝ → E × ℝ :=
    fun p => (p.1, (1 - p.2) * l p.1 + p.2 * u p.1)
  have hdomain : closure (D ×ˢ Set.Ioo (0 : ℝ) 1) = C ×ˢ Set.Icc (0 : ℝ) 1 := by
    rw [closure_prod_eq, hD, closure_Ioo zero_ne_one]
  have hF : ContinuousOn F (closure (D ×ˢ Set.Ioo (0 : ℝ) 1)) := by
    rw [hdomain]
    apply continuousOn_fst.prodMk
    exact ((continuousOn_const.sub continuousOn_snd).mul
      (hl.comp continuousOn_fst (fun _ hx => hx.1))).add
      (continuousOn_snd.mul (hu.comp continuousOn_fst (fun _ hx => hx.1)))
  have himage : F '' (D ×ˢ Set.Ioo (0 : ℝ) 1) ⊆
      {p : E × ℝ | p.1 ∈ D ∧ l p.1 < p.2 ∧ p.2 < u p.1} := by
    rintro _ ⟨⟨x, t⟩, ⟨hx, ht⟩, rfl⟩
    have hpos := sub_pos.mpr (hstrict x hx)
    refine ⟨hx, ?_, ?_⟩ <;> dsimp [F]
    · nlinarith [mul_pos ht.1 hpos]
    · nlinarith [mul_pos (sub_pos.mpr ht.2) hpos]
  apply Set.Subset.antisymm
  · apply closure_minimal
    · intro p hp
      exact ⟨hD ▸ subset_closure hp.1, hp.2.1.le, hp.2.2.le⟩
    · exact (s2v_hardt6rb_compact_ambient_band C hC l u hl hu hlu).isClosed
  · intro p hp
    obtain ⟨t, ht, he⟩ := s2v_hardt6rb_band_interpolation_surjective
      (hlu p.1 hp.1) hp.2
    apply closure_mono himage
    apply hF.image_closure
    refine ⟨(p.1, t), ?_, Prod.ext rfl he⟩
    rw [hdomain]
    exact ⟨hp.1, ht⟩

end HodgeLean.Foundations.Program
