import HodgeLean.Foundations.Program.SchoenTowerHardt6RbBandInterpolation
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.Compact

/-! Compactness of actual ambient bands with continuous endpoints on a compact base. -/
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_compact_ambient_band {E : Type*} [TopologicalSpace E]
    (C : Set E) (hC : IsCompact C) (l u : E → ℝ)
    (hl : ContinuousOn l C) (hu : ContinuousOn u C) (hlu : ∀ x ∈ C, l x ≤ u x) :
    IsCompact {p : E × ℝ | p.1 ∈ C ∧ l p.1 ≤ p.2 ∧ p.2 ≤ u p.1} := by
  let f : E × ℝ → E × ℝ := fun p => (p.1, (1 - p.2) * l p.1 + p.2 * u p.1)
  have hf : ContinuousOn f (C ×ˢ Set.Icc (0 : ℝ) 1) := by
    apply continuousOn_fst.prodMk
    exact ((continuousOn_const.sub continuousOn_snd).mul
      (hl.comp continuousOn_fst (fun _ hx => hx.1))).add
      (continuousOn_snd.mul (hu.comp continuousOn_fst (fun _ hx => hx.1)))
  have he : f '' (C ×ˢ Set.Icc (0 : ℝ) 1) =
      {p : E × ℝ | p.1 ∈ C ∧ l p.1 ≤ p.2 ∧ p.2 ≤ u p.1} := by
    ext p
    constructor
    · rintro ⟨q, hq, rfl⟩
      exact ⟨hq.1, s2v_hardt6rb_band_interpolation_mem (hlu q.1 hq.1) hq.2⟩
    · rintro ⟨hp, hlo, hup⟩
      obtain ⟨t, ht, he⟩ := s2v_hardt6rb_band_interpolation_surjective (hlu p.1 hp) ⟨hlo, hup⟩
      exact ⟨(p.1, t), ⟨hp, ht⟩, Prod.ext rfl he⟩
  rw [← he]
  exact (hC.prod isCompact_Icc).image_of_continuousOn hf

end HodgeLean.Foundations.Program
