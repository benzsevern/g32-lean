import HodgeLean.Foundations.Program.SchoenTowerHardt6RbAmbientBand
import HodgeLean.Foundations.Program.SchoenTowerHardt6RbBandGraphs

/-! Actual ambient graph equations for band rescaling across collapsed fibers. -/
noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_ambient_band_rescale {E : Type*}
    [TopologicalSpace E] [T2Space E] (A : Set E) [CompactSpace A]
    (l u c d : E → ℝ)
    (hl : Continuous (fun x : A => l x.val))
    (hu : Continuous (fun x : A => u x.val))
    (hc : Continuous (fun x : A => c x.val))
    (hd : Continuous (fun x : A => d x.val))
    (hlu : ∀ x : A, l x.val ≤ u x.val)
    (hcd : ∀ x : A, c x.val ≤ d x.val)
    (hzero : ∀ x : A, l x.val = u x.val ↔ c x.val = d x.val) :
    ∃ h : {p : E × ℝ | p.1 ∈ A ∧ l p.1 ≤ p.2 ∧ p.2 ≤ u p.1} ≃ₜ
        {p : E × ℝ | p.1 ∈ A ∧ c p.1 ≤ p.2 ∧ p.2 ≤ d p.1},
      ∀ p q, h p = q ↔ p.val.1 = q.val.1 ∧
        (p.val.2 - l p.val.1) * (d p.val.1 - c p.val.1) =
          (q.val.2 - c p.val.1) * (u p.val.1 - l p.val.1) := by
  obtain ⟨es, hes, _⟩ := s2v_hardt6rb_ambient_band_homeomorph A l u
  obtain ⟨et, het, _⟩ := s2v_hardt6rb_ambient_band_homeomorph A c d
  obtain ⟨b, hb⟩ := s2v_hardt6rb_band_homeomorph_full_graph
    (fun x : A => l x.val) (fun x : A => u x.val)
    (fun x : A => c x.val) (fun x : A => d x.val) hl hu hc hd hlu hcd hzero
  let h := (es.trans b).trans et.symm
  refine ⟨h, ?_⟩
  intro p q
  have he : h p = q ↔ b (es p) = et q := by
    constructor
    · intro hpq
      have hh := congrArg et hpq
      simpa only [h, Homeomorph.trans_apply, Homeomorph.apply_symm_apply] using hh
    · intro hpq
      apply et.injective
      simpa only [h, Homeomorph.trans_apply, Homeomorph.apply_symm_apply] using hpq
  rw [he, hb]
  simpa only [Subtype.ext_iff, (hes p).1, (hes p).2, (het q).1, (het q).2]

end HodgeLean.Foundations.Program
