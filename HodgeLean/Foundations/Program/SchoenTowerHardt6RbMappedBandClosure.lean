import HodgeLean.Foundations.Program.SchoenTowerHardt6RbDenseBandClosure
import HodgeLean.Foundations.Program.SchoenTowerHardt6RbBandCoordinates

/-! Closure equations for bands after continuous base maps and ambient changes of coordinates. -/
noncomputable section
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_mapped_band_closure {n : ℕ}
    (C D : Set (EuclideanSpace ℝ (Fin n))) (hC : IsCompact C)
    (hD : closure D = C)
    (β : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hβ : ContinuousOn β C)
    (e : EuclideanSpace ℝ (Fin (n + 1)) ≃ₜ EuclideanSpace ℝ (Fin (n + 1)))
    (l u : EuclideanSpace ℝ (Fin n) → ℝ)
    (hl : ContinuousOn l C) (hu : ContinuousOn u C)
    (hlu : ∀ x ∈ C, l x ≤ u x) (hstrict : ∀ x ∈ D, l x < u x) :
    closure (e '' {z | ∃ x ∈ D, (∀ j, z j.succ = β x j) ∧
      l x < z 0 ∧ z 0 < u x}) =
      e '' {z | ∃ x ∈ C, (∀ j, z j.succ = β x j) ∧
        l x ≤ z 0 ∧ z 0 ≤ u x} := by
  obtain ⟨v, hv0, hvs, _, _⟩ := s2v_hardt6rb_band_coordinate_equiv n
  let B := {p : EuclideanSpace ℝ (Fin n) × ℝ |
    p.1 ∈ C ∧ l p.1 ≤ p.2 ∧ p.2 ≤ u p.1}
  let A := {p : EuclideanSpace ℝ (Fin n) × ℝ |
    p.1 ∈ D ∧ l p.1 < p.2 ∧ p.2 < u p.1}
  let F := fun p : EuclideanSpace ℝ (Fin n) × ℝ => e (v (β p.1, p.2))
  have hAB : closure A = B :=
    s2v_hardt6rb_dense_band_closure C D hC hD l u hl hu hlu hstrict
  have hF : ContinuousOn F B := by
    exact e.continuous.comp_continuousOn (v.continuous.comp_continuousOn
      ((hβ.comp continuousOn_fst (fun _ hp => hp.1)).prodMk continuousOn_snd))
  have himage (S : Set (EuclideanSpace ℝ (Fin n))) (R :
      EuclideanSpace ℝ (Fin n) → ℝ → Prop) :
      F '' {p | p.1 ∈ S ∧ R p.1 p.2} =
        e '' {z | ∃ x ∈ S, (∀ j, z j.succ = β x j) ∧ R x (z 0)} := by
    ext y
    constructor
    · rintro ⟨⟨x, t⟩, ⟨hx, ht⟩, rfl⟩
      exact ⟨v (β x, t), ⟨x, hx, hvs _, by rwa [hv0]⟩, rfl⟩
    · rintro ⟨z, ⟨x, hx, hz, ht⟩, rfl⟩
      refine ⟨(x, z 0), ⟨hx, ht⟩, congrArg e ?_⟩
      ext j
      refine Fin.cases (hv0 _) (fun i => (hvs _ i).trans (hz i).symm) j
  rw [← himage D (fun x t => l x < t ∧ t < u x),
    ← himage C (fun x t => l x ≤ t ∧ t ≤ u x)]
  change closure (F '' A) = F '' B
  apply Set.Subset.antisymm
  · apply closure_minimal (Set.image_mono (hAB ▸ subset_closure))
    exact ((s2v_hardt6rb_compact_ambient_band C hC l u hl hu hlu).image_of_continuousOn hF).isClosed
  · rw [← hAB] at hF ⊢
    exact hF.image_closure

end HodgeLean.Foundations.Program
