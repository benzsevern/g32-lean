import HodgeLean.Foundations.Program.SchoenTowerHardt6RbMappedBandClosure

/-! Graph-cell closure equations in the actual height-first ambient coordinates. -/
noncomputable section
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_mapped_graph_closure {n : ℕ}
    (C D : Set (EuclideanSpace ℝ (Fin n))) (hC : IsCompact C)
    (hD : closure D = C)
    (β : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hβ : ContinuousOn β C)
    (e : EuclideanSpace ℝ (Fin (n + 1)) ≃ₜ EuclideanSpace ℝ (Fin (n + 1)))
    (l : EuclideanSpace ℝ (Fin n) → ℝ) (hl : ContinuousOn l C) :
    closure (e '' {z | ∃ x ∈ D, (∀ j, z j.succ = β x j) ∧ z 0 = l x}) =
      e '' {z | ∃ x ∈ C, (∀ j, z j.succ = β x j) ∧ z 0 = l x} := by
  obtain ⟨v, hv0, hvs, _, _⟩ := s2v_hardt6rb_band_coordinate_equiv n
  let F := fun x => e (v (β x, l x))
  have hF : ContinuousOn F C :=
    e.continuous.comp_continuousOn (v.continuous.comp_continuousOn (hβ.prodMk hl))
  have himage (S : Set (EuclideanSpace ℝ (Fin n))) :
      F '' S = e '' {z | ∃ x ∈ S, (∀ j, z j.succ = β x j) ∧ z 0 = l x} := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨v (β x, l x), ⟨x, hx, hvs _, hv0 _⟩, rfl⟩
    · rintro ⟨z, ⟨x, hx, hz, ht⟩, rfl⟩
      refine ⟨x, hx, congrArg e ?_⟩
      ext j
      refine Fin.cases ((hv0 _).trans ht.symm)
        (fun i => (hvs _ i).trans (hz i).symm) j
  rw [← himage D, ← himage C]
  apply Set.Subset.antisymm
  · apply closure_minimal (Set.image_mono (hD ▸ subset_closure))
    exact (hC.image_of_continuousOn hF).isClosed
  · rw [← hD] at hF ⊢
    exact hF.image_closure

end HodgeLean.Foundations.Program
