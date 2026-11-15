import HodgeLean.Foundations.Program.SchoenCycleC1PartialIsoTowerHelpers

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Every compatible earlier map retained by a final weighted chart carries
the partial isomorphism determined by the actual tower transitions. -/
theorem s2e_c1_earlier_maps_partial_iso
    {r : ℕ} (X : Fin (r + 1) → Scheme)
    (b : ∀ i : Fin r, X i.succ ⟶ X i.castSucc)
    (c : ∀ i, X (Fin.last r) ⟶ X i)
    (hc : c (Fin.last r) = 𝟙 _)
    (hb : ∀ i : Fin r, c i.succ ≫ b i = c i.castSucc)
    (P : ∀ i : Fin r, (X i.succ).PartialIso (X i.castSucc))
    (hP : ∀ i, (P i).iso.hom ≫ (P i).target.ι = (P i).source.ι ≫ b i) :
    ∀ i, ∃ Q : (X (Fin.last r)).PartialIso (X i),
      Q.iso.hom ≫ Q.target.ι = Q.source.ι ≫ c i := by
  apply Fin.reverseInduction
  · refine ⟨Scheme.PartialIso.refl _, ?_⟩
    simp [hc, Scheme.PartialIso.refl]
  · intro i ih
    obtain ⟨Q, hQ⟩ := ih
    refine ⟨Q.trans (P i), ?_⟩
    have hQ' : Q.IsOver (c i.castSucc) (b i) := by
      simpa only [Scheme.PartialIso.IsOver, Category.assoc, hb i] using
        congrArg (fun f => f ≫ b i) hQ
    have hP' : (P i).IsOver (b i) (𝟙 _) := by
      simpa only [Scheme.PartialIso.IsOver, Category.comp_id] using hP i
    simpa only [Scheme.PartialIso.IsOver, Category.comp_id] using hQ'.trans hP'

end HodgeLean.Foundations.Program
