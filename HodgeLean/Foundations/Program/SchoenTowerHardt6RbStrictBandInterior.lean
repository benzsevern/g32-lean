import HodgeLean.Foundations.Program.SchoenTowerHardt6RbLocalIntrinsicInterior

/-! Strict fiber points over intrinsic base interiors belong to the actual band interior. -/
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_strict_band_interior {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (C : Set E) (l u : E → ℝ) (hl : Continuous l) (hu : Continuous u)
    {p : E × ℝ} (hp : p.1 ∈ intrinsicInterior ℝ C)
    (hlo : l p.1 < p.2) (hup : p.2 < u p.1) :
    p ∈ intrinsicInterior ℝ {q : E × ℝ | q.1 ∈ C ∧ l q.1 ≤ q.2 ∧ q.2 ≤ u q.1} := by
  apply s2v_hardt6rb_local_intrinsicInterior _ (C ×ˢ (Set.univ : Set ℝ))
    {q : E × ℝ | l q.1 < q.2 ∧ q.2 < u q.1}
  · exact fun _ hq => ⟨hq.1, Set.mem_univ _⟩
  · exact (isOpen_lt (hl.comp continuous_fst) continuous_snd).inter
      (isOpen_lt continuous_snd (hu.comp continuous_fst))
  · exact fun _ hq => ⟨hq.2.1, hq.1.1.le, hq.1.2.le⟩
  · rw [intrinsicInterior_prod_eq]
    exact ⟨hp, by simp⟩
  · exact ⟨hlo, hup⟩

end HodgeLean.Foundations.Program
