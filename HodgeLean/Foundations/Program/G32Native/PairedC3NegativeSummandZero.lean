import HodgeLean.Foundations.Program.G32Native.PairedC3NegativeSummandMaps

/-! # Factoring a map with zero negative components through the original trivial summands -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 20000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native

/-- A retained earlier negative coordinate has its original recursive projection. -/
theorem paired_c3_negative_projection_castSucc (k a b : ℕ) (i : Fin (b + 1)) :
    pairedC3NegativeProjection k a (b + 1) i.castSucc =
      biprod.fst ≫ pairedC3NegativeProjection k a b i := by
  simp only [pairedC3SplitBundle, pairedC3NegativeProjection, pairedC3NegativeSummandIso, Fin.lastCases_castSucc,
    Iso.trans_hom, biprod.mapIso_hom, Category.assoc, biprod.associator_hom,
    biprod.lift_fst, biprod.lift_fst_assoc, biprod.map_fst_assoc]

/-- Vanishing of every actual negative coordinate leaves exactly the
original trivial subobject, without replacing its inclusion. -/
theorem paired_c3_zero_negative_factor (k a b : ℕ) {Z : (pairedC3Proj k).Modules}
    (f : Z ⟶ pairedC3SplitBundle k a (b + 1))
    (hz : ∀ i : Fin (b + 1), f ≫ pairedC3NegativeProjection k a b i = 0) :
    ∃ l : Z ⟶ (SheafOfModules.free (Fin a) : (pairedC3Proj k).Modules),
      f = l ≫ pairedC3TrivialInclusion k a (b + 1) := by
  induction b with
  | zero =>
    refine ⟨f ≫ biprod.fst, ?_⟩
    have hlast := hz (Fin.last 0)
    rw [paired_c3_negative_projection_last] at hlast
    apply biprod.hom_ext <;>
      simp only [pairedC3TrivialInclusion, pairedC3SplitBundle, Category.assoc,
        Category.id_comp, biprod.inl_fst, biprod.inl_snd, Category.comp_id, comp_zero]
    exact hlast
  | succ b ih =>
    have hz' (i : Fin (b + 1)) : (f ≫ biprod.fst) ≫
        pairedC3NegativeProjection k a b i = 0 := by
      have h := hz i.castSucc
      rw [paired_c3_negative_projection_castSucc] at h
      exact h
    obtain ⟨l, hl⟩ := ih (f ≫ biprod.fst) hz'
    refine ⟨l, ?_⟩
    have hlast := hz (Fin.last (b + 1))
    rw [paired_c3_negative_projection_last] at hlast
    apply biprod.hom_ext
    · simpa only [pairedC3TrivialInclusion, Category.assoc, biprod.inl_fst,
        Category.comp_id] using hl
    · simpa only [pairedC3TrivialInclusion, Category.assoc, biprod.inl_snd, comp_zero] using hlast

end HodgeLean.Foundations.Program.G32Native
