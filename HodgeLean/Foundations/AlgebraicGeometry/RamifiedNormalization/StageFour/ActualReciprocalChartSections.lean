import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.ClassifiedReciprocalSections
import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.ProjectiveLineReciprocalCoordinate

noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory
open scoped OnePoint
namespace AlgebraicGeometry.RamifiedNormalization.StageFour

/-- Actual integral chart comparisons transport the two binomial classifications into exhaustive scheme component sections. -/
theorem actual_reciprocal_chart_sections
    {A B TA TB I K : Type} [CommRing A] [CommRing B] [Algebra ℂ A] [Algebra ℂ B]
    (F N W : Over (Spec ↧ℂ)) [IsProper F.hom]
    (J : N ⟶ W) [Mono J] (l : F ⟶ N) (a : F ⟶ W) (hl : l ≫ J = a)
    (JA : Over.mk (ComplexPoint.affineSpecStructureMap A) ⟶ N)
    (JB : Over.mk (ComplexPoint.affineSpecStructureMap B) ⟶ N)
    (Q : N ⟶ Over.mk (ComplexPoint.affineSpecStructureMap (Polynomial ℂ)))
    (T : N ⟶ projectiveLine) (q t : A) (q' s : B)
    (hQA : JA ≫ Q = affineLineParameter q) (hQB : JB ≫ Q = affineLineParameter q')
    (hTA : JA ≫ T = projectiveLineChart 1 t) (hTB : JB ≫ T = projectiveLineChart 0 s)
    (U V : Set (ComplexPoint F)) (hcover : ∀ z, z ∈ U ∨ z ∈ V)
    (H₁ : TA ≃ U) (H₂ : TB ≃ V)
    (pA : TA → ComplexPoint (Over.mk (ComplexPoint.affineSpecStructureMap A)))
    (pB : TB → ComplexPoint (Over.mk (ComplexPoint.affineSpecStructureMap B)))
    (hH₁ : ∀ z, Point.map a (H₁ z).val = Point.map (JA ≫ J) (pA z))
    (hH₂ : ∀ z, Point.map a (H₂ z).val = Point.map (JB ≫ J) (pB z))
    (E₁ : TA ≃ I × ℂ) (E₂ : TB ≃ K × ℂ)
    (b : I → ℂ) (b' : K → ℂ) (hb : Function.Injective b) (hb' : Function.Injective b')
    (e : I ≃ K) (he : ∀ i, b' (e i) = b i)
    (hq₁ : ∀ z, ComplexPoint.affineSpecEquiv A (pA z) q = b (E₁ z).1)
    (ht₁ : ∀ z, ComplexPoint.affineSpecEquiv A (pA z) t = (E₁ z).2)
    (hq₂ : ∀ z, ComplexPoint.affineSpecEquiv B (pB z) q' = b' (E₂ z).1)
    (hs₂ : ∀ z, ComplexPoint.affineSpecEquiv B (pB z) s = 0 ↔ (E₂ z).2 = 0)
    (hoverlap : ∀ z, (H₂ z).val ∈ U ↔ ComplexPoint.affineSpecEquiv B (pB z) s ≠ 0) :
    ∃ (E : ComplexPoint F ≃ I × OnePoint ℂ) (j : I → (projectiveLine ⟶ F)),
      (∀ i, IsClosedImmersion (j i).left) ∧
      (∀ z : ComplexPoint F, ∃! i, z ∈ Set.range (Point.map (j i))) ∧
      (∀ i y, E (Point.map (j i) y) = (i, lineCoordinate y)) ∧
      (∀ z, ComplexPoint.affineSpecEquiv (Polynomial ℂ) (Point.map (l ≫ Q) z) Polynomial.X =
        b (E z).1 ∧ lineCoordinate (Point.map (l ≫ T) z) = (E z).2) ∧
      (∀ z : TA, E (H₁ z).val = ((E₁ z).1, ((E₁ z).2 : OnePoint ℂ))) := by
  have hLA (z) : Point.map l (H₁ z).val = Point.map JA (pA z) := by
    apply (cancel_mono J).mp
    change Point.map J (Point.map l (H₁ z).val) = Point.map J (Point.map JA (pA z))
    rw [← Point.map_comp_apply, hl, ← Point.map_comp_apply]
    exact hH₁ z
  have hLB (z) : Point.map l (H₂ z).val = Point.map JB (pB z) := by
    apply (cancel_mono J).mp
    change Point.map J (Point.map l (H₂ z).val) = Point.map J (Point.map JB (pB z))
    rw [← Point.map_comp_apply, hl, ← Point.map_comp_apply]
    exact hH₂ z
  have hQ₁ (z) : ComplexPoint.affineSpecEquiv (Polynomial ℂ)
      (Point.map (l ≫ Q) (H₁ z).val) Polynomial.X = b (E₁ z).1 := by
    rw [Point.map_comp_apply, hLA, ← Point.map_comp_apply, hQA, affineLineParameter_coordinate]
    exact hq₁ z
  have hQ₂ (z) : ComplexPoint.affineSpecEquiv (Polynomial ℂ)
      (Point.map (l ≫ Q) (H₂ z).val) Polynomial.X = b' (E₂ z).1 := by
    rw [Point.map_comp_apply, hLB, ← Point.map_comp_apply, hQB, affineLineParameter_coordinate]
    exact hq₂ z
  have hR₁ (z) : lineCoordinate (Point.map (l ≫ T) (H₁ z).val) = ((E₁ z).2 : OnePoint ℂ) := by
    rw [Point.map_comp_apply, hLA, ← Point.map_comp_apply, hTA,
      projectiveLineChart_finite_coordinate, ht₁]
  have hR₂ (z) : lineCoordinate (Point.map (l ≫ T) (H₂ z).val) = ∞ ↔ (E₂ z).2 = 0 := by
    rw [Point.map_comp_apply, hLB, ← Point.map_comp_apply, hTB,
      projectiveLineChart_reciprocal_coordinate]
    by_cases hz : ComplexPoint.affineSpecEquiv B (pB z) s = 0
    · simp only [hz, ite_true, true_iff]
      exact (hs₂ z).mp hz
    · simp only [hz, ite_false, OnePoint.coe_ne_infty, false_iff]
      exact fun h => hz ((hs₂ z).mpr h)
  have hU (z) : z ∈ U ↔ lineCoordinate (Point.map (l ≫ T) z) ≠ ∞ := by
    constructor
    · intro hz
      obtain ⟨w, hw⟩ := H₁.surjective ⟨z, hz⟩
      have he : (H₁ w).val = z := congrArg Subtype.val hw
      rw [← he, hR₁]
      exact OnePoint.coe_ne_infty _
    · intro hz
      rcases hcover z with hu | hv
      · exact hu
      · let w := H₂.symm ⟨z, hv⟩
        have hw : (H₂ w).val = z := congrArg Subtype.val (H₂.apply_symm_apply ⟨z, hv⟩)
        rw [← hw]
        apply (hoverlap w).mpr
        intro hs
        exact hz (hw ▸ (hR₂ w).mpr ((hs₂ w).mp hs))
  obtain ⟨E, j, hj, hex, hjE, hE, hfirst⟩ := classified_reciprocal_sections F (l ≫ Q) (l ≫ T) U V hcover
    (H₁.symm.trans E₁) (H₂.symm.trans E₂) b b' hb hb' e he hU
    (by
      intro z
      have hh := hQ₁ (H₁.symm z)
      rw [H₁.apply_symm_apply] at hh
      exact hh)
    (by
      intro z
      have hh := hR₁ (H₁.symm z)
      rw [H₁.apply_symm_apply] at hh
      exact hh)
    (by
      intro z
      have hh := hQ₂ (H₂.symm z)
      rw [H₂.apply_symm_apply] at hh
      exact hh)
    (by
      intro z
      have hh := hR₂ (H₂.symm z)
      rw [H₂.apply_symm_apply] at hh
      exact hh)
  refine ⟨E, j, hj, hex, hjE, hE, ?_⟩
  intro z
  simpa only [Equiv.trans_apply, H₁.symm_apply_apply] using hfirst (H₁ z)

end AlgebraicGeometry.RamifiedNormalization.StageFour
