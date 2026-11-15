import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.ActualReciprocalChartSections
import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.ClassifiedSphereEndpoints

noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory
open scoped OnePoint
namespace AlgebraicGeometry.RamifiedNormalization.StageFour

/-- The actual reciprocal chart classifications and finite power projection retain all projective component sections with both specified scalar endpoints. -/
theorem actual_reciprocal_endpoint_sections
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
    (hoverlap : ∀ z, (H₂ z).val ∈ U ↔ ComplexPoint.affineSpecEquiv B (pB z) s ≠ 0)
    (v : ComplexPoint F → OnePoint ℂ) (k : I → ℂ) (hk : ∀ i, k i ≠ 0)
    (n : ℕ) (hn : 0 < n)
    (hvU : ∀ z, z ∈ U ↔ v z ≠ (∞ : OnePoint ℂ))
    (hvfirst : ∀ z, v (H₁ z).val = ((k (E₁ z).1 * (E₁ z).2 ^ n : ℂ) : OnePoint ℂ)) :
    ∃ j : I → (projectiveLine ⟶ F),
      (∀ i, IsClosedImmersion (j i).left) ∧
      (∀ z : ComplexPoint F, ∃! i, z ∈ Set.range (Point.map (j i))) ∧
      (∀ i y, v (Point.map (j i) y) = ((0 : ℂ) : OnePoint ℂ) ↔ lineCoordinate y = ((0 : ℂ) : OnePoint ℂ)) ∧
      (∀ i y, v (Point.map (j i) y) = (∞ : OnePoint ℂ) ↔ lineCoordinate y = (∞ : OnePoint ℂ)) ∧
      (∀ i, v (Point.map (j i) (lineCoordinate.symm ((0 : ℂ) : OnePoint ℂ))) = ((0 : ℂ) : OnePoint ℂ)) ∧
      (∀ i, v (Point.map (j i) (lineCoordinate.symm (∞ : OnePoint ℂ))) = (∞ : OnePoint ℂ)) := by
  obtain ⟨E, j, hj, hex, hjE, hglobal, hfirst⟩ := actual_reciprocal_chart_sections
    F N W J l a hl JA JB Q T q t q' s hQA hQB hTA hTB U V hcover H₁ H₂ pA pB hH₁ hH₂
    E₁ E₂ b b' hb hb' e he hq₁ ht₁ hq₂ hs₂ hoverlap
  have hends := classified_sphere_endpoints U H₁ E₁ E v k hk n hn hfirst hvU hvfirst
  refine ⟨j, hj, hex, ?_, ?_, ?_, ?_⟩
  · intro i y
    have hh := hends (Point.map (j i) y)
    rw [hjE i y] at hh
    exact hh.1
  · intro i y
    have hh := hends (Point.map (j i) y)
    rw [hjE i y] at hh
    exact hh.2
  · intro i
    apply (hends _).1.mpr
    rw [hjE, lineCoordinate.apply_symm_apply]
  · intro i
    apply (hends _).2.mpr
    rw [hjE, lineCoordinate.apply_symm_apply]

end AlgebraicGeometry.RamifiedNormalization.StageFour
