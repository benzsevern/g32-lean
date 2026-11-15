import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.ReciprocalLabelledCompletion
import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.LabelledProjectiveSections
import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.AffineLineParameterFibres

noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory
open scoped OnePoint
namespace AlgebraicGeometry.RamifiedNormalization.StageFour

/-- The two classified actual chart loci retain all projective component sections and their global selector and sphere coordinates. -/
theorem classified_reciprocal_sections
    {I J : Type} (F : Over (Spec ↧ℂ)) [IsProper F.hom]
    (Q : F ⟶ Over.mk (ComplexPoint.affineSpecStructureMap (Polynomial ℂ)))
    (R : F ⟶ projectiveLine)
    (U V : Set (ComplexPoint F)) (hcover : ∀ z, z ∈ U ∨ z ∈ V)
    (E₁ : U ≃ I × ℂ) (E₂ : V ≃ J × ℂ)
    (b : I → ℂ) (b' : J → ℂ) (hb : Function.Injective b) (hb' : Function.Injective b')
    (e : I ≃ J) (he : ∀ i, b' (e i) = b i)
    (hU : ∀ z, z ∈ U ↔ lineCoordinate (Point.map R z) ≠ ∞)
    (hq₁ : ∀ z : U, ComplexPoint.affineSpecEquiv (Polynomial ℂ) (Point.map Q z.val)
      Polynomial.X = b (E₁ z).1)
    (hr₁ : ∀ z : U, lineCoordinate (Point.map R z.val) = ((E₁ z).2 : OnePoint ℂ))
    (hq₂ : ∀ z : V, ComplexPoint.affineSpecEquiv (Polynomial ℂ) (Point.map Q z.val)
      Polynomial.X = b' (E₂ z).1)
    (hr₂ : ∀ z : V, lineCoordinate (Point.map R z.val) = ∞ ↔ (E₂ z).2 = 0) :
    ∃ (E : ComplexPoint F ≃ I × OnePoint ℂ) (j : I → (projectiveLine ⟶ F)),
      (∀ i, IsClosedImmersion (j i).left) ∧
      (∀ z : ComplexPoint F, ∃! i, z ∈ Set.range (Point.map (j i))) ∧
      (∀ i y, E (Point.map (j i) y) = (i, lineCoordinate y)) ∧
      (∀ z, ComplexPoint.affineSpecEquiv (Polynomial ℂ) (Point.map Q z) Polynomial.X =
        b (E z).1 ∧ lineCoordinate (Point.map R z) = (E z).2) ∧
      (∀ z : U, E z.val = ((E₁ z).1, ((E₁ z).2 : OnePoint ℂ))) := by
  let q : ComplexPoint F → ℂ := fun z =>
    ComplexPoint.affineSpecEquiv (Polynomial ℂ) (Point.map Q z) Polynomial.X
  let r : ComplexPoint F → OnePoint ℂ := fun z => lineCoordinate (Point.map R z)
  let c : J × ℂ → ComplexPoint F := fun z => (E₂.symm z).val
  have hc : Function.Injective c := Subtype.val_injective.comp E₂.symm.injective
  have hqc (i : J) (a : ℂ) : q (c (i, a)) = b' i := by
    exact (hq₂ (E₂.symm (i, a))).trans (congrArg (fun z : J × ℂ => b' z.1)
      (E₂.apply_symm_apply (i, a)))
  have hrc (i : J) (a : ℂ) : r (c (i, a)) = ∞ ↔ a = 0 := by
    simpa only [E₂.apply_symm_apply] using hr₂ (E₂.symm (i, a))
  have hcov (z : ComplexPoint F) (hz : r z = ∞) : z ∈ Set.range c := by
    have hzU : z ∉ U := fun h => (hU z).mp h hz
    have hzV : z ∈ V := (hcover z).resolve_left hzU
    exact ⟨E₂ ⟨z, hzV⟩, congrArg Subtype.val (E₂.symm_apply_apply ⟨z, hzV⟩)⟩
  obtain ⟨E, hE⟩ := reciprocal_labelled_completion U q r b b' hb hb' e he E₁ hU hq₁ hr₁
    c hc hqc hrc hcov
  let C := Over.mk (ComplexPoint.affineSpecStructureMap (Polynomial ℂ))
  haveI : IsSeparated C.hom := by
    change IsSeparated (Spec.map (CommRingCat.ofHom (algebraMap ℂ (Polynomial ℂ))))
    infer_instance
  let bP : I → ComplexPoint C := fun i =>
    (ComplexPoint.affineSpecEquiv (Polynomial ℂ)).symm (Polynomial.aeval (b i))
  have hbP : Function.Injective bP := by
    intro i j h
    apply hb
    have hh := congrArg (fun p => ComplexPoint.affineSpecEquiv (Polynomial ℂ) p Polynomial.X) h
    simpa only [bP, Equiv.apply_symm_apply, Polynomial.aeval_X] using hh
  have hqP (z) : Point.map Q z = bP (E z).1 := by
    apply (ComplexPoint.affineSpecEquiv (Polynomial ℂ)).injective
    rw [Equiv.apply_symm_apply]
    apply Polynomial.algHom_ext
    rw [Polynomial.aeval_X]
    exact (hE z).1
  obtain ⟨j, hj, hex, hjE⟩ := labelled_projective_sections F C Q R bP hbP E hqP
    (fun z => (hE z).2)
  refine ⟨E, j, hj, hex, hjE, hE, ?_⟩
  intro z
  apply Prod.ext
  · exact hb ((hE z.val).1.symm.trans (hq₁ z))
  · exact (hE z.val).2.symm.trans (hr₁ z)

end AlgebraicGeometry.RamifiedNormalization.StageFour
