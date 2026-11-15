import HodgeLean.Foundations.Program.SchoenCycleU1AffineChartNaturality
import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.OpenFibreComparison

noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory
open HodgeLean.Foundations.Program
namespace AlgebraicGeometry.RamifiedNormalization.StageFour

/-- The retained blowup comparison gives an actual complex open model inclusion and its base square. -/
theorem retained_model_open_inclusion
    (B X : Over (Spec ↧ℂ)) (p : X ⟶ B) (U : B.left.affineOpens)
    (M : Scheme) (π : M ⟶ Spec Γ(B.left, U))
    (e : (p.left ⁻¹ᵁ U.1).toScheme ≅ M)
    (he : e.hom ≫ π ≫ U.2.fromSpec = (p.left ⁻¹ᵁ U.1).ι ≫ p.left) :
    letI := s2e_step1_sectionAlgebra B U.1
    ∃ i : Over.mk (π ≫ ComplexPoint.affineSpecStructureMap Γ(B.left, U)) ⟶ X,
      i.left = e.inv ≫ (p.left ⁻¹ᵁ U.1).ι ∧ IsOpenImmersion i.left ∧
      i ≫ p = Over.homMk π rfl ≫ s2e_u1_fromSpecOver B U.1 U.2 ∧
      Set.range i.left = (p.left ⁻¹ᵁ U.1 : Set X.left) := by
  letI := s2e_step1_sectionAlgebra B U.1
  let a := s2e_u1_fromSpecOver B U.1 U.2
  have hei : (e.inv ≫ (p.left ⁻¹ᵁ U.1).ι) ≫ p.left = π ≫ U.2.fromSpec := by
    rw [Category.assoc, ← he]
    simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  let i : Over.mk (π ≫ ComplexPoint.affineSpecStructureMap Γ(B.left, U)) ⟶ X :=
    Over.homMk (e.inv ≫ (p.left ⁻¹ᵁ U.1).ι) (by
      change (e.inv ≫ (p.left ⁻¹ᵁ U.1).ι) ≫ X.hom =
        π ≫ ComplexPoint.affineSpecStructureMap Γ(B.left, U)
      rw [← p.w, ← Category.assoc, hei, Category.assoc]
      exact congrArg (fun f => π ≫ f) a.w)
  refine ⟨i, rfl, ?_, ?_, ?_⟩
  · change IsOpenImmersion (e.inv ≫ (p.left ⁻¹ᵁ U.1).ι)
    infer_instance
  · apply Over.OverMorphism.ext
    exact hei
  · have hesurj : Function.Surjective e.inv := by
      intro z
      exact ⟨e.hom z, congrArg (fun f : (p.left ⁻¹ᵁ U.1).toScheme ⟶
        (p.left ⁻¹ᵁ U.1).toScheme => f z) e.hom_inv_id⟩
    change Set.range ((p.left ⁻¹ᵁ U.1).ι ∘ e.inv) = _
    rw [Set.range_comp, hesurj.range_eq, Set.image_univ, Scheme.Opens.range_ι]

end AlgebraicGeometry.RamifiedNormalization.StageFour
