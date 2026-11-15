import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.RetainedModelInclusion

noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory
open HodgeLean.Foundations.Program
namespace AlgebraicGeometry.RamifiedNormalization.StageFour

/-- The selected actual fibre is homeomorphic to the fibre of its retained affine blowup model. -/
theorem retained_model_point_fibre_homeomorph
    (B X : Over (Spec ↧ℂ)) (p : X ⟶ B) (U : B.left.affineOpens)
    (M : Scheme) (π : M ⟶ Spec Γ(B.left, U))
    (e : (p.left ⁻¹ᵁ U.1).toScheme ≅ M)
    (he : e.hom ≫ π ≫ U.2.fromSpec = (p.left ⁻¹ᵁ U.1).ι ≫ p.left)
    (x : ComplexPoint B) (hx : x.left (IsLocalRing.closedPoint ℂ) ∈ U.1) :
    letI := s2e_step1_sectionAlgebra B U.1
    let Mover := Over.mk (π ≫ ComplexPoint.affineSpecStructureMap Γ(B.left, U))
    let q : Mover ⟶ Over.mk (ComplexPoint.affineSpecStructureMap Γ(B.left, U)) := Over.homMk π rfl
    ∃ (xR : ComplexPoint (Over.mk (ComplexPoint.affineSpecStructureMap Γ(B.left, U))))
      (i : Mover ⟶ X)
      (H : {z : ComplexPoint Mover // Point.map q z = xR} ≃ₜ
        {z : ComplexPoint X // Point.map p z = x}),
      i.left = e.inv ≫ (p.left ⁻¹ᵁ U.1).ι ∧
      Point.map (s2e_u1_fromSpecOver B U.1 U.2) xR = x ∧
      ∀ z, (H z).val = Point.map i z.val := by
  letI := s2e_step1_sectionAlgebra B U.1
  let a := s2e_u1_fromSpecOver B U.1 U.2
  haveI : IsOpenImmersion a.left := by
    change IsOpenImmersion U.2.fromSpec
    infer_instance
  have hxa : x.left (IsLocalRing.closedPoint ℂ) ∈ Set.range a.left := by
    change x.left (IsLocalRing.closedPoint ℂ) ∈ Set.range U.2.fromSpec
    rw [U.2.range_fromSpec]
    exact hx
  obtain ⟨xR, hxR⟩ := complex_point_lifts_open_chart a x hxa
  obtain ⟨i, hi, hio, hsq, hrange⟩ := retained_model_open_inclusion B X p U M π e he
  letI : IsOpenImmersion i.left := hio
  let q : Over.mk (π ≫ ComplexPoint.affineSpecStructureMap Γ(B.left, U)) ⟶
      Over.mk (ComplexPoint.affineSpecStructureMap Γ(B.left, U)) := Over.homMk π rfl
  have hcover (z : ComplexPoint X) (hz : Point.map p z = Point.map a xR) :
      z.left (IsLocalRing.closedPoint ℂ) ∈ Set.range i.left := by
    rw [hrange]
    change p.left (z.left (IsLocalRing.closedPoint ℂ)) ∈ U.1
    have hpz := hz.trans hxR
    have hpz' := congrArg (fun t : ComplexPoint B => t.left (IsLocalRing.closedPoint ℂ)) hpz
    change p.left (z.left (IsLocalRing.closedPoint ℂ)) = x.left (IsLocalRing.closedPoint ℂ) at hpz'
    rw [hpz']
    exact hx
  obtain ⟨H, hH⟩ := open_chart_point_fibre_homeomorph p q i a hsq xR hcover
  let E : {z : ComplexPoint X // Point.map p z = Point.map a xR} ≃ₜ
      {z : ComplexPoint X // Point.map p z = x} :=
    (Homeomorph.refl _).subtype (fun z => by rw [hxR]; rfl)
  refine ⟨xR, i, H.trans E, hi, hxR, ?_⟩
  exact fun z => hH z

end AlgebraicGeometry.RamifiedNormalization.StageFour
