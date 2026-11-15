import HodgeLean.Foundations.Program.SchoenTransferQ3CoordinateMorphisms

/-! The actual tangential coordinate square on an algebraic support neighbourhood. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
namespace HodgeLean.Foundations.Program

/-- The lifted ambient tangential morphism restricts to the specified etale
coordinate morphism on a common support neighbourhood. -/
theorem s4_q3_support_coordinate_square
    {D W : Over (Spec ↧ℂ)} (r : ℕ) [SmoothOfRelativeDimension r D.hom]
    (j : D ⟶ W) [IsClosedImmersion j.left] (x : D.left) :
    let E := AlgebraicGeometry.localEtaleCoordinates D r x
    ∃ (U : W.left.Opens) (_ : IsAffineOpen U) (_ : j.left x ∈ U)
      (g : Fin r → Γ(W.left, U)) (V : D.left.Opens) (_ : x ∈ V)
      (hVU : V ≤ j.left ⁻¹ᵁ U) (hVE : V ≤ E.neighborhood),
      j.left.resLE U V hVU ≫ s4_q3_tangentialCoordinateMorphism W U r g =
        D.left.homOfLE hVE ≫ E.toAffineSpace := by
  let E := AlgebraicGeometry.localEtaleCoordinates D r x
  obtain ⟨U, hU, hxU, g, V, hxV, hVU, hVE, hg⟩ :=
    s4_q3_support_coordinates_algebraic_agreement r j x
  refine ⟨U, hU, hxU, g, V, hxV, hVU, hVE, ?_⟩
  rw [s4_q3_tangentialCoordinateMorphism_resLE]
  have heq : (fun i => D.left.presheaf.map (homOfLE hVU).op (j.left.app U (g i))) =
      (fun i => D.left.presheaf.map (homOfLE hVE).op (E.coordinateAlgHom (MvPolynomial.X i))) :=
    funext hg
  rw [heq]
  have hid := s4_q3_tangentialCoordinateMorphism_resLE (𝟙 D) E.neighborhood V
    (show V ≤ (𝟙 D : D ⟶ D).left ⁻¹ᵁ E.neighborhood from hVE) r
    (fun i => E.coordinateAlgHom (MvPolynomial.X i))
  simp only [Over.id_left, Scheme.Hom.resLE_id, Scheme.Hom.id_app,
    CommRingCat.id_apply] at hid
  rw [s4_q3_tangentialCoordinateMorphism_etale_coordinates D r x] at hid
  exact hid.symm

/-- The actual support restriction of the lifted ambient coordinate morphism
is etale on the constructed nonempty Zariski neighbourhood. -/
theorem s4_q3_support_coordinate_square_etale
    {D W : Over (Spec ↧ℂ)} (r : ℕ) [SmoothOfRelativeDimension r D.hom]
    (j : D ⟶ W) [IsClosedImmersion j.left] (x : D.left) :
    ∃ (U : W.left.Opens) (_ : IsAffineOpen U) (_ : j.left x ∈ U)
      (g : Fin r → Γ(W.left, U)) (V : D.left.Opens) (_ : x ∈ V)
      (hVU : V ≤ j.left ⁻¹ᵁ U),
      Etale (j.left.resLE U V hVU ≫ s4_q3_tangentialCoordinateMorphism W U r g) := by
  obtain ⟨U, hU, hxU, g, V, hxV, hVU, hVE, heq⟩ := s4_q3_support_coordinate_square r j x
  refine ⟨U, hU, hxU, g, V, hxV, hVU, ?_⟩
  rw [heq]
  letI := s4_q3_support_coordinateMorphism_etale D r x
  infer_instance

end HodgeLean.Foundations.Program
