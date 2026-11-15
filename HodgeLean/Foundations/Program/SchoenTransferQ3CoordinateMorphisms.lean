import HodgeLean.Foundations.Program.SchoenTransferQ3AlgebraicCoordinates

/-! The actual ambient morphisms specified by tangential regular sections. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
namespace HodgeLean.Foundations.Program

/-- The ambient morphism to affine space defined by the original regular
sections, retaining the given structure morphism over the complex numbers. -/
def s4_q3_tangentialCoordinateMorphism
    (W : Over (Spec ↧ℂ)) (U : W.left.Opens) (r : ℕ) (g : Fin r → Γ(W.left, U)) :
    U.toScheme ⟶ ComplexPoint.complexAffineSpace (Fin r) :=
  AffineSpace.homOfVector (U.ι ≫ W.hom) (fun i => U.topIso.inv (g i))

/-- The constructed coordinate morphism is over the original complex base. -/
theorem s4_q3_tangentialCoordinateMorphism_over
    (W : Over (Spec ↧ℂ)) (U : W.left.Opens) (r : ℕ) (g : Fin r → Γ(W.left, U)) :
    s4_q3_tangentialCoordinateMorphism W U r g ≫
      (ComplexPoint.complexAffineSpace (Fin r) ↘ Spec ↧ℂ) = U.ι ≫ W.hom :=
  AffineSpace.homOfVector_over _ _

/-- The standard affine coordinates pull back to the original ambient
regular sections, with the actual open-subscheme section identification. -/
theorem s4_q3_tangentialCoordinateMorphism_coordinate
    (W : Over (Spec ↧ℂ)) (U : W.left.Opens) (r : ℕ) (g : Fin r → Γ(W.left, U))
    (i : Fin r) :
    (s4_q3_tangentialCoordinateMorphism W U r g).appTop
      (AffineSpace.coord (Spec ↧ℂ) i) = U.topIso.inv (g i) :=
  AffineSpace.homOfVector_appTop_coord _ _ _

/-- The constructed support coordinate morphism is the specified etale
coordinate morphism from the smooth-coordinate construction. -/
theorem s4_q3_tangentialCoordinateMorphism_etale_coordinates
    (D : Over (Spec ↧ℂ)) (r : ℕ) [SmoothOfRelativeDimension r D.hom]
    (x : D.left) :
    let E := AlgebraicGeometry.localEtaleCoordinates D r x
    s4_q3_tangentialCoordinateMorphism D E.neighborhood r
      (fun i => E.coordinateAlgHom (MvPolynomial.X i)) = E.toAffineSpace := by
  let E := AlgebraicGeometry.localEtaleCoordinates D r x
  apply AffineSpace.hom_ext
  · exact (s4_q3_tangentialCoordinateMorphism_over D E.neighborhood r _).trans
      E.toAffineSpace_over.symm
  · intro i
    rw [s4_q3_tangentialCoordinateMorphism_coordinate]
    change E.coordinateRingHomOnOpen (MvPolynomial.X i) = _
    simp only [LocalEtaleCoordinates.toAffineSpace, Scheme.Hom.comp_appTop,
      CommRingCat.comp_apply]
    rw [AffineSpace.SpecIso_inv_appTop_coord]
    have h := ConcreteCategory.congr_hom
      (ΓSpecIso_inv_ΓSpec_adjunction_homEquiv
        (X := E.neighborhood.toScheme) (CommRingCat.ofHom E.coordinateRingHomOnOpen))
      (MvPolynomial.X i)
    have hh :
        (ΓSpec.adjunction.homEquiv E.neighborhood.toScheme
          (Opposite.op (CommRingCat.of (MvPolynomial (Fin r) ℂ))))
          (CommRingCat.ofHom E.coordinateRingHomOnOpen).op =
        E.neighborhood.toScheme.toSpecΓ ≫
          Spec.map (CommRingCat.ofHom E.coordinateRingHomOnOpen) := by
      rw [Adjunction.homEquiv_apply]
      rfl
    rw [hh] at h
    simpa only [Scheme.Hom.comp_appTop, ConcreteCategory.comp_apply,
      ConcreteCategory.hom_ofHom] using h.symm

/-- Restricting the actual ambient coordinate morphism along a support map
uses precisely the regular-section pullbacks of that support map. -/
theorem s4_q3_tangentialCoordinateMorphism_resLE
    {D W : Over (Spec ↧ℂ)} (j : D ⟶ W) (U : W.left.Opens)
    (V : D.left.Opens) (hVU : V ≤ j.left ⁻¹ᵁ U) (r : ℕ) (g : Fin r → Γ(W.left, U)) :
    j.left.resLE U V hVU ≫ s4_q3_tangentialCoordinateMorphism W U r g =
      s4_q3_tangentialCoordinateMorphism D V r
        (fun i => D.left.presheaf.map (homOfLE hVU).op (j.left.app U (g i))) := by
  apply AffineSpace.hom_ext
  · simp only [Category.assoc, s4_q3_tangentialCoordinateMorphism_over,
      Scheme.Hom.resLE_comp_ι_assoc, Over.w]
  · intro i
    rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
      s4_q3_tangentialCoordinateMorphism_coordinate,
      s4_q3_tangentialCoordinateMorphism_coordinate]
    change (j.left.resLE U V hVU).app ⊤ (U.topIso.inv (g i)) = _
    rw [Scheme.Hom.resLE_app_top]
    simp only [CommRingCat.comp_apply, Iso.inv_hom_id_apply]
    rfl

/-- The specified algebraic support-coordinate morphism is etale. -/
theorem s4_q3_support_coordinateMorphism_etale
    (D : Over (Spec ↧ℂ)) (r : ℕ) [SmoothOfRelativeDimension r D.hom]
    (x : D.left) :
    Etale (AlgebraicGeometry.localEtaleCoordinates D r x).toAffineSpace := by
  let E := AlgebraicGeometry.localEtaleCoordinates D r x
  letI : IsAffine E.neighborhood.toScheme := E.isAffine
  letI : Etale (Spec.map (CommRingCat.ofHom E.coordinateRingHomOnOpen)) :=
    (HasRingHomProperty.Spec_iff (P := @Etale)).mpr E.coordinateRingHomOnOpen_etale
  change Etale (E.neighborhood.toScheme.toSpecΓ ≫
    Spec.map (CommRingCat.ofHom E.coordinateRingHomOnOpen) ≫
      (AffineSpace.SpecIso (Fin r) (CommRingCat.of ℂ)).inv)
  infer_instance

end HodgeLean.Foundations.Program
