import HodgeLean.Foundations.QuotientDuality.ProperCycleGenericResidueDegree

/-! # Actual residue degrees through open immersions -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry HodgeLean.Adapters
namespace HodgeLean.Foundations.QuotientDuality

/-- Restricting the source by an actual open immersion preserves the original residue-field degree at the specified point.
Source: Fulton, Intersection Theory, section 1.4; Mathlib, AlgebraicGeometry/ResidueField.lean, residue-field isomorphisms of open immersions.
HC no distance; AV milestone no distance. -/
lemma properCycle_degree_precompose_open_immersion
    {X' X Y : Scheme.{0}} (i : X' ⟶ X) [IsOpenImmersion i] (f : X ⟶ Y) (x : X') :
    a1p_degree (i ≫ f) x = a1p_degree f (i x) := by
  let φ : Y.residueField (f (i x)) ⟶ X'.residueField x := (i ≫ f).residueFieldMap x
  letI := φ.hom.toAlgebra
  letI := (f.residueFieldMap (i x)).hom.toAlgebra
  let e := RingEquiv.ofBijective (i.residueFieldMap x).hom
    (ConcreteCategory.bijective_of_isIso (i.residueFieldMap x))
  have h := Algebra.finrank_eq_of_equiv_equiv
    (RingEquiv.refl (Y.residueField (f (i x)))) e (by
      ext a
      exact ConcreteCategory.congr_hom (Scheme.residueFieldMap_comp i f x) a)
  exact h.symm

/-- Composing the target with an actual open immersion preserves the original residue-field degree at the specified point.
Source: Fulton, Intersection Theory, section 1.4; Mathlib, AlgebraicGeometry/ResidueField.lean, residue-field isomorphisms of open immersions.
HC no distance; AV milestone no distance. -/
lemma properCycle_degree_postcompose_open_immersion
    {X Y Y' : Scheme.{0}} (f : X ⟶ Y) (i : Y ⟶ Y') [IsOpenImmersion i] (x : X) :
    a1p_degree (f ≫ i) x = a1p_degree f x := by
  let φ : Y'.residueField (i (f x)) ⟶ X.residueField x := (f ≫ i).residueFieldMap x
  letI := φ.hom.toAlgebra
  letI := (f.residueFieldMap x).hom.toAlgebra
  let e := RingEquiv.ofBijective (i.residueFieldMap (f x)).hom
    (ConcreteCategory.bijective_of_isIso (i.residueFieldMap (f x)))
  have h := Algebra.finrank_eq_of_equiv_equiv e (RingEquiv.refl (X.residueField x)) (by
    ext a
    exact (ConcreteCategory.congr_hom (Scheme.residueFieldMap_comp f i x) a).symm)
  exact h

/-- An actual commuting square of source and target open immersions retains the original residue-field degree at every source point.
Source: Fulton, Intersection Theory, section 1.4; Mathlib, AlgebraicGeometry/ResidueField.lean, functoriality and open-immersion residue maps.
HC no distance; AV milestone no distance. -/
lemma properCycle_degree_open_square
    {X' X Y' Y : Scheme.{0}} (g : X' ⟶ Y') (f : X ⟶ Y)
    (iX : X' ⟶ X) (iY : Y' ⟶ Y) [IsOpenImmersion iX] [IsOpenImmersion iY]
    (hsquare : g ≫ iY = iX ≫ f) (x : X') :
    a1p_degree g x = a1p_degree f (iX x) := by
  have h := congrArg (fun h => a1p_degree h x) hsquare
  rw [properCycle_degree_postcompose_open_immersion,
    properCycle_degree_precompose_open_immersion] at h
  exact h

/-- Restricting the original morphism to an actual target open retains its actual residue degree at every restricted source point.
Source: Fulton, Intersection Theory, section 1.4; Mathlib, AlgebraicGeometry/Restrict.lean, morphismRestrict_ι.
HC no distance; AV milestone no distance. -/
lemma properCycle_degree_target_open_restriction
    {X Y : Scheme.{0}} (f : X ⟶ Y) (U : Y.Opens) (x : (f ⁻¹ᵁ U).toScheme) :
    a1p_degree (f ∣_ U) x = a1p_degree f ((f ⁻¹ᵁ U).ι x) :=
  properCycle_degree_open_square (f ∣_ U) f (f ⁻¹ᵁ U).ι U.ι (morphismRestrict_ι f U) x

end HodgeLean.Foundations.QuotientDuality
