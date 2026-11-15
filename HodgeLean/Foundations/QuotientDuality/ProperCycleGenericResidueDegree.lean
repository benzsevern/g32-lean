import HodgeLean.Foundations.QuotientDuality.ProperCycleDefs

/-! # Actual generic residue degrees and the specified function-field embedding -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry
open HodgeLean.Adapters
namespace HodgeLean.Foundations.QuotientDuality

/-- The actual generic residue degree is the degree of the specified generic-stalk field embedding.
Source: Hartshorne, Algebraic Geometry, II.3, generic residue fields; Fulton, Intersection Theory, section 1.4.
HC no distance; AV milestone no distance. -/
lemma properCycle_generic_residue_degree_eq_functionField_degree
    {X Y : Over (Spec ↧ℂ)} [IsIntegral X.left] [IsIntegral Y.left]
    (f : X ⟶ Y) (hg : f.left (genericPoint X.left) = genericPoint Y.left) :
    let φ := (eqToHom (congrArg Y.left.presheaf.stalk hg.symm) ≫
      f.left.stalkMap (genericPoint X.left)).hom
    letI := φ.toAlgebra
    a1p_degree f.left (genericPoint X.left) =
      Module.finrank Y.left.functionField X.left.functionField := by
  let φ := (eqToHom (congrArg Y.left.presheaf.stalk hg.symm) ≫
    f.left.stalkMap (genericPoint X.left)).hom
  letI := φ.toAlgebra
  letI := (f.left.residueFieldMap (genericPoint X.left)).hom.toAlgebra
  let rY : Y.left.functionField ⟶ Y.left.residueField (f.left (genericPoint X.left)) :=
    eqToHom (congrArg Y.left.presheaf.stalk hg.symm) ≫ Y.left.residue _
  have hrY : Function.Surjective rY :=
    (Y.left.residue_surjective _).comp
      (ConcreteCategory.bijective_of_isIso (eqToHom (congrArg Y.left.presheaf.stalk hg.symm))).2
  let eY := RingEquiv.ofBijective rY.hom ⟨rY.hom.injective, hrY⟩
  let eX := RingEquiv.ofBijective (X.left.residue (genericPoint X.left)).hom
    ⟨(X.left.residue (genericPoint X.left)).hom.injective, X.left.residue_surjective _⟩
  have hsquare : (eqToHom (congrArg Y.left.presheaf.stalk hg.symm) ≫
      f.left.stalkMap (genericPoint X.left)) ≫ X.left.residue (genericPoint X.left) =
      rY ≫ f.left.residueFieldMap (genericPoint X.left) := by
    simp only [rY, Category.assoc, Scheme.residue_residueFieldMap]
  have heq := Algebra.finrank_eq_of_equiv_equiv eY eX (by
    ext a
    exact (ConcreteCategory.congr_hom hsquare a).symm)
  exact heq.symm

end HodgeLean.Foundations.QuotientDuality
