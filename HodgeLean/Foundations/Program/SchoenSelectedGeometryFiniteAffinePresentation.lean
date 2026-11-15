import HodgeLean.Foundations.Program.SchoenSelectedGeometryLineSpecSmooth

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint ComplexAlgHom
namespace HodgeLean.Foundations.Program

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- A finite flat map from an integral scheme to an affine line has a compatible affine algebra presentation. -/
theorem s0_finite_flat_line_affine_presentation
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left]
    (q : X ⟶ Over.mk (affineSpecStructureMap (complexPolynomialRing 1)))
    [IsFinite q.left] [Flat q.left] :
    ∃ (S : Type) (_ : CommRing S) (_ : IsDomain S) (_ : Algebra ℂ S)
      (_ : Algebra (complexPolynomialRing 1) S)
      (_ : IsScalarTower ℂ (complexPolynomialRing 1) S)
      (_ : Module.Finite (complexPolynomialRing 1) S)
      (_ : Module.Flat (complexPolynomialRing 1) S)
      (_ : Algebra.FinitePresentation ℂ S),
      ∃ e : X ≅ Over.mk (affineSpecStructureMap S),
        e.inv.left ≫ q.left = Spec.map (CommRingCat.ofHom
          (algebraMap (complexPolynomialRing 1) S)) := by
  let A := complexPolynomialRing 1
  letI : IsAffine (Over.mk (affineSpecStructureMap A)).left := inferInstanceAs (IsAffine (Spec ↧A))
  letI : IsAffine X.left := isAffine_of_isAffineHom q.left
  let S := Γ(X.left, ⊤)
  let e := X.left.isoSpec
  let ψ : A →+* S := (Spec.preimage (e.inv ≫ q.left)).hom
  letI : Algebra A S := ψ.toAlgebra
  letI : Algebra ℂ S := (ψ.comp (algebraMap ℂ A)).toAlgebra
  letI : IsScalarTower ℂ A S := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have hψ : Spec.map (CommRingCat.ofHom ψ) = e.inv ≫ q.left := Spec.map_preimage _
  have hsf : IsFinite (Spec.map (CommRingCat.ofHom ψ)) := by
    rw [hψ]
    infer_instance
  have hfin : ψ.Finite := (IsFinite.SpecMap_iff _).mp hsf
  letI : Module.Finite A S := hfin
  have hfl : Flat (Spec.map (CommRingCat.ofHom ψ)) := by
    rw [hψ]
    infer_instance
  have hflat : ψ.Flat := (HasRingHomProperty.Spec_iff (P := @Flat)).mp hfl
  letI : Module.Flat A S := hflat
  letI : Algebra.FiniteType ℂ S := Algebra.FiniteType.trans
    (inferInstance : Algebra.FiniteType ℂ A) (inferInstance : Algebra.FiniteType A S)
  letI : Algebra.FinitePresentation ℂ S := Algebra.FinitePresentation.of_finiteType.mp inferInstance
  have he : e.hom ≫ affineSpecStructureMap S = X.hom := by
    change e.hom ≫ Spec.map (CommRingCat.ofHom (ψ.comp (algebraMap ℂ A))) = _
    rw [show CommRingCat.ofHom (ψ.comp (algebraMap ℂ A)) =
      CommRingCat.ofHom (algebraMap ℂ A) ≫ CommRingCat.ofHom ψ from rfl,
      Spec.map_comp, hψ, ← Category.assoc, e.hom_inv_id_assoc]
    exact Over.w q
  exact ⟨S, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, Over.isoMk e he, hψ.symm⟩

#print axioms s0_finite_flat_line_affine_presentation
end HodgeLean.Foundations.Program
