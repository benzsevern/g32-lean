import HodgeLean.Foundations.AlgebraicGeometry.ComplexTopology.Presentation
import HodgeConjecture.Mathlib.AlgebraicGeometry.Over.Basic
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-! Global-section coordinates on affine complex schemes.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint Topology
namespace HodgeLean.Foundations.ComplexTopology
attribute [local instance] overSpecAlgebra

set_option backward.isDefEq.respectTransparency false in
lemma affine_toSpec_over (X : Over (Spec ↧ℂ)) :
    X.left.toSpecΓ ≫ affineSpecStructureMap Γ(X.left, ⊤) = X.hom := by
  apply ext_to_Spec
  exact (ΓSpecIso_inv_ΓSpec_adjunction_homEquiv
    (CommRingCat.ofHom (algebraMap ℂ Γ(X.left, ⊤)))).trans (by
      change (Scheme.ΓSpecIso ↧ℂ).inv ≫ X.hom.appLE ⊤ ⊤ _ = _
      congr 1
      simp only [Scheme.Hom.appLE, Scheme.Γ_map_op, Scheme.Hom.appTop]
      rw [show (homOfLE (show (⊤ : X.left.Opens) ≤ X.hom ⁻¹ᵁ ⊤ by simp)).op = 𝟙 _ from Subsingleton.elim _ _]
      rw [CategoryTheory.Functor.map_id, Category.comp_id])

def affinePointModel (X : Over (Spec ↧ℂ)) [IsAffine X.left] :
    @Homeomorph (ComplexPoint X) (Γ(X.left, ⊤) →ₐ[ℂ] ℂ)
      Point.analyticTopology (affineAlgebraHomTopology Γ(X.left, ⊤)) :=
  let e : X ≅ Over.mk (affineSpecStructureMap Γ(X.left, ⊤)) :=
    Over.isoMk (asIso X.left.toSpecΓ) (affine_toSpec_over X)
  (Point.isoMapHomeomorph e).trans (affineSpecHomeomorph Γ(X.left, ⊤))

lemma affinePointModel_apply (X : Over (Spec ↧ℂ)) [IsAffine X.left]
    (z : ComplexPoint X) (r : Γ(X.left, ⊤)) :
    affinePointModel X z r = Point.evaluate ⊤ r z := by
  change affineSpecEquiv Γ(X.left, ⊤)
    (Point.map (Over.homMk X.left.toSpecΓ (affine_toSpec_over X)) z) r = _
  rw [affineSpecEquiv_apply, Point.evaluate_map]
  change Point.evaluate ⊤
    (X.left.toSpecΓ.appTop ((Scheme.ΓSpecIso ↧Γ(X.left, ⊤)).inv r)) z = _
  rw [Scheme.toSpecΓ_appTop]
  have h := DFunLike.congr_fun (congrArg CommRingCat.Hom.hom
    (Scheme.ΓSpecIso ↧Γ(X.left, ⊤)).inv_hom_id) r
  exact congrArg (fun s => Point.evaluate ⊤ s z) h

lemma affine_globalSections_finiteType (X : Over (Spec ↧ℂ))
    [IsAffine X.left] [LocallyOfFiniteType X.hom] :
    Algebra.FiniteType ℂ Γ(X.left, ⊤) := by
  rw [← RingHom.finiteType_algebraMap]
  apply (X.hom.finiteType_appLE (isAffineOpen_top (Spec ↧ℂ))
    (isAffineOpen_top X.left) (by simp)).comp
  exact RingHom.FiniteType.of_surjective _
    (Scheme.ΓSpecIso ↧ℂ).symm.commRingCatIsoToRingEquiv.surjective

lemma finite_presentation_equations {S : Type} [CommRing S] [Algebra ℂ S]
    [Algebra.FiniteType ℂ S] :
    ∃ (n m : ℕ) (f : MvPolynomial (Fin n) ℂ →ₐ[ℂ] S)
      (p : Fin m → MvPolynomial (Fin n) ℂ),
      Function.Surjective f ∧ Ideal.span (Set.range p) = RingHom.ker f.toRingHom := by
  obtain ⟨n, f, hf⟩ := (Algebra.FiniteType.iff_quotient_mvPolynomial'' (R := ℂ) (S := S)).mp inferInstance
  obtain ⟨m, p, hp⟩ := Submodule.fg_iff_exists_fin_generating_family.mp
    (IsNoetherian.noetherian (RingHom.ker f.toRingHom))
  exact ⟨n, m, f, p, hf, (Ideal.submodule_span_eq.symm.trans hp)⟩

end HodgeLean.Foundations.ComplexTopology
