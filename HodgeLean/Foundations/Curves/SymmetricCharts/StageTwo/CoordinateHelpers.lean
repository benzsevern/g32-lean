import HodgeLean.Foundations.Curves.SymmetricCharts.StageTwo.Defs
import HodgeLean.Foundations.Program.SchoenCycleSectionDefinedAffineMap
import HodgeLean.Foundations.Program.SchoenCycleAffineIdeals

/-! # Coordinate morphisms from affine section algebras

HC no distance; AV milestone no distance.
-/
noncomputable section
open CategoryTheory AlgebraicGeometry
open HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.Curves.SymmetricCharts.StageTwo
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 200000
attribute [local instance] overSpecAlgebra

/-- Etale section coordinates retain their coordinate ideal sheaves.
Source: Hartshorne, Algebraic Geometry, II.2 and II.5.
HC no distance; AV milestone no distance.
-/
theorem affine_section_coordinates (Y : Over (Spec ↧ℂ)) [IsAffine Y.left]
    (n : ℕ) (G : MvPolynomial (Fin n) ℂ →ₐ[ℂ] Γ(Y.left, ⊤))
    (hG : G.toRingHom.Etale) :
    ∃ t : Y ⟶ affine n, Etale t.left ∧
      ∀ i, (coordinateIdeal n i).comap t.left =
        Scheme.IdealSheafData.ofIdealTop (Ideal.span {G (MvPolynomial.X i)}) := by
  letI : IsAffine (affine n).left := by
    change IsAffine (Spec ↧(MvPolynomial (Fin n) ℂ))
    infer_instance
  let t : Y ⟶ affine n := s2e_section_defined_affine_map Y _ G
  have ht : t.left = Y.left.toSpecΓ ≫ Spec.map (CommRingCat.ofHom G.toRingHom) := rfl
  haveI : Etale (Spec.map (CommRingCat.ofHom G.toRingHom)) :=
    HasRingHomProperty.Spec_iff.mpr hG
  haveI : Etale Y.left.toSpecΓ := inferInstance
  refine ⟨t, ?_, ?_⟩
  · rw [ht]
    infer_instance
  · intro i
    apply Scheme.IdealSheafData.ext_of_isAffine
    rw [s2e_affine_comap_ideal]
    simp only [coordinateIdeal, Scheme.IdealSheafData.ofIdealTop_ideal,
      Ideal.map_span, Set.image_singleton]
    have hΓ := ΓSpecIso_inv_ΓSpec_adjunction_homEquiv
      (CommRingCat.ofHom G.toRingHom)
    change Ideal.span {t.left.appTop ((Scheme.ΓSpecIso _).inv (MvPolynomial.X i))} = _
    simp only [homOfLE_refl, op_id, Functor.map_id, CommRingCat.id_apply]
    rw [Y.left.presheaf.map_id]
    congr 2
    exact congrArg (fun f : CommRingCat.of (MvPolynomial (Fin n) ℂ) ⟶ Γ(Y.left, ⊤) =>
      f.hom (MvPolynomial.X i)) hΓ

end HodgeLean.Foundations.Curves.SymmetricCharts.StageTwo
