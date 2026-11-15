import HodgeLean.Foundations.Program.G32Native.UnionConormalAffineComparison

/-! # Coordinates of the natural affine conormal arrow -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
open scoped TensorProduct
namespace HodgeLean.Foundations.Program.G32Native
open AlgebraicGeometry.Conormal

/-- The natural conormal comparison is scalar extension of the supplied
kernel map when that map has the natural values on ideal generators. -/
lemma unionConormal_affine_comparison_coordinates
    {R S : Type} [CommRing R] [CommRing S] [Algebra R S]
    (A B : CommRingCat.{0}) (p : CommRingCat.of R ⟶ A) (q : CommRingCat.of S ⟶ B)
    (k : A ⟶ B)
    (h : Spec.map k ≫ Spec.map p = Spec.map q ≫
      Spec.map (CommRingCat.ofHom (algebraMap R S)))
    (E : (ModuleCat.extendScalars (algebraMap R S)).obj
      (ModuleCat.of R (RingHom.ker p.hom)) ⟶ ModuleCat.of S (RingHom.ker q.hom))
    (hE : ∀ x : RingHom.ker p.hom,
      (E.hom ((1 : S) ⊗ₜ[R] x)).val = algebraMap R S x.val) :
    comparisonMap (Spec.map p) (Spec.map q)
        (Spec.map (CommRingCat.ofHom (algebraMap R S))) (Spec.map k) h ≫
      (unionConormalAffineComparisonTargetIso (CommRingCat.of S) B q).hom =
      (unionConormalAffineComparisonSourceIso A B p q k h).hom ≫
        (tilde.functor B).map ((ModuleCat.extendScalars q.hom).map E) := by
  rw [unionConormal_comparisonMap_eq_prefix,
    unionConormalAffineComparisonTargetIso_hom,
    unionConormalAffineComparisonSourceIso_hom,
    unionConormal_affineIdealPullbackMap_transported A B p q k h E hE]
  simp only [Functor.map_comp, Category.assoc]
  simp only [← Functor.mapIso_inv, ← Functor.mapIso_hom, Iso.inv_hom_id_assoc]
  simp only [Functor.mapIso_hom, Functor.map_comp, Category.assoc]
  have hn := (s2e_affine_pullback_tilde_iso (CommRingCat.of S) B q).hom.naturality E
  simp only [Functor.comp_map] at hn
  rw [hn]

#print axioms unionConormal_affine_comparison_coordinates
end HodgeLean.Foundations.Program.G32Native
