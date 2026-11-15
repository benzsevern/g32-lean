import HodgeLean.Foundations.Program.G32Native.UnionConormalAffineComparisonMap

/-! # Epimorphisms in natural affine conormal comparison -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
open scoped TensorProduct
namespace HodgeLean.Foundations.Program.G32Native
open AlgebraicGeometry.Conormal

/-- A surjective kernel-extension arrow gives an epic natural conormal comparison. -/
lemma unionConormal_affineComparison_epi
    {R S : Type} [CommRing R] [CommRing S] [Algebra R S]
    (A B : CommRingCat.{0}) (p : CommRingCat.of R ⟶ A) (q : CommRingCat.of S ⟶ B)
    (k : A ⟶ B)
    (h : Spec.map k ≫ Spec.map p = Spec.map q ≫
      Spec.map (CommRingCat.ofHom (algebraMap R S)))
    (E : (ModuleCat.extendScalars (algebraMap R S)).obj
      (ModuleCat.of R (RingHom.ker p.hom)) ⟶ ModuleCat.of S (RingHom.ker q.hom))
    (hE : ∀ x : RingHom.ker p.hom,
      (E.hom ((1 : S) ⊗ₜ[R] x)).val = algebraMap R S x.val)
    [Epi E] :
    Epi (comparisonMap (Spec.map p) (Spec.map q)
      (Spec.map (CommRingCat.ofHom (algebraMap R S))) (Spec.map k) h) := by
  have he := unionConormal_affineComparisonMap_eq A B p q k h E hE
  haveI : Epi (comparisonMap (Spec.map p) (Spec.map q)
      (Spec.map (CommRingCat.ofHom (algebraMap R S))) (Spec.map k) h ≫
      (unionConormalAffineComparisonTargetIso (CommRingCat.of S) B q).hom) := by
    rw [he]
    infer_instance
  exact (epi_comp_iff_of_isIso _
    (unionConormalAffineComparisonTargetIso (CommRingCat.of S) B q).hom).mp inferInstance

#print axioms unionConormal_affineComparison_epi
end HodgeLean.Foundations.Program.G32Native
