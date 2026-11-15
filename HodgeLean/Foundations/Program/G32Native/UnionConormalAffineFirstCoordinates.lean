import HodgeLean.Foundations.Program.G32Native.UnionConormalAffineComparisonMap
import HodgeLean.Foundations.Program.G32Native.UnionConormalMaps

/-! # Normalized coordinates of a natural affine first conormal arrow -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
open scoped TensorProduct
namespace HodgeLean.Foundations.Program.G32Native
open AlgebraicGeometry.Conormal

/-- A quotient triangle also commutes over the ambient ring identity. -/
lemma unionConormal_affineTriangle_identity
    (R : Type) [CommRing R] (A B : CommRingCat.{0})
    (p : CommRingCat.of R ⟶ A) (q : CommRingCat.of R ⟶ B) (k : A ⟶ B)
    (h : Spec.map k ≫ Spec.map p = Spec.map q) :
    Spec.map k ≫ Spec.map p = Spec.map q ≫
      Spec.map (CommRingCat.ofHom (algebraMap R R)) := by
  change _ = _ ≫ Spec.map (𝟙 (CommRingCat.of R))
  rw [Spec.map_id, Category.comp_id]
  exact h

/-- The affine comparison over the ring identity is the natural first map. -/
lemma unionConormal_affineTriangle_comparison
    (R : Type) [CommRing R] (A B : CommRingCat.{0})
    (p : CommRingCat.of R ⟶ A) (q : CommRingCat.of R ⟶ B) (k : A ⟶ B)
    (h : Spec.map k ≫ Spec.map p = Spec.map q) :
    comparisonMap (Spec.map p) (Spec.map q)
      (Spec.map (CommRingCat.ofHom (algebraMap R R))) (Spec.map k)
      (unionConormal_affineTriangle_identity R A B p q k h) =
      unionConormalFirst (Spec.map p) (Spec.map q) (Spec.map k) h := by
  change comparisonMap _ _ (Spec.map (𝟙 (CommRingCat.of R))) _ _ = _
  simp only [Spec.map_id]
  rfl

/-- Normalization of a kernel arrow gives coordinates of the actual natural first arrow. -/
lemma unionConormal_affineFirst_coordinates
    (R : Type) [CommRing R] (A B : CommRingCat.{0})
    (p : CommRingCat.of R ⟶ A) (q : CommRingCat.of R ⟶ B) (k : A ⟶ B)
    (h : Spec.map k ≫ Spec.map p = Spec.map q)
    (E : (ModuleCat.extendScalars (algebraMap R R)).obj
      (ModuleCat.of R (RingHom.ker p.hom)) ⟶ ModuleCat.of R (RingHom.ker q.hom))
    (hE : ∀ x : RingHom.ker p.hom, (E.hom ((1 : R) ⊗ₜ[R] x)).val = x.val)
    (M N : ModuleCat B)
    (e₁ : (ModuleCat.extendScalars q.hom).obj
      ((ModuleCat.extendScalars (algebraMap R R)).obj
        (ModuleCat.of R (RingHom.ker p.hom))) ≅ M)
    (e₂ : (ModuleCat.extendScalars q.hom).obj
      (ModuleCat.of R (RingHom.ker q.hom)) ≅ N)
    (f : M ⟶ N)
    (hn : (ModuleCat.extendScalars q.hom).map E ≫ e₂.hom = e₁.hom ≫ f) :
    unionConormalFirst (Spec.map p) (Spec.map q) (Spec.map k) h ≫
        (unionConormalAffineComparisonTargetIso (CommRingCat.of R) B q ≪≫
          (tilde.functor B).mapIso e₂).hom =
      (unionConormalAffineComparisonSourceIso A B p q k
          (unionConormal_affineTriangle_identity R A B p q k h) ≪≫
        (tilde.functor B).mapIso e₁).hom ≫ (tilde.functor B).map f := by
  have hc := unionConormal_affineComparisonMap_eq A B p q k
    (unionConormal_affineTriangle_identity R A B p q k h) E hE
  have hc' := (congrArg (fun u => u ≫
      (unionConormalAffineComparisonTargetIso (CommRingCat.of R) B q).hom)
      (unionConormal_affineTriangle_comparison R A B p q k h).symm).trans hc
  exact unionConormal_transport_map_square (tilde.functor B)
    (unionConormalFirst (Spec.map p) (Spec.map q) (Spec.map k) h)
    (unionConormalAffineComparisonSourceIso A B p q k
      (unionConormal_affineTriangle_identity R A B p q k h))
    (unionConormalAffineComparisonTargetIso (CommRingCat.of R) B q) e₁ e₂
    ((ModuleCat.extendScalars q.hom).map E) f hc' hn

#print axioms unionConormal_affineTriangle_identity
#print axioms unionConormal_affineFirst_coordinates
end HodgeLean.Foundations.Program.G32Native
