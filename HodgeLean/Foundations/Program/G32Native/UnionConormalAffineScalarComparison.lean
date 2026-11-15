import HodgeLean.Foundations.Program.G32Native.UnionConormalAffineMapCoordinates
import HodgeLean.Foundations.Program.G32Native.UnionConormalFramedScalarMono

/-! # Scalar right inverses in natural affine conormal coordinates -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
open scoped TensorProduct
namespace HodgeLean.Foundations.Program.G32Native
open AlgebraicGeometry.Conormal HodgeLean.Foundations.Program

/-- A scalar right inverse in the actual affine kernel coordinates makes
the equally framed natural conormal comparison monic. -/
lemma unionConormal_affine_scalar_comparison_mono
    {R S : Type} [CommRing R] [CommRing S] [Algebra R S]
    (A B : CommRingCat.{0}) [IsDomain B]
    (p : CommRingCat.of R ⟶ A) (q : CommRingCat.of S ⟶ B) (k : A ⟶ B)
    (h : Spec.map k ≫ Spec.map p = Spec.map q ≫
      Spec.map (CommRingCat.ofHom (algebraMap R S)))
    (E : (ModuleCat.extendScalars (algebraMap R S)).obj
      (ModuleCat.of R (RingHom.ker p.hom)) ⟶ ModuleCat.of S (RingHom.ker q.hom))
    (hE : ∀ x : RingHom.ker p.hom,
      (E.hom ((1 : S) ⊗ₜ[R] x)).val = algebraMap R S x.val)
    (G : (ModuleCat.extendScalars q.hom).obj (ModuleCat.of S (RingHom.ker q.hom)) ⟶
      (ModuleCat.extendScalars q.hom).obj
        ((ModuleCat.extendScalars (algebraMap R S)).obj
          (ModuleCat.of R (RingHom.ker p.hom))))
    (a : B) (ha : a ≠ 0)
    (hEG : ((ModuleCat.extendScalars q.hom).map E).hom.comp G.hom =
      a • (LinearMap.id :
        (ModuleCat.extendScalars q.hom).obj (ModuleCat.of S (RingHom.ker q.hom)) →ₗ[B]
        (ModuleCat.extendScalars q.hom).obj (ModuleCat.of S (RingHom.ker q.hom))))
    (n : ℕ)
    (eM : (Scheme.Modules.pullback (Spec.map k)).obj (s2c_conormal (Spec.map p)) ≅
      (SheafOfModules.free (R := (Spec B).ringCatSheaf) (Fin n) : (Spec B).Modules))
    (eN : s2c_conormal (Spec.map q) ≅
      (SheafOfModules.free (R := (Spec B).ringCatSheaf) (Fin n) : (Spec B).Modules)) :
    Mono (comparisonMap (Spec.map p) (Spec.map q)
      (Spec.map (CommRingCat.ofHom (algebraMap R S))) (Spec.map k) h) := by
  let es := unionConormalAffineComparisonSourceIso A B p q k h
  let et := unionConormalAffineComparisonTargetIso (CommRingCat.of S) B q
  have he := unionConormal_affine_comparison_coordinates A B p q k h E hE
  haveI : Mono ((tilde.functor B).map ((ModuleCat.extendScalars q.hom).map E)) :=
    union_framed_tilde_mono_of_scalar_right_inverse B _ _
      ((ModuleCat.extendScalars q.hom).map E) G a ha hEG n
      (es.symm ≪≫ eM) (et.symm ≪≫ eN)
  haveI : Mono (comparisonMap (Spec.map p) (Spec.map q)
      (Spec.map (CommRingCat.ofHom (algebraMap R S))) (Spec.map k) h ≫ et.hom) := by
    rw [he]
    infer_instance
  exact mono_of_mono _ et.hom

#print axioms unionConormal_affine_scalar_comparison_mono
end HodgeLean.Foundations.Program.G32Native
