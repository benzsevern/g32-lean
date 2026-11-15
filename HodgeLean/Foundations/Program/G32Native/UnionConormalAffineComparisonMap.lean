import HodgeLean.Foundations.Program.G32Native.UnionConormalAffineComparison
import HodgeLean.Foundations.Program.G32Native.UnionConormalTransport
import HodgeLean.Foundations.Program.G32Native.UnionConormalAffineNaturality

/-! # The natural conormal comparison in affine module coordinates -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
open scoped TensorProduct
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Program AlgebraicGeometry.Conormal

/-- In the affine presentations, the natural conormal map is the scalar extension
of the natural kernel-ideal map. The explicit presentation expressions avoid
expensive kernel conversion of local data bindings. -/
lemma unionConormal_affineComparisonMap_eq
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
  have hu : (idealPullbackMap (Spec.map p) (Spec.map q) (Spec.map (CommRingCat.ofHom (algebraMap R S))) (Spec.map k) h) = (unionConormalAffineIdealSourceIso (S := S) A p).hom ≫ ((tilde.functor (CommRingCat.of S)).map E) ≫ (affineIdealIso (CommRingCat.of S) B q).inv :=
    unionConormal_affineIdealPullbackMap_transported A B p q k h E hE
  have hn : (Scheme.Modules.pullback (Spec.map q)).map ((tilde.functor (CommRingCat.of S)).map E) ≫ ((s2e_affine_pullback_tilde_iso (CommRingCat.of S) B q).hom.app (ModuleCat.of S (RingHom.ker q.hom))) = ((s2e_affine_pullback_tilde_iso (CommRingCat.of S) B q).hom.app ((ModuleCat.extendScalars (algebraMap R S)).obj (ModuleCat.of R (RingHom.ker p.hom)))) ≫ ((tilde.functor B).map ((ModuleCat.extendScalars q.hom).map E)) :=
    unionConormal_affinePullback_naturality (CommRingCat.of S) B q _ _ E
  have hc : (comparisonMap (Spec.map p) (Spec.map q) (Spec.map (CommRingCat.ofHom (algebraMap R S))) (Spec.map k) h) = (unionConormalComparisonPrefixIso (Spec.map p) (Spec.map q) (Spec.map (CommRingCat.ofHom (algebraMap R S))) (Spec.map k) h).hom ≫ (Scheme.Modules.pullback (Spec.map q)).map (idealPullbackMap (Spec.map p) (Spec.map q) (Spec.map (CommRingCat.ofHom (algebraMap R S))) (Spec.map k) h) :=
    unionConormal_comparisonMap_eq_prefix (Spec.map p) (Spec.map q)
      (Spec.map (CommRingCat.ofHom (algebraMap R S))) (Spec.map k) h
  have hs : (unionConormalAffineComparisonSourceIso A B p q k h).hom =
      ((unionConormalComparisonPrefixIso (Spec.map p) (Spec.map q) (Spec.map (CommRingCat.ofHom (algebraMap R S))) (Spec.map k) h).hom ≫ (Scheme.Modules.pullback (Spec.map q)).map (unionConormalAffineIdealSourceIso (S := S) A p).hom) ≫ ((s2e_affine_pullback_tilde_iso (CommRingCat.of S) B q).hom.app ((ModuleCat.extendScalars (algebraMap R S)).obj (ModuleCat.of R (RingHom.ker p.hom)))) :=
    unionConormalAffineComparisonSourceIso_hom A B p q k h
  have ht : (unionConormalAffineComparisonTargetIso (CommRingCat.of S) B q).hom =
      (Scheme.Modules.pullback (Spec.map q)).map (affineIdealIso (CommRingCat.of S) B q).hom ≫ ((s2e_affine_pullback_tilde_iso (CommRingCat.of S) B q).hom.app (ModuleCat.of S (RingHom.ker q.hom))) :=
    unionConormalAffineComparisonTargetIso_hom (CommRingCat.of S) B q
  change (comparisonMap (Spec.map p) (Spec.map q) (Spec.map (CommRingCat.ofHom (algebraMap R S))) (Spec.map k) h) ≫ (unionConormalAffineComparisonTargetIso (CommRingCat.of S) B q).hom =
    (unionConormalAffineComparisonSourceIso A B p q k h).hom ≫ ((tilde.functor B).map ((ModuleCat.extendScalars q.hom).map E))
  calc
    _ = (comparisonMap (Spec.map p) (Spec.map q) (Spec.map (CommRingCat.ofHom (algebraMap R S))) (Spec.map k) h) ≫ ((Scheme.Modules.pullback (Spec.map q)).map (affineIdealIso (CommRingCat.of S) B q).hom ≫ ((s2e_affine_pullback_tilde_iso (CommRingCat.of S) B q).hom.app (ModuleCat.of S (RingHom.ker q.hom)))) := congrArg (fun t => (comparisonMap (Spec.map p) (Spec.map q) (Spec.map (CommRingCat.ofHom (algebraMap R S))) (Spec.map k) h) ≫ t) ht
    _ = ((unionConormalComparisonPrefixIso (Spec.map p) (Spec.map q) (Spec.map (CommRingCat.ofHom (algebraMap R S))) (Spec.map k) h).hom ≫ (Scheme.Modules.pullback (Spec.map q)).map (idealPullbackMap (Spec.map p) (Spec.map q) (Spec.map (CommRingCat.ofHom (algebraMap R S))) (Spec.map k) h)) ≫ ((Scheme.Modules.pullback (Spec.map q)).map (affineIdealIso (CommRingCat.of S) B q).hom ≫ ((s2e_affine_pullback_tilde_iso (CommRingCat.of S) B q).hom.app (ModuleCat.of S (RingHom.ker q.hom)))) :=
      congrArg (fun t => t ≫ ((Scheme.Modules.pullback (Spec.map q)).map (affineIdealIso (CommRingCat.of S) B q).hom ≫ ((s2e_affine_pullback_tilde_iso (CommRingCat.of S) B q).hom.app (ModuleCat.of S (RingHom.ker q.hom))))) hc
    _ = (((unionConormalComparisonPrefixIso (Spec.map p) (Spec.map q) (Spec.map (CommRingCat.ofHom (algebraMap R S))) (Spec.map k) h).hom ≫ (Scheme.Modules.pullback (Spec.map q)).map (unionConormalAffineIdealSourceIso (S := S) A p).hom) ≫ ((s2e_affine_pullback_tilde_iso (CommRingCat.of S) B q).hom.app ((ModuleCat.extendScalars (algebraMap R S)).obj (ModuleCat.of R (RingHom.ker p.hom))))) ≫ ((tilde.functor B).map ((ModuleCat.extendScalars q.hom).map E)) :=
      unionConormal_transport_naturality (Scheme.Modules.pullback (Spec.map q)) (unionConormalComparisonPrefixIso (Spec.map p) (Spec.map q) (Spec.map (CommRingCat.ofHom (algebraMap R S))) (Spec.map k) h).hom (unionConormalAffineIdealSourceIso (S := S) A p) (affineIdealIso (CommRingCat.of S) B q) (idealPullbackMap (Spec.map p) (Spec.map q) (Spec.map (CommRingCat.ofHom (algebraMap R S))) (Spec.map k) h) ((tilde.functor (CommRingCat.of S)).map E) hu ((s2e_affine_pullback_tilde_iso (CommRingCat.of S) B q).hom.app ((ModuleCat.extendScalars (algebraMap R S)).obj (ModuleCat.of R (RingHom.ker p.hom)))) ((s2e_affine_pullback_tilde_iso (CommRingCat.of S) B q).hom.app (ModuleCat.of S (RingHom.ker q.hom))) ((tilde.functor B).map ((ModuleCat.extendScalars q.hom).map E)) hn
    _ = _ := congrArg (fun t => t ≫ ((tilde.functor B).map ((ModuleCat.extendScalars q.hom).map E))) hs.symm

end HodgeLean.Foundations.Program.G32Native
