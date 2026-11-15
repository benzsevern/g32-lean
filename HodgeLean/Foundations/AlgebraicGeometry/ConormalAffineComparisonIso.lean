import HodgeLean.Foundations.AlgebraicGeometry.ConormalAffineComparisonSections
import HodgeLean.Foundations.AlgebraicGeometry.ConormalAffinePullbackCompatibility
import HodgeLean.Foundations.AlgebraicGeometry.ConormalAffinePushout

/-! # Invertibility of the natural affine ideal comparison
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open HodgeLean.Foundations.Program
open scoped TensorProduct

namespace AlgebraicGeometry.Conormal

/-- Matching affine kernels make the natural flat ideal comparison invertible. -/
lemma affineIdealPullbackMap_isIso_of_kernel_eq
    {R S : Type} [CommRing R] [CommRing S] [Algebra R S] [Module.Flat R S]
    (A B : CommRingCat.{0}) (p : CommRingCat.of R ⟶ A) (q : CommRingCat.of S ⟶ B)
    (k : A ⟶ B)
    (h : Spec.map k ≫ Spec.map p = Spec.map q ≫ Spec.map (CommRingCat.ofHom (algebraMap R S)))
    (hker : (RingHom.ker p.hom).map (algebraMap R S) = RingHom.ker q.hom) :
    IsIso (idealPullbackMap (Spec.map p) (Spec.map q)
      (Spec.map (CommRingCat.ofHom (algebraMap R S))) (Spec.map k) h) := by
  let f : CommRingCat.of R ⟶ CommRingCat.of S := CommRingCat.ofHom (algebraMap R S)
  let K := ModuleCat.of R (RingHom.ker p.hom)
  let N := idealModule (Spec.map q)
  let eP := affineIdealIso _ _ p
  let eQ := s2e_affine_ideal_sections_equiv (CommRingCat.of S) B q
  let E : (ModuleCat.extendScalars f.hom).obj K ≅ ModuleCat.of S (RingHom.ker q.hom) :=
    s2e_extendScalars_algebraMap_iso K ≪≫
      (idealExtensionEquiv (S := S) (RingHom.ker p.hom)).toModuleIso ≪≫
      (LinearEquiv.ofEq _ _ hker).toModuleIso
  let u : (ModuleCat.extendScalars f.hom).obj K ⟶ (moduleSpecΓFunctor (R := CommRingCat.of S)).obj N :=
    E.hom ≫ eQ.symm.toModuleIso.hom
  have hu : IsIso u := by dsimp only [u]; infer_instance
  have : IsIso N.fromTildeΓ := s2e_idealModule_spec_fromTilde_isIso _ (Spec.map q)
  let t : (Scheme.Modules.pullback (Spec.map f)).obj (tilde K) ⟶ N :=
    (s2e_affine_pullback_tilde_iso _ _ f).hom.app K ≫
      ((tilde.adjunction (R := CommRingCat.of S)).homEquiv _ _).symm u
  have ht : IsIso t := by
    change IsIso ((s2e_affine_pullback_tilde_iso _ _ f).hom.app K ≫
      (tilde.functor (CommRingCat.of S)).map u ≫ N.fromTildeΓ)
    infer_instance
  have heq : idealPullbackMap (Spec.map p) (Spec.map q) (Spec.map f) (Spec.map k) h =
      (Scheme.Modules.pullback (Spec.map f)).map eP.hom ≫ t := by
    apply ((Scheme.Modules.pullbackPushforwardAdjunction (Spec.map f)).homEquiv _ _).injective
    rw [idealPullbackMap, Equiv.apply_symm_apply, Adjunction.homEquiv_naturality_left]
    apply (cancel_epi eP.inv).mp
    rw [Iso.inv_hom_id_assoc]
    apply ((tilde.adjunction (R := CommRingCat.of R)).homEquiv _ _).injective
    apply (cancel_mono ((s2e_affine_pushforward_sections_iso _ _ f).hom.app N)).mp
    rw [affineIdealIso_inv_transpose]
    refine Eq.trans ?_ (affinePullbackTilde_transpose _ _ f K N u).symm
    ext x
    apply eQ.injective
    apply Subtype.ext
    have hv := affineIdealPushforwardMap_value (CommRingCat.of R) A (CommRingCat.of S) B
      p q f k h ((s2e_affine_ideal_sections_equiv _ _ p).symm x)
    rw [LinearEquiv.apply_symm_apply] at hv
    change (eQ (((s2e_affine_pushforward_sections_iso _ _ f).hom.app N)
      (((moduleSpecΓFunctor (R := CommRingCat.of R)).map
        (idealPushforwardMap (Spec.map p) (Spec.map q) (Spec.map f) (Spec.map k) h))
          ((s2e_affine_ideal_sections_equiv _ _ p).symm x)))).val =
      (eQ (eQ.symm (E.hom ((1 : S) ⊗ₜ[R] x)))).val
    rw [eQ.apply_symm_apply]
    have hE : (E.hom ((1 : S) ⊗ₜ[R] x)).val = f x.val := by
      change (1 : S) • algebraMap R S x.val = algebraMap R S x.val
      rw [one_smul]
    rw [hE]
    exact hv
  rw [heq]
  infer_instance

/-- A cartesian affine square supplies the kernel equality for the natural comparison. -/
lemma affineIdealPullbackMap_isIso
    {R S : Type} [CommRing R] [CommRing S] [Algebra R S] [Module.Flat R S]
    (A B : CommRingCat.{0}) (p : CommRingCat.of R ⟶ A) (q : CommRingCat.of S ⟶ B)
    (k : A ⟶ B)
    (sq : IsPullback (Spec.map k) (Spec.map q) (Spec.map p)
      (Spec.map (CommRingCat.ofHom (algebraMap R S))))
    (hp : Function.Surjective p.hom) :
    IsIso (idealPullbackMap (Spec.map p) (Spec.map q)
      (Spec.map (CommRingCat.ofHom (algebraMap R S))) (Spec.map k) sq.w) := by
  have hs : IsPullback k.op q.op p.op (CommRingCat.ofHom (algebraMap R S)).op :=
    IsPullback.of_map_of_faithful Scheme.Spec sq
  have hker : (RingHom.ker p.hom).map (algebraMap R S) = RingHom.ker q.hom :=
    pushout_kernel_eq p (CommRingCat.ofHom (algebraMap R S)) k q hs.unop.flip hp
  exact affineIdealPullbackMap_isIso_of_kernel_eq A B p q k sq.w hker

end AlgebraicGeometry.Conormal
