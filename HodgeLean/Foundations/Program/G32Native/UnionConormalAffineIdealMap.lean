import HodgeLean.Foundations.AlgebraicGeometry.ConormalAffineComparisonIso
import HodgeLean.Foundations.Program.G32Native.UnionConormalAffineIdealSource

/-! # Identifying natural affine ideal maps without a flatness assumption -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Program AlgebraicGeometry.Conormal

/-- The values on scalar-extension generators identify the actual natural ideal map. -/
lemma unionConormal_affineIdealPullbackMap_eq
    {R S : Type} [CommRing R] [CommRing S] [Algebra R S]
    (A B : CommRingCat.{0}) (p : CommRingCat.of R ⟶ A) (q : CommRingCat.of S ⟶ B)
    (k : A ⟶ B)
    (h : Spec.map k ≫ Spec.map p = Spec.map q ≫
      Spec.map (CommRingCat.ofHom (algebraMap R S)))
    (E : (ModuleCat.extendScalars (algebraMap R S)).obj
      (ModuleCat.of R (RingHom.ker p.hom)) ⟶ ModuleCat.of S (RingHom.ker q.hom))
    (hE : ∀ x : RingHom.ker p.hom,
      (E.hom ((1 : S) ⊗ₜ[R] x)).val = algebraMap R S x.val) :
    let f : CommRingCat.of R ⟶ CommRingCat.of S := CommRingCat.ofHom (algebraMap R S)
    let K := ModuleCat.of R (RingHom.ker p.hom)
    let N := idealModule (Spec.map q)
    let u := E ≫ (s2e_affine_ideal_sections_equiv (CommRingCat.of S) B q).symm.toModuleIso.hom
    idealPullbackMap (Spec.map p) (Spec.map q) (Spec.map f) (Spec.map k) h =
      (Scheme.Modules.pullback (Spec.map f)).map (affineIdealIso _ _ p).hom ≫
        (s2e_affine_pullback_tilde_iso _ _ f).hom.app K ≫
          ((tilde.adjunction (R := CommRingCat.of S)).homEquiv _ N).symm u := by
  dsimp only
  let f : CommRingCat.of R ⟶ CommRingCat.of S := CommRingCat.ofHom (algebraMap R S)
  let K := ModuleCat.of R (RingHom.ker p.hom)
  let N := idealModule (Spec.map q)
  let eP := affineIdealIso _ _ p
  let eQ := s2e_affine_ideal_sections_equiv (CommRingCat.of S) B q
  let u := E ≫ eQ.symm.toModuleIso.hom
  apply ((Scheme.Modules.pullbackPushforwardAdjunction (Spec.map f)).homEquiv _ _).injective
  rw [idealPullbackMap, Equiv.apply_symm_apply, Adjunction.homEquiv_naturality_left]
  apply (cancel_epi eP.inv).mp
  rw [Iso.inv_hom_id_assoc]
  apply ((tilde.adjunction (R := CommRingCat.of R)).homEquiv _ _).injective
  apply (cancel_mono ((s2e_affine_pushforward_sections_iso _ _ f).hom.app N)).mp
  rw [affineIdealIso_inv_transpose]
  refine Eq.trans ?_ (affinePullbackTilde_transpose _ _ f K N u).symm
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
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
  rw [eQ.apply_symm_apply, hE]
  exact hv

/-- The natural affine ideal map is scalar extension of its kernel-module map. -/
lemma unionConormal_affineIdealPullbackMap_tilde
    {R S : Type} [CommRing R] [CommRing S] [Algebra R S]
    (A B : CommRingCat.{0}) (p : CommRingCat.of R ⟶ A) (q : CommRingCat.of S ⟶ B)
    (k : A ⟶ B)
    (h : Spec.map k ≫ Spec.map p = Spec.map q ≫
      Spec.map (CommRingCat.ofHom (algebraMap R S)))
    (E : (ModuleCat.extendScalars (algebraMap R S)).obj
      (ModuleCat.of R (RingHom.ker p.hom)) ⟶ ModuleCat.of S (RingHom.ker q.hom))
    (hE : ∀ x : RingHom.ker p.hom,
      (E.hom ((1 : S) ⊗ₜ[R] x)).val = algebraMap R S x.val) :
    let f : CommRingCat.of R ⟶ CommRingCat.of S := CommRingCat.ofHom (algebraMap R S)
    idealPullbackMap (Spec.map p) (Spec.map q) (Spec.map f) (Spec.map k) h =
      (Scheme.Modules.pullback (Spec.map f)).map (affineIdealIso _ _ p).hom ≫
        (s2e_affine_pullback_tilde_iso _ _ f).hom.app
          (ModuleCat.of R (RingHom.ker p.hom)) ≫
        (tilde.functor (CommRingCat.of S)).map E ≫ (affineIdealIso _ _ q).inv := by
  dsimp only
  rw [unionConormal_affineIdealPullbackMap_eq A B p q k h E hE]
  congr 1
  congr 1
  let adj := tilde.adjunction (R := CommRingCat.of S)
  apply (adj.homEquiv _ _).injective
  rw [Equiv.apply_symm_apply, Adjunction.homEquiv_naturality_left]
  change E ≫ (s2e_affine_ideal_sections_equiv _ _ q).symm.toModuleIso.hom =
    E ≫ adj.homEquiv _ _ ((adj.homEquiv _ _).symm
      (s2e_affine_ideal_sections_equiv _ _ q).symm.toModuleIso.hom)
  rw [Equiv.apply_symm_apply]

/-- Group the source identification before the scalar-extended kernel map. -/
lemma unionConormal_affineIdealPullbackMap_grouped
    {R S : Type} [CommRing R] [CommRing S] [Algebra R S]
    (A B : CommRingCat.{0}) (p : CommRingCat.of R ⟶ A) (q : CommRingCat.of S ⟶ B)
    (k : A ⟶ B)
    (h : Spec.map k ≫ Spec.map p = Spec.map q ≫
      Spec.map (CommRingCat.ofHom (algebraMap R S)))
    (E : (ModuleCat.extendScalars (algebraMap R S)).obj
      (ModuleCat.of R (RingHom.ker p.hom)) ⟶ ModuleCat.of S (RingHom.ker q.hom))
    (hE : ∀ x : RingHom.ker p.hom,
      (E.hom ((1 : S) ⊗ₜ[R] x)).val = algebraMap R S x.val) :
    let f : CommRingCat.of R ⟶ CommRingCat.of S := CommRingCat.ofHom (algebraMap R S)
    idealPullbackMap (Spec.map p) (Spec.map q) (Spec.map f) (Spec.map k) h =
      ((Scheme.Modules.pullback (Spec.map f)).map (affineIdealIso _ _ p).hom ≫
        (s2e_affine_pullback_tilde_iso _ _ f).hom.app
          (ModuleCat.of R (RingHom.ker p.hom))) ≫
        (tilde.functor (CommRingCat.of S)).map E ≫ (affineIdealIso _ _ q).inv := by
  dsimp only
  rw [unionConormal_affineIdealPullbackMap_tilde A B p q k h E hE]
  simp only [Category.assoc]

/-- The natural ideal map in the typed scalar-extension presentation. -/
lemma unionConormal_affineIdealPullbackMap_transported
    {R S : Type} [CommRing R] [CommRing S] [Algebra R S]
    (A B : CommRingCat.{0}) (p : CommRingCat.of R ⟶ A) (q : CommRingCat.of S ⟶ B)
    (k : A ⟶ B)
    (h : Spec.map k ≫ Spec.map p = Spec.map q ≫
      Spec.map (CommRingCat.ofHom (algebraMap R S)))
    (E : (ModuleCat.extendScalars (algebraMap R S)).obj
      (ModuleCat.of R (RingHom.ker p.hom)) ⟶ ModuleCat.of S (RingHom.ker q.hom))
    (hE : ∀ x : RingHom.ker p.hom,
      (E.hom ((1 : S) ⊗ₜ[R] x)).val = algebraMap R S x.val) :
    let f : CommRingCat.of R ⟶ CommRingCat.of S := CommRingCat.ofHom (algebraMap R S)
    idealPullbackMap (Spec.map p) (Spec.map q) (Spec.map f) (Spec.map k) h =
      (unionConormalAffineIdealSourceIso (S := S) A p).hom ≫
        (tilde.functor (CommRingCat.of S)).map E ≫ (affineIdealIso _ _ q).inv := by
  dsimp only
  rw [unionConormalAffineIdealSourceIso_hom]
  exact unionConormal_affineIdealPullbackMap_grouped A B p q k h E hE

end HodgeLean.Foundations.Program.G32Native
