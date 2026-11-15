import HodgeLean.Foundations.SegreProjectiveDefs
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor
import HodgeLean.Adapters.AbelianPower

/-! # Projectivity of fibre products (the Segre embedding): proof obligations

One `_aux` theorem per statement of `SegreProjective.lean`, all open. HC no distance; AV
milestone no distance.
-/

noncomputable section

namespace HodgeLean.Foundations

open CategoryTheory Limits AlgebraicGeometry MvPolynomial HomogeneousLocalization
open AlgebraicGeometry.ComplexProjectiveSpace ProjectiveSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local instance] MvPolynomial.gradedAlgebra

/-! ### Part A: the Segre morphism over `ℤ` -/

section General

universe u

variable {σ : Type*} {A : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-- For a global section `x` of `X`, the map `D(x) ⟶ Spec Γ(X)_x` induced by `X ⟶ Spec Γ(X)`
(the first factor of Mathlib's `Proj.toBasicOpenOfGlobalSections`).
Source: Hartshorne, *Algebraic Geometry*, Ex. II.2.4 (`X ⟶ Spec Γ(X)`); Mathlib
`Scheme.toSpecΓ`, `basicOpenIsoSpecAway`. -/
def g3c_basicOpenToSpecAway {X : Scheme.{u}} (x : Γ(X, ⊤)) :
    (X.basicOpen x).toScheme ⟶ Spec (.of (Localization.Away x)) :=
  (X.isoOfEq (X.toSpecΓ_preimage_basicOpen x)).inv ≫ X.toSpecΓ ∣_ _ ≫
    (basicOpenIsoSpecAway x).hom

example {X : Scheme.{u}} (x : Γ(X, ⊤)) :
    (X.basicOpen x).toScheme ⟶ Spec (.of (Localization.Away x)) :=
  g3c_basicOpenToSpecAway x

@[reassoc]
lemma g3c_basicOpenToSpecAway_spec {X : Scheme.{u}} (x : Γ(X, ⊤)) :
    g3c_basicOpenToSpecAway x ≫ Spec.map (CommRingCat.ofHom (algebraMap _ _)) = (X.basicOpen x).ι ≫ X.toSpecΓ := by
  simp [g3c_basicOpenToSpecAway, Scheme.isoOfEq_inv]

lemma g3c_toBasic_eq {X : Scheme.{u}} (f : A →+* Γ(X, ⊤)) {t : A} {d : ℕ} (h0d : 0 < d) (hd : t ∈ 𝒜 d) :
    Proj.toBasicOpenOfGlobalSections 𝒜 f rfl h0d hd = g3c_basicOpenToSpecAway (f t) ≫
      Spec.map (CommRingCat.ofHom (RingHom.comp (IsLocalization.map (M := .powers t)
        (T := .powers (f t)) _ f (by rw [← Submonoid.map_le_iff_le_comap, Submonoid.map_powers]))
          (algebraMap _ (Localization.Away t)))) ≫ (Proj.basicOpenIsoSpec _ _ hd h0d).inv := by
  rfl

lemma g3c_basicOpenToSpecAway_natural {X X' : Scheme.{u}} (g : X' ⟶ X) (x : Γ(X, ⊤))
    (h : X'.basicOpen (g.appTop.hom x) ≤ g ⁻¹ᵁ X.basicOpen x) :
    g.resLE (X.basicOpen x) (X'.basicOpen (g.appTop.hom x)) h ≫ g3c_basicOpenToSpecAway x =
      g3c_basicOpenToSpecAway (g.appTop.hom x) ≫ Spec.map (CommRingCat.ofHom (Localization.awayMap g.appTop.hom x)) := by
  rw [← cancel_mono (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, ⊤) (Localization.Away x)))),
    Category.assoc, g3c_basicOpenToSpecAway_spec, Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have : (Localization.awayMap g.appTop.hom x).comp (algebraMap Γ(X, ⊤) (Localization.Away x)) =
      (algebraMap _ _).comp g.appTop.hom := IsLocalization.map_comp _
  rw [this, CommRingCat.ofHom_comp, Spec.map_comp, g3c_basicOpenToSpecAway_spec_assoc, ← Category.assoc,
    Scheme.Hom.resLE_comp_ι]
  simp [Scheme.toSpecΓ_naturality]

lemma g3c_toBasic_natural {X X' : Scheme.{u}} (g : X' ⟶ X) (f : A →+* Γ(X, ⊤)) {t : A} {d : ℕ}
    (h0d : 0 < d) (hd : t ∈ 𝒜 d)
    (h : X'.basicOpen (g.appTop.hom (f t)) ≤ g ⁻¹ᵁ X.basicOpen (f t)) :
    g.resLE _ _ h ≫ Proj.toBasicOpenOfGlobalSections 𝒜 f rfl h0d hd =
      Proj.toBasicOpenOfGlobalSections 𝒜 (g.appTop.hom.comp f) rfl h0d hd := by
  rw [g3c_toBasic_eq, g3c_toBasic_eq]
  rw [← Category.assoc, g3c_basicOpenToSpecAway_natural, Category.assoc, ← Spec.map_comp_assoc,
    ← CommRingCat.ofHom_comp]
  congr 4
  rw [← RingHom.comp_assoc]
  congr 1
  apply IsLocalization.ringHom_ext (M := .powers t)
  ext a
  simp [Localization.awayMap, IsLocalization.Away.map, IsLocalization.map_eq]

@[reassoc]
lemma g3c_ι_fromOfGlobalSections {X : Scheme.{u}} (f : A →+* Γ(X, ⊤))
    (hf : (HomogeneousIdeal.irrelevant 𝒜).toIdeal.map f = ⊤) {t : A} {d : ℕ} (h0d : 0 < d)
    (hd : t ∈ 𝒜 d) :
    (X.basicOpen (f t)).ι ≫ Proj.fromOfGlobalSections 𝒜 f hf =
      Proj.toBasicOpenOfGlobalSections 𝒜 f rfl h0d hd ≫ (Proj.basicOpen 𝒜 t).ι := by
  rw [Proj.fromOfGlobalSections]
  exact (Proj.openCoverOfMapIrrelevantEqTop 𝒜 f hf).ι_glueMorphisms _ _ ⟨_, _, h0d, hd⟩

theorem spec_g3c_comp_fromOfGlobalSections_aux {X X' : Scheme.{u}} (g : X' ⟶ X)
    (f : A →+* Γ(X, ⊤)) (hf : (HomogeneousIdeal.irrelevant 𝒜).toIdeal.map f = ⊤)
    (hf' : (HomogeneousIdeal.irrelevant 𝒜).toIdeal.map (g.appTop.hom.comp f) = ⊤) :
    g ≫ Proj.fromOfGlobalSections 𝒜 f hf =
      Proj.fromOfGlobalSections 𝒜 (g.appTop.hom.comp f) hf' := by
  refine (Proj.openCoverOfMapIrrelevantEqTop 𝒜 _ hf').hom_ext _ _ fun ri ↦ ?_
  obtain ⟨d, t, h0d, hd⟩ := ri
  have h : X'.basicOpen (g.appTop.hom (f t)) ≤ g ⁻¹ᵁ X.basicOpen (f t) :=
    (Scheme.preimage_basicOpen_top g (f t)).ge
  change (X'.basicOpen (g.appTop.hom (f t))).ι ≫ _ = (X'.basicOpen (g.appTop.hom (f t))).ι ≫ _
  rw [← Scheme.Hom.resLE_comp_ι_assoc g h, g3c_ι_fromOfGlobalSections 𝒜 f hf h0d hd,
    ← Category.assoc, g3c_toBasic_natural 𝒜 g f h0d hd h]
  exact (g3c_ι_fromOfGlobalSections 𝒜 (g.appTop.hom.comp f) hf' h0d hd).symm

@[reassoc]
lemma g3c_basicOpenToSpecAway_unit {X : Scheme.{u}} (x x' : Γ(X, ⊤))
    (hu : IsUnit (algebraMap Γ(X, ⊤) (Localization.Away x) x'))
    (hD : X.basicOpen x = X.basicOpen x') :
    (X.isoOfEq hD).hom ≫ g3c_basicOpenToSpecAway x' =
      g3c_basicOpenToSpecAway x ≫ Spec.map (CommRingCat.ofHom
        (IsLocalization.Away.lift (S := Localization.Away x') x' hu)) := by
  rw [← cancel_mono (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, ⊤) (Localization.Away x')))),
    Category.assoc, g3c_basicOpenToSpecAway_spec, Category.assoc, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp, IsLocalization.Away.lift_comp, g3c_basicOpenToSpecAway_spec,
    Scheme.isoOfEq_hom_ι_assoc]

lemma g3c_twist_ring {R : Type u} [CommRing R]
    (f f' : A →+* R) (v : Rˣ)
    (hv : ∀ (d : ℕ) (r : A), r ∈ 𝒜 d → f' r = (v : R) ^ d * f r) {t : A} {d : ℕ}
    (hd : t ∈ 𝒜 d)
    (hu : IsUnit (algebraMap R (Localization.Away (f t)) (f' t))) :
    ((IsLocalization.Away.lift (S := Localization.Away (f' t)) (f' t) hu).comp
      ((IsLocalization.map (M := .powers t) (T := .powers (f' t)) _ f'
        (by rw [← Submonoid.map_le_iff_le_comap, Submonoid.map_powers])).comp
          (algebraMap (HomogeneousLocalization.Away 𝒜 t) (Localization.Away t)))) =
      (IsLocalization.map (M := .powers t) (T := .powers (f t)) _ f
        (by rw [← Submonoid.map_le_iff_le_comap, Submonoid.map_powers])).comp
          (algebraMap (HomogeneousLocalization.Away 𝒜 t) (Localization.Away t)) := by
  ext z
  obtain ⟨n, a, ha, rfl⟩ := HomogeneousLocalization.Away.mk_surjective 𝒜 hd z
  simp only [RingHom.coe_comp, Function.comp_apply, HomogeneousLocalization.algebraMap_apply,
    HomogeneousLocalization.Away.val_mk, Localization.mk_eq_mk', IsLocalization.map_mk']
  set θ := IsLocalization.Away.lift (S := Localization.Away (f' t)) (f' t) hu
  have hθ : ∀ y, θ (algebraMap R (Localization.Away (f' t)) y) =
      algebraMap R (Localization.Away (f t)) y := fun y ↦
    RingHom.congr_fun (IsLocalization.Away.lift_comp (f' t) hu) y
  have htn := SetLike.pow_mem_graded n hd
  have hw : IsUnit (algebraMap R (Localization.Away (f t)) ((v : R) ^ (n • d))) :=
    (v.isUnit.pow _).map _
  rw [IsLocalization.eq_mk'_iff_mul_eq]
  refine hw.mul_left_cancel ?_
  rw [mul_left_comm, ← map_mul, ← hv _ _ htn, ← hθ, ← map_mul, IsLocalization.mk'_spec_mk, hθ,
    hv _ _ ha, map_mul]

theorem spec_g3c_fromOfGlobalSections_unit_twist_aux {X : Scheme.{u}}
    (f f' : A →+* Γ(X, ⊤)) (hf : (HomogeneousIdeal.irrelevant 𝒜).toIdeal.map f = ⊤)
    (hf' : (HomogeneousIdeal.irrelevant 𝒜).toIdeal.map f' = ⊤) (v : Γ(X, ⊤)ˣ)
    (hv : ∀ (d : ℕ) (r : A), r ∈ 𝒜 d → f' r = (v : Γ(X, ⊤)) ^ d * f r) :
    Proj.fromOfGlobalSections 𝒜 f hf = Proj.fromOfGlobalSections 𝒜 f' hf' := by
  refine (Proj.openCoverOfMapIrrelevantEqTop 𝒜 _ hf).hom_ext _ _ fun ri ↦ ?_
  obtain ⟨d, t, h0d, hd⟩ := ri
  change (X.basicOpen (f t)).ι ≫ _ = (X.basicOpen (f t)).ι ≫ _
  have hD : X.basicOpen (f t) = X.basicOpen (f' t) := by
    rw [hv _ _ hd, Scheme.basicOpen_mul, Scheme.basicOpen_of_isUnit _ (v.isUnit.pow _), top_inf_eq]
  have hu : IsUnit (algebraMap Γ(X, ⊤) (Localization.Away (f t)) (f' t)) := by
    rw [hv _ _ hd, map_mul]
    exact ((v.isUnit.pow _).map _).mul (IsLocalization.Away.algebraMap_isUnit _)
  conv_rhs => rw [← Scheme.isoOfEq_hom_ι X hD]
  rw [Category.assoc, g3c_ι_fromOfGlobalSections 𝒜 f hf h0d hd,
    g3c_ι_fromOfGlobalSections 𝒜 f' hf' h0d hd, g3c_toBasic_eq, g3c_toBasic_eq]
  simp only [Category.assoc]
  rw [g3c_basicOpenToSpecAway_unit_assoc _ _ hu hD, ← Spec.map_comp_assoc,
    ← CommRingCat.ofHom_comp, g3c_twist_ring 𝒜 f f' v hv hd hu]

end General

lemma g3c_SpecMap_appTop_ΓSpecIso_inv {R S : CommRingCat.{0}} (φ : R ⟶ S) (c : R) :
    (Spec.map φ).appTop.hom ((Scheme.ΓSpecIso R).inv.hom c) = (Scheme.ΓSpecIso S).inv.hom (φ.hom c) :=
  (congrArg (fun ψ : R ⟶ Γ(Spec S, ⊤) ↦ ψ.hom c) (Scheme.ΓSpecIso_inv_naturality φ)).symm

lemma g3c_appTop_SpecMap_mul {W : Scheme.{0}} {R₁ R₂ S : CommRingCat.{0}} (e : W ⟶ Spec S)
    (φ₁ : R₁ ⟶ S) (φ₂ : R₂ ⟶ S) (c₁ c₂ : R₂) (c₃ : R₁) (h : φ₂ c₁ = φ₂ c₂ * φ₁ c₃) :
    (e ≫ Spec.map φ₂).appTop.hom ((Scheme.ΓSpecIso R₂).inv.hom c₁) =
      (e ≫ Spec.map φ₂).appTop.hom ((Scheme.ΓSpecIso R₂).inv.hom c₂) *
        (e ≫ Spec.map φ₁).appTop.hom ((Scheme.ΓSpecIso R₁).inv.hom c₃) := by
  simp only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply,
    g3c_SpecMap_appTop_ΓSpecIso_inv, ← map_mul, h]

lemma g3c_chartCoordinate_awayMap (n : ℕ) (i j k : Fin (n + 1)) :
    awayMap (UniversalGrading n) (isHomogeneous_X _ i)
        (show (X i * X j : UniversalRing n) = X j * X i from mul_comm _ _) (chartCoordinate j k) =
      awayMap (UniversalGrading n) (isHomogeneous_X _ i)
          (show (X i * X j : UniversalRing n) = X j * X i from mul_comm _ _) (chartCoordinate j i) *
        awayMap (UniversalGrading n) (isHomogeneous_X _ j) rfl (chartCoordinate i k) := by
  simp only [chartCoordinate, awayMap_mk]
  rw [HomogeneousLocalization.ext_iff_val, HomogeneousLocalization.val_mul]
  simp only [Away.val_mk, Localization.mk_mul]
  rw [Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  exact ⟨1, by simp; ring⟩

lemma g3c_overlap_coord (n : ℕ) (i j k : Fin (n + 1)) :
    (pullback.snd (g3c_chartι n i) (g3c_chartι n j)).appTop.hom
        ((Scheme.ΓSpecIso _).inv.hom (chartCoordinate j k)) =
      (pullback.snd (g3c_chartι n i) (g3c_chartι n j)).appTop.hom
          ((Scheme.ΓSpecIso _).inv.hom (chartCoordinate j i)) *
        (pullback.fst (g3c_chartι n i) (g3c_chartι n j)).appTop.hom
          ((Scheme.ΓSpecIso _).inv.hom (chartCoordinate i k)) := by
  simp only [g3c_chartι]
  rw [← Proj.pullbackAwayιIso_hom_SpecMap_awayMap_left (UniversalGrading n) (isHomogeneous_X _ i)
    zero_lt_one (isHomogeneous_X _ j) zero_lt_one rfl,
    ← Proj.pullbackAwayιIso_hom_SpecMap_awayMap_right (UniversalGrading n) (isHomogeneous_X _ i)
    zero_lt_one (isHomogeneous_X _ j) zero_lt_one rfl]
  exact g3c_appTop_SpecMap_mul _ _ _ _ _ _ (g3c_chartCoordinate_awayMap n i j k)

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
lemma g3c_map_isHomogeneous_twist {ι R : Type*} [CommRing R]
    (F G : MvPolynomial ι (ULift.{0} ℤ) →+* R) (u : R) (hFG : ∀ i, F (X i) = u * G (X i))
    {d : ℕ} {r : MvPolynomial ι (ULift.{0} ℤ)} (hr : r ∈ homogeneousSubmodule ι (ULift.{0} ℤ) d) :
    F r = u ^ d * G r := by
  have hC : ∀ c : ULift.{0} ℤ, F (C c) = G (C c) := by
    intro c
    have : c = ((c.down : ℤ) : ULift.{0} ℤ) := by ext; simp
    rw [this, map_intCast, map_intCast, map_intCast]
  rw [mem_homogeneousSubmodule] at hr
  conv_lhs => rw [r.as_sum]
  conv_rhs => rw [r.as_sum]
  rw [map_sum F, map_sum G, Finset.mul_sum]
  refine Finset.sum_congr rfl fun α hα ↦ ?_
  have hdeg : α.degree = d := by
    rw [Finsupp.degree_eq_weight_one]; exact hr (mem_support_iff.mp hα)
  rw [monomial_eq, map_mul, map_mul, hC, map_finsuppProd, map_finsuppProd]
  simp only [map_pow, hFG, mul_pow]
  rw [Finsupp.prod_mul, ← hdeg, Finsupp.degree_apply, ← Finset.prod_pow_eq_pow_sum]
  simp only [Finsupp.prod]
  ring

lemma g3c_overlap_fstCoord (n m : ℕ) (a b : Fin (n + 1) × Fin (m + 1)) (k : Fin (n + 1)) :
    (pullback.snd (g3c_prodChartι n m a.1 a.2) (g3c_prodChartι n m b.1 b.2)).appTop.hom
        (g3c_fstCoord n m b.1 b.2 k) =
      (pullback.snd (g3c_prodChartι n m a.1 a.2) (g3c_prodChartι n m b.1 b.2)).appTop.hom
          (g3c_fstCoord n m b.1 b.2 a.1) *
        (pullback.fst (g3c_prodChartι n m a.1 a.2) (g3c_prodChartι n m b.1 b.2)).appTop.hom
          (g3c_fstCoord n m a.1 a.2 k) := by
  have hq : (pullback.fst (g3c_prodChartι n m a.1 a.2) (g3c_prodChartι n m b.1 b.2) ≫
      pullback.fst (terminal.from _) (terminal.from _)) ≫ g3c_chartι n a.1 =
      (pullback.snd (g3c_prodChartι n m a.1 a.2) (g3c_prodChartι n m b.1 b.2) ≫
      pullback.fst (terminal.from _) (terminal.from _)) ≫ g3c_chartι n b.1 := by
    have h1 : ∀ i j, pullback.fst (terminal.from _) (terminal.from _) ≫ g3c_chartι n i =
        g3c_prodChartι n m i j ≫ pullback.fst _ _ := fun i j ↦ (pullback.lift_fst _ _ _).symm
    rw [Category.assoc, Category.assoc, h1 a.1 a.2, h1 b.1 b.2, pullback.condition_assoc]
  have e := congrArg (pullback.lift _ _ hq).appTop.hom (g3c_overlap_coord n a.1 b.1 k)
  rw [map_mul] at e
  change ((pullback.lift _ _ hq) ≫ pullback.snd _ _).appTop.hom _ =
    ((pullback.lift _ _ hq) ≫ pullback.snd _ _).appTop.hom _ *
      ((pullback.lift _ _ hq) ≫ pullback.fst _ _).appTop.hom _ at e
  rw [pullback.lift_fst, pullback.lift_snd] at e
  exact e

lemma g3c_overlap_sndCoord (n m : ℕ) (a b : Fin (n + 1) × Fin (m + 1)) (l : Fin (m + 1)) :
    (pullback.snd (g3c_prodChartι n m a.1 a.2) (g3c_prodChartι n m b.1 b.2)).appTop.hom
        (g3c_sndCoord n m b.1 b.2 l) =
      (pullback.snd (g3c_prodChartι n m a.1 a.2) (g3c_prodChartι n m b.1 b.2)).appTop.hom
          (g3c_sndCoord n m b.1 b.2 a.2) *
        (pullback.fst (g3c_prodChartι n m a.1 a.2) (g3c_prodChartι n m b.1 b.2)).appTop.hom
          (g3c_sndCoord n m a.1 a.2 l) := by
  have hq : (pullback.fst (g3c_prodChartι n m a.1 a.2) (g3c_prodChartι n m b.1 b.2) ≫
      pullback.snd (terminal.from _) (terminal.from _)) ≫ g3c_chartι m a.2 =
      (pullback.snd (g3c_prodChartι n m a.1 a.2) (g3c_prodChartι n m b.1 b.2) ≫
      pullback.snd (terminal.from _) (terminal.from _)) ≫ g3c_chartι m b.2 := by
    have h1 : ∀ i j, pullback.snd (terminal.from _) (terminal.from _) ≫ g3c_chartι m j =
        g3c_prodChartι n m i j ≫ pullback.snd _ _ := fun i j ↦ (pullback.lift_snd _ _ _).symm
    rw [Category.assoc, Category.assoc, h1 a.1 a.2, h1 b.1 b.2, pullback.condition_assoc]
  have e := congrArg (pullback.lift _ _ hq).appTop.hom (g3c_overlap_coord m a.2 b.2 l)
  rw [map_mul] at e
  change ((pullback.lift _ _ hq) ≫ pullback.snd _ _).appTop.hom _ =
    ((pullback.lift _ _ hq) ≫ pullback.snd _ _).appTop.hom _ *
      ((pullback.lift _ _ hq) ≫ pullback.fst _ _).appTop.hom _ at e
  rw [pullback.lift_fst, pullback.lift_snd] at e
  exact e

lemma g3c_compat_fstCoord_self (n m : ℕ) (i : Fin (n + 1)) (j : Fin (m + 1)) :
    g3c_fstCoord n m i j i = 1 := by
  simp [g3c_fstCoord, chartCoordinate_self]

lemma g3c_compat_sndCoord_self (n m : ℕ) (i : Fin (n + 1)) (j : Fin (m + 1)) :
    g3c_sndCoord n m i j j = 1 := by
  simp [g3c_sndCoord, chartCoordinate_self]

theorem spec_g3c_chartMap_compat_aux (n m : ℕ) (a b : Fin (n + 1) × Fin (m + 1)) :
    pullback.fst (g3c_prodChartι n m a.1 a.2) (g3c_prodChartι n m b.1 b.2) ≫
        g3c_chartMap n m a.1 a.2 =
      pullback.snd (g3c_prodChartι n m a.1 a.2) (g3c_prodChartι n m b.1 b.2) ≫
        g3c_chartMap n m b.1 b.2 := by
  set p₁ := pullback.fst (g3c_prodChartι n m a.1 a.2) (g3c_prodChartι n m b.1 b.2)
  set p₂ := pullback.snd (g3c_prodChartι n m a.1 a.2) (g3c_prodChartι n m b.1 b.2)
  have h₁ : (HomogeneousIdeal.irrelevant (g3c_segreGrading n m)).toIdeal.map
      (p₁.appTop.hom.comp (g3c_chartSections n m a.1 a.2)) = ⊤ := by
    rw [← Ideal.map_map, g3c_chartSections_irrelevant, Ideal.map_top]
  have h₂ : (HomogeneousIdeal.irrelevant (g3c_segreGrading n m)).toIdeal.map
      (p₂.appTop.hom.comp (g3c_chartSections n m b.1 b.2)) = ⊤ := by
    rw [← Ideal.map_map, g3c_chartSections_irrelevant, Ideal.map_top]
  rw [g3c_chartMap, g3c_chartMap, spec_g3c_comp_fromOfGlobalSections_aux _ p₁ _ _ h₁,
    spec_g3c_comp_fromOfGlobalSections_aux _ p₂ _ _ h₂]
  set u := p₂.appTop.hom (g3c_fstCoord n m b.1 b.2 a.1 * g3c_sndCoord n m b.1 b.2 a.2)
  set w := p₁.appTop.hom (g3c_fstCoord n m a.1 a.2 b.1 * g3c_sndCoord n m a.1 a.2 b.2)
  have huw : u * w = 1 := by
    have e1 := g3c_overlap_fstCoord n m a b b.1
    have e2 := g3c_overlap_sndCoord n m a b b.2
    rw [g3c_compat_fstCoord_self, map_one] at e1
    rw [g3c_compat_sndCoord_self, map_one] at e2
    simp only [u, w, map_mul]
    rw [mul_mul_mul_comm, ← e1, ← e2, one_mul]
  refine spec_g3c_fromOfGlobalSections_unit_twist_aux _ _ _ h₁ h₂ (Units.mkOfMulEqOne u w huw)
    fun d r hr ↦ g3c_map_isHomogeneous_twist _ _ _ (fun kl ↦ ?_) hr
  simp only [Units.val_mkOfMulEqOne, RingHom.comp_apply, g3c_chartSections_X, map_mul, u]
  rw [g3c_overlap_fstCoord n m a b kl.1, g3c_overlap_sndCoord n m a b kl.2]
  ring

theorem g3c_chartι_covers (n : ℕ) (x : g3c_P n) : ∃ i, x ∈ Set.range (g3c_chartι n i) := by
  have hx : x ∈ (⊤ : (g3c_P n).Opens) := trivial
  rw [← iSup_coordinateBasicOpen_eq_top n, TopologicalSpace.Opens.mem_iSup] at hx
  obtain ⟨i, hi⟩ := hx
  refine ⟨i, ?_⟩
  change x ∈ (Proj.awayι (UniversalGrading n) (X i) (isHomogeneous_X _ i) zero_lt_one).opensRange
  rw [Proj.opensRange_awayι]
  exact hi

theorem g3c_range_prodChartι (n m : ℕ) (i : Fin (n + 1)) (j : Fin (m + 1)) :
    Set.range (g3c_prodChartι n m i j) =
      pullback.fst (terminal.from (g3c_P n)) (terminal.from (g3c_P m)) ⁻¹'
          Set.range (g3c_chartι n i) ∩
        pullback.snd (terminal.from (g3c_P n)) (terminal.from (g3c_P m)) ⁻¹'
          Set.range (g3c_chartι m j) := by
  rw [g3c_prodChartι, Scheme.Pullback.range_map]

theorem g3c_prodChartι_covers (n m : ℕ) (x : g3c_prod n m) :
    ∃ ij : Fin (n + 1) × Fin (m + 1), ∃ y, g3c_prodChartι n m ij.1 ij.2 y = x := by
  obtain ⟨i, hi⟩ := g3c_chartι_covers n
    (pullback.fst (terminal.from (g3c_P n)) (terminal.from (g3c_P m)) x)
  obtain ⟨j, hj⟩ := g3c_chartι_covers m
    (pullback.snd (terminal.from (g3c_P n)) (terminal.from (g3c_P m)) x)
  have hx : x ∈ Set.range (g3c_prodChartι n m i j) := by
    rw [g3c_range_prodChartι]
    exact ⟨hi, hj⟩
  obtain ⟨y, hy⟩ := hx
  exact ⟨(i, j), y, hy⟩

/-- The open cover of `ℙⁿ_ℤ × ℙᵐ_ℤ` by the charts `D₊(x_i) × D₊(y_j)`.
Source: Hartshorne, *Algebraic Geometry*, Thm. II.3.3, Step 3 and Prop. II.2.5(b); Mathlib
`Scheme.Cover.mkOfCovers`, `Scheme.Pullback.range_map`. -/
def g3c_prodCover (n m : ℕ) : (g3c_prod n m).OpenCover :=
  Scheme.Cover.mkOfCovers (Fin (n + 1) × Fin (m + 1)) (fun ij => g3c_chart n m ij.1 ij.2)
    (fun ij => g3c_prodChartι n m ij.1 ij.2) (g3c_prodChartι_covers n m)

example (n m : ℕ) (i : Fin (n + 1)) (j : Fin (m + 1)) :
    (g3c_prodCover n m).f (i, j) = g3c_prodChartι n m i j := rfl

theorem spec_g3c_existsUnique_segre_aux (n m : ℕ) :
    ∃! s : g3c_prod n m ⟶ g3c_segreTarget n m,
      ∀ i j, g3c_prodChartι n m i j ≫ s = g3c_chartMap n m i j := by
  refine ⟨(g3c_prodCover n m).glueMorphisms (fun ij => g3c_chartMap n m ij.1 ij.2)
      (fun a b => spec_g3c_chartMap_compat_aux n m a b),
    fun i j => (g3c_prodCover n m).ι_glueMorphisms _ _ (i, j),
    fun s hs => (g3c_prodCover n m).hom_ext _ _ fun ij => ?_⟩
  rw [Scheme.Cover.ι_glueMorphisms]
  exact hs ij.1 ij.2

theorem g3c_chartι_preimage_opensRange (n : ℕ) (a i : Fin (n + 1)) :
    g3c_chartι n a ⁻¹ᵁ (g3c_chartι n i).opensRange =
      (Spec (.of (Away (UniversalGrading n) (X a : UniversalRing n)))).basicOpen
        ((Scheme.ΓSpecIso _).inv (chartCoordinate a i)) := by
  rw [basicOpen_eq_of_affine]
  change Proj.awayι (UniversalGrading n) (X a) (isHomogeneous_X _ a) zero_lt_one ⁻¹ᵁ
    (Proj.awayι (UniversalGrading n) (X i) (isHomogeneous_X _ i) zero_lt_one).opensRange = _
  rw [Proj.opensRange_awayι, Proj.awayι_preimage_basicOpen _ (isHomogeneous_X _ a) zero_lt_one
    (isHomogeneous_X _ i) zero_lt_one]
  congr 1
  rw [HomogeneousLocalization.ext_iff_val]
  simp [chartCoordinate]

theorem g3c_basicOpen_fstCoord (n m : ℕ) (a : Fin (n + 1)) (b : Fin (m + 1)) (i : Fin (n + 1)) :
    (g3c_chart n m a b).basicOpen (g3c_fstCoord n m a b i) =
      pullback.fst (terminal.from (Spec (.of (Away (UniversalGrading n) (X a : UniversalRing n)))))
          (terminal.from (Spec (.of (Away (UniversalGrading m) (X b : UniversalRing m))))) ⁻¹ᵁ
        (g3c_chartι n a ⁻¹ᵁ (g3c_chartι n i).opensRange) := by
  rw [g3c_chartι_preimage_opensRange, Scheme.preimage_basicOpen_top]
  rfl

theorem g3c_basicOpen_sndCoord (n m : ℕ) (a : Fin (n + 1)) (b : Fin (m + 1)) (j : Fin (m + 1)) :
    (g3c_chart n m a b).basicOpen (g3c_sndCoord n m a b j) =
      pullback.snd (terminal.from (Spec (.of (Away (UniversalGrading n) (X a : UniversalRing n)))))
          (terminal.from (Spec (.of (Away (UniversalGrading m) (X b : UniversalRing m))))) ⁻¹ᵁ
        (g3c_chartι m b ⁻¹ᵁ (g3c_chartι m j).opensRange) := by
  rw [g3c_chartι_preimage_opensRange, Scheme.preimage_basicOpen_top]
  rfl

theorem g3c_prodChartι_preimage_opensRange (n m : ℕ) (a i : Fin (n + 1)) (b j : Fin (m + 1)) :
    g3c_prodChartι n m a b ⁻¹ᵁ (g3c_prodChartι n m i j).opensRange =
      (g3c_chart n m a b).basicOpen (g3c_fstCoord n m a b i * g3c_sndCoord n m a b j) := by
  rw [Scheme.basicOpen_mul, g3c_basicOpen_fstCoord, g3c_basicOpen_sndCoord]
  ext x
  change g3c_prodChartι n m a b x ∈ Set.range (g3c_prodChartι n m i j) ↔
    g3c_chartι n a (pullback.fst (terminal.from (Spec (.of (Away (UniversalGrading n) (X a : UniversalRing n)))))
      (terminal.from (Spec (.of (Away (UniversalGrading m) (X b : UniversalRing m))))) x) ∈ Set.range (g3c_chartι n i) ∧
      g3c_chartι m b (pullback.snd (terminal.from (Spec (.of (Away (UniversalGrading n) (X a : UniversalRing n)))))
      (terminal.from (Spec (.of (Away (UniversalGrading m) (X b : UniversalRing m))))) x) ∈ Set.range (g3c_chartι m j)
  rw [g3c_range_prodChartι, Set.mem_inter_iff, Set.mem_preimage, Set.mem_preimage,
    ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply,
    ← Scheme.Hom.comp_apply]
  simp only [g3c_prodChartι, pullback.lift_fst, pullback.lift_snd]

theorem spec_g3c_segre_preimage_basicOpen_aux (n m : ℕ) (s : g3c_prod n m ⟶ g3c_segreTarget n m)
    (hs : ∀ i j, g3c_prodChartι n m i j ≫ s = g3c_chartMap n m i j)
    (i : Fin (n + 1)) (j : Fin (m + 1)) :
    s ⁻¹ᵁ Proj.basicOpen (g3c_segreGrading n m) (X (i, j)) =
      (g3c_prodChartι n m i j).opensRange := by
  ext x
  obtain ⟨⟨a, b⟩, y, rfl⟩ := g3c_prodChartι_covers n m x
  rw [SetLike.mem_coe, SetLike.mem_coe, ← Scheme.Hom.mem_preimage, ← Scheme.Hom.mem_preimage,
    ← Scheme.Hom.comp_preimage, hs, g3c_chartMap,
    Proj.fromOfGlobalSections_preimage_basicOpen _ _ _ zero_lt_one (isHomogeneous_X _ (i, j)),
    g3c_chartSections_X, g3c_prodChartι_preimage_opensRange]

private def chartTensorIso (n m : ℕ) (i : Fin (n+1)) (j : Fin (m+1)) :
    g3c_chart n m i j ≅ Spec (.of (TensorProduct ℤ
      (Away (UniversalGrading n) (X i : UniversalRing n))
      (Away (UniversalGrading m) (X j : UniversalRing m)))) :=
  let e := terminalIsTerminal.uniqueUpToIso specZIsTerminal
  (asIso (pullback.map _ _ _ _ (𝟙 _) (𝟙 _) e.hom
    (specZIsTerminal.hom_ext _ _) (specZIsTerminal.hom_ext _ _))) ≪≫
    pullbackSpecIso ℤ _ _

section ClosedImmersion

universe u

variable {σ : Type*} {A : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜]

theorem g3c_surjective_of_away_mk {X : Scheme.{u}} (f : A →+* Γ(X, ⊤))
    (hf : Function.Surjective f) {t : A} (ht : t ∈ 𝒜 1) (h1 : f t = 1)
    (φ : Away 𝒜 t →+* Localization.Away (f t))
    (hφ : ∀ (i : ℕ) (x : A) (hx : x ∈ 𝒜 (i • 1)),
      φ (Away.mk 𝒜 ht i x hx) = algebraMap _ _ (f x)) :
    Function.Surjective φ := by
  classical
  intro z
  obtain ⟨⟨y, ⟨_, k, rfl⟩⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers (f t)) z
  obtain ⟨a, rfl⟩ := hf y
  have hk : (⟨f t ^ k, k, rfl⟩ : Submonoid.powers (f t)) = 1 := Subtype.ext (by simp [h1])
  rw [hk]
  dsimp only
  rw [IsLocalization.mk'_one, ← DirectSum.sum_support_decompose 𝒜 a, map_sum, map_sum]
  refine ⟨∑ i ∈ (DirectSum.decompose 𝒜 a).support,
    Away.mk 𝒜 ht i (DirectSum.decompose 𝒜 a i)
      (by rw [smul_eq_mul, mul_one]; exact (DirectSum.decompose 𝒜 a i).2), ?_⟩
  rw [map_sum]
  exact Finset.sum_congr rfl fun i _ => hφ _ _ _

theorem g3c_isClosedImmersion_toBasicOpenOfGlobalSections {X : Scheme.{u}} [IsAffine X]
    (f : A →+* Γ(X, ⊤)) (hf : Function.Surjective f) {t : A} (ht : t ∈ 𝒜 1) (h1 : f t = 1) :
    IsClosedImmersion (Proj.toBasicOpenOfGlobalSections 𝒜 f rfl zero_lt_one ht) := by
  unfold Proj.toBasicOpenOfGlobalSections
  simp only [Category.assoc]
  rw [MorphismProperty.cancel_left_of_respectsIso @IsClosedImmersion,
    MorphismProperty.cancel_left_of_respectsIso @IsClosedImmersion,
    MorphismProperty.cancel_left_of_respectsIso @IsClosedImmersion,
    MorphismProperty.cancel_right_of_respectsIso @IsClosedImmersion]
  apply IsClosedImmersion.spec_of_surjective
  refine g3c_surjective_of_away_mk 𝒜 f hf ht h1 _ fun i x hx => ?_
  simp only [CommRingCat.hom_ofHom, RingHom.coe_comp, Function.comp_apply,
    HomogeneousLocalization.algebraMap_apply, HomogeneousLocalization.Away.val_mk,
    Localization.mk_eq_mk', IsLocalization.map_mk']
  rw [IsLocalization.mk'_eq_iff_eq_mul]
  simp [h1]

theorem g3c_isClosedImmersion_fromOfGlobalSections_restrict {X : Scheme.{u}} [IsAffine X]
    (f : A →+* Γ(X, ⊤)) (hf : (HomogeneousIdeal.irrelevant 𝒜).toIdeal.map f = ⊤)
    (hsurj : Function.Surjective f) {t : A} (ht : t ∈ 𝒜 1) (h1 : f t = 1) :
    IsClosedImmersion (Proj.fromOfGlobalSections 𝒜 f hf ∣_ Proj.basicOpen 𝒜 t) := by
  rw [Proj.fromOfGlobalSections_morphismRestrict _ _ _ zero_lt_one ht,
    MorphismProperty.cancel_left_of_respectsIso @IsClosedImmersion]
  exact g3c_isClosedImmersion_toBasicOpenOfGlobalSections 𝒜 f hsurj ht h1

end ClosedImmersion

theorem g3c_isClosedImmersion_morphismRestrict_of_opensRange {X Y Z : Scheme.{0}} (f : X ⟶ Y)
    (U : Y.Opens) (ι : Z ⟶ X) [IsOpenImmersion ι] (hι : ι.opensRange = f ⁻¹ᵁ U)
    (h : IsClosedImmersion ((ι ≫ f) ∣_ U)) : IsClosedImmersion (f ∣_ U) := by
  have : IsIso (ι ∣_ (f ⁻¹ᵁ U)) := by
    rw [isIso_iff_isOpenImmersion_and_surjective]
    refine ⟨inferInstance, ⟨fun y => ?_⟩⟩
    obtain ⟨z, hz⟩ : y.1 ∈ Set.range ι := by
      change y.1 ∈ ι.opensRange
      rw [hι]
      exact y.2
    refine ⟨⟨z, ?_⟩, Subtype.ext ?_⟩
    · change ι z ∈ f ⁻¹ᵁ U
      rw [hz]
      exact y.2
    · rw [morphismRestrict_base_coe]
      exact hz
  rw [morphismRestrict_comp, MorphismProperty.cancel_left_of_respectsIso @IsClosedImmersion] at h
  exact h

theorem g3c_irrelevant_le_span_segre (n m : ℕ) :
    (HomogeneousIdeal.irrelevant (g3c_segreGrading n m)).toIdeal ≤
      Ideal.span (Set.range (MvPolynomial.X :
        Fin (n + 1) × Fin (m + 1) → MvPolynomial (Fin (n + 1) × Fin (m + 1)) (ULift.{0} ℤ))) := by
  rw [HomogeneousIdeal.irrelevant_eq_span, Ideal.span_le]
  intro r hr
  simp only [Set.mem_iUnion] at hr
  obtain ⟨d, hd⟩ := hr
  obtain ⟨hd0, hr⟩ := hd
  have hrpow : r ∈ Ideal.span (Set.range (MvPolynomial.X :
      Fin (n + 1) × Fin (m + 1) → MvPolynomial (Fin (n + 1) × Fin (m + 1)) (ULift.{0} ℤ))) ^ d := by
    rw [Ideal.span_pow_eq_map_homogeneousSubmodule]
    exact ⟨MvPolynomial.map MvPolynomial.C r, hr.map _, by simp⟩
  exact Ideal.pow_le_self hd0.ne' hrpow

private def appTopEquiv {X Y : Scheme} (e : X ≅ Y) : Γ(Y, ⊤) ≃+* Γ(X, ⊤) where
  toFun := e.hom.appTop
  invFun := e.inv.appTop
  map_add' := map_add _
  map_mul' := map_mul _
  left_inv x := by
    have h := congrArg Scheme.Hom.appTop e.inv_hom_id
    rw [Scheme.Hom.comp_appTop] at h
    exact congrArg (fun k : Γ(Y, ⊤) ⟶ Γ(Y, ⊤) => k.hom x) h
  right_inv x := by
    have h := congrArg Scheme.Hom.appTop e.hom_inv_id
    rw [Scheme.Hom.comp_appTop] at h
    exact congrArg (fun k : Γ(X, ⊤) ⟶ Γ(X, ⊤) => k.hom x) h

example (n m : ℕ) (i : Fin (n+1)) (j : Fin (m+1)) :
    TensorProduct ℤ (Away (UniversalGrading n) (X i : UniversalRing n))
      (Away (UniversalGrading m) (X j : UniversalRing m)) ≃+*
      Γ(g3c_chart n m i j, ⊤) :=
  (Scheme.ΓSpecIso _).symm.commRingCatIsoToRingEquiv.trans
    (appTopEquiv (chartTensorIso n m i j))

private def tensorChartEquiv (n m : ℕ) (i : Fin (n+1)) (j : Fin (m+1)) :=
  (Scheme.ΓSpecIso _).symm.commRingCatIsoToRingEquiv.trans
    (appTopEquiv (chartTensorIso n m i j))

private theorem tensorChartEquiv_includeLeft (n m : ℕ) (i : Fin (n+1)) (j : Fin (m+1))
    (k : Fin (n+1)) :
    tensorChartEquiv n m i j (Algebra.TensorProduct.includeLeft (R := ℤ) (S := ℤ)
      (B := Away (UniversalGrading m) (X j : UniversalRing m))
      (chartCoordinate i k)) = g3c_fstCoord n m i j k := by
  have h : (chartTensorIso n m i j).hom ≫
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom (R := ℤ)
        (A := Away (UniversalGrading n) (X i : UniversalRing n))
        (B := Away (UniversalGrading m) (X j : UniversalRing m)))) =
      pullback.fst (terminal.from (Spec (.of (Away (UniversalGrading n) (X i : UniversalRing n)))))
        (terminal.from (Spec (.of (Away (UniversalGrading m) (X j : UniversalRing m))))) := by
    simp [chartTensorIso]
  have ht := congrArg Scheme.Hom.appTop h
  rw [Scheme.Hom.comp_appTop] at ht
  change _ = (Scheme.Hom.appTop (pullback.fst _ _)).hom
    ((Scheme.ΓSpecIso (.of (Away (UniversalGrading n) (X i : UniversalRing n)))).inv.hom
      (chartCoordinate i k))
  rw [← ht]
  change (Scheme.Hom.appTop (chartTensorIso n m i j).hom).hom
      ((Scheme.ΓSpecIso _).inv.hom
        (Algebra.TensorProduct.includeLeft (R := ℤ) (S := ℤ)
          (B := Away (UniversalGrading m) (X j : UniversalRing m)) (chartCoordinate i k))) =
    (Scheme.Hom.appTop (chartTensorIso n m i j).hom).hom
      ((Scheme.Hom.appTop (Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeLeftRingHom (R := ℤ)
          (A := Away (UniversalGrading n) (X i : UniversalRing n))
          (B := Away (UniversalGrading m) (X j : UniversalRing m)))))).hom
        ((Scheme.ΓSpecIso _).inv.hom (chartCoordinate i k)))
  apply congrArg (Scheme.Hom.appTop (chartTensorIso n m i j).hom).hom
  exact congrArg (fun q => q.hom (chartCoordinate i k))
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom
      (Algebra.TensorProduct.includeLeftRingHom (R := ℤ)
        (A := Away (UniversalGrading n) (X i : UniversalRing n))
        (B := Away (UniversalGrading m) (X j : UniversalRing m)))))

private theorem awayCoord_surj (n : ℕ) (i : Fin (n+1)) : Function.Surjective
    (eval₂Hom ((fromZeroRingHom (UniversalGrading n) (.powers (X i))).comp
      (ProjectiveSpace.degreeZeroEquiv (Fin (n+1)) (ULift.{0} ℤ)).symm.toRingHom)
      (chartCoordinate i) : UniversalRing n →+* Away (UniversalGrading n) (X i)) := by
  intro z
  let φ : UniversalRing n →+* Away (UniversalGrading n) (X i) :=
    eval₂Hom ((fromZeroRingHom (UniversalGrading n) (.powers (X i))).comp
      (ProjectiveSpace.degreeZeroEquiv (Fin (n+1)) (ULift.{0} ℤ)).symm.toRingHom)
      (chartCoordinate i)
  let S : Subring (Away (UniversalGrading n) (X i)) := φ.range
  have hbase : ∀ a : UniversalGrading n 0,
      fromZeroRingHom (UniversalGrading n) (.powers (X i)) a ∈ S := by
    intro a
    obtain ⟨c, rfl⟩ := (ProjectiveSpace.degreeZeroEquiv
      (Fin (n+1)) (ULift.{0} ℤ)).symm.surjective a
    exact ⟨C c, by simp [φ]⟩
  have hcoord : ∀ k, chartCoordinate i k ∈ S := by
    intro k
    exact ⟨X k, by simp [φ]⟩
  have htop := Away.adjoin_mk_prod_pow_eq_top (isHomogeneous_X (ULift.{0} ℤ) i)
    (Fin (n+1)) (fun k => X k) (adjoin_coordinates_eq_top n)
    (fun _ => (1 : ℕ)) (fun k => isHomogeneous_X (ULift.{0} ℤ) k)
  have hz : z ∈ Algebra.adjoin (UniversalGrading n 0)
      { Away.mk (UniversalGrading n) (isHomogeneous_X (ULift.{0} ℤ) i) a
        (∏ k, X k ^ ai k) (hai ▸ SetLike.prod_pow_mem_graded _ _ _ _
          (fun k _ => isHomogeneous_X (ULift.{0} ℤ) k)) |
        (a : ℕ) (ai : Fin (n+1) → ℕ) (hai : ∑ k, ai k • 1 = a • 1)
          (_ : ∀ k, ai k ≤ 1) } := by
    rw [htop]
    trivial
  refine Algebra.adjoin_induction (p := fun x _ => x ∈ S) ?_ hbase ?_ ?_ hz
  · intro x hx
    obtain ⟨a, ai, hai, _, rfl⟩ := hx
    have hai' : ∑ k, ai k = a := by simpa using hai
    rw [chartGenerator_eq_prod i ai hai']
    exact Subring.prod_mem S (fun k _ => S.pow_mem (hcoord k) _)
  · intro x y _ _ hx hy
    exact S.add_mem hx hy
  · intro x y _ _ hx hy
    exact S.mul_mem hx hy

set_option maxHeartbeats 400000 in
private theorem chartSections_rename_left (n m : ℕ) (i : Fin (n+1)) (j : Fin (m+1))
    (p : UniversalRing n) :
    g3c_chartSections n m i j (rename (fun k => (k, j)) p) =
      tensorChartEquiv n m i j (Algebra.TensorProduct.includeLeft (R := ℤ) (S := ℤ)
        (B := Away (UniversalGrading m) (X j : UniversalRing m))
        (eval₂Hom ((fromZeroRingHom (UniversalGrading n) (.powers (X i))).comp
          (ProjectiveSpace.degreeZeroEquiv (Fin (n+1)) (ULift.{0} ℤ)).symm.toRingHom)
          (chartCoordinate i) p)) := by
  let ψ : UniversalRing n →+* Γ(g3c_chart n m i j, ⊤) :=
    (tensorChartEquiv n m i j).toRingHom.comp
      ((Algebra.TensorProduct.includeLeft (R := ℤ) (S := ℤ)
        (B := Away (UniversalGrading m) (X j : UniversalRing m))).toRingHom.comp
        (eval₂Hom ((fromZeroRingHom (UniversalGrading n) (.powers (X i))).comp
          (ProjectiveSpace.degreeZeroEquiv (Fin (n+1)) (ULift.{0} ℤ)).symm.toRingHom)
          (chartCoordinate i)))
  change (g3c_chartSections n m i j).comp
    (rename (R := ULift.{0} ℤ) (fun k => (k,j))).toRingHom p = ψ p
  apply DFunLike.congr_fun _ p
  apply MvPolynomial.ringHom_ext'
  · ext c
    obtain ⟨c⟩ := c
    simp only [RingHom.comp_apply]
    unfold ψ g3c_chartSections
    simp
    change (c : Γ(g3c_chart n m i j, ⊤)) = _
    rw [← map_intCast (tensorChartEquiv n m i j) c]
    congr 1
    have hc : (fromZeroRingHom (UniversalGrading n) (.powers (X i)))
        ((ProjectiveSpace.degreeZeroEquiv (Fin (n+1)) (ULift.{0} ℤ)).symm
          (ULift.up c)) = (c : Away (UniversalGrading n) (X i)) := by
      let f : ℤ →+* Away (UniversalGrading n) (X i) :=
        (fromZeroRingHom (UniversalGrading n) (.powers (X i))).comp
          ((ProjectiveSpace.degreeZeroEquiv (Fin (n+1)) (ULift.{0} ℤ)).symm.toRingHom.comp
            (ULift.ringEquiv (R := ℤ)).symm.toRingHom)
      exact DFunLike.congr_fun (Subsingleton.elim f (Int.castRingHom _)) c
    rw [hc]
    change algebraMap ℤ _ c = _
    rw [← Algebra.TensorProduct.includeLeft_apply (S := ℤ)
      (B := Away (UniversalGrading m) (X j : UniversalRing m))]
    rfl
  intro k
  simp only [RingHom.comp_apply]
  rw [show (rename (R := ULift.{0} ℤ) (fun k => (k,j))).toRingHom (X k) = X (k,j) by simp]
  unfold ψ
  simp only [RingHom.comp_apply, eval₂Hom_X']
  rw [g3c_chartSections_X]
  change g3c_fstCoord n m i j k * g3c_sndCoord n m i j j =
    tensorChartEquiv n m i j (Algebra.TensorProduct.includeLeft (R := ℤ) (S := ℤ)
      (B := Away (UniversalGrading m) (X j : UniversalRing m)) (chartCoordinate i k))
  rw [tensorChartEquiv_includeLeft]
  simp [g3c_sndCoord, chartCoordinate_self]

private theorem tensorChartEquiv_includeRight (n m : ℕ) (i : Fin (n+1)) (j : Fin (m+1))
    (l : Fin (m+1)) :
    tensorChartEquiv n m i j (Algebra.TensorProduct.includeRight (R := ℤ)
      (A := Away (UniversalGrading n) (X i : UniversalRing n))
      (chartCoordinate j l)) = g3c_sndCoord n m i j l := by
  have h : (chartTensorIso n m i j).hom ≫
      Spec.map (CommRingCat.ofHom ((Algebra.TensorProduct.includeRight (R := ℤ)
        (A := Away (UniversalGrading n) (X i : UniversalRing n))).toRingHom)) =
      pullback.snd (terminal.from (Spec (.of (Away (UniversalGrading n) (X i : UniversalRing n)))))
        (terminal.from (Spec (.of (Away (UniversalGrading m) (X j : UniversalRing m))))) := by
    simp [chartTensorIso]
  have ht := congrArg Scheme.Hom.appTop h
  rw [Scheme.Hom.comp_appTop] at ht
  change _ = (Scheme.Hom.appTop (pullback.snd _ _)).hom
    ((Scheme.ΓSpecIso (.of (Away (UniversalGrading m) (X j : UniversalRing m)))).inv.hom
      (chartCoordinate j l))
  rw [← ht]
  change (Scheme.Hom.appTop (chartTensorIso n m i j).hom).hom
      ((Scheme.ΓSpecIso _).inv.hom
        (Algebra.TensorProduct.includeRight (R := ℤ)
          (A := Away (UniversalGrading n) (X i : UniversalRing n)) (chartCoordinate j l))) =
    (Scheme.Hom.appTop (chartTensorIso n m i j).hom).hom
      ((Scheme.Hom.appTop (Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight (R := ℤ)
          (A := Away (UniversalGrading n) (X i : UniversalRing n))).toRingHom))).hom
        ((Scheme.ΓSpecIso _).inv.hom (chartCoordinate j l)))
  apply congrArg (Scheme.Hom.appTop (chartTensorIso n m i j).hom).hom
  exact congrArg (fun q => q.hom (chartCoordinate j l))
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom
      (Algebra.TensorProduct.includeRight (R := ℤ)
        (A := Away (UniversalGrading n) (X i : UniversalRing n))
        (B := Away (UniversalGrading m) (X j : UniversalRing m))).toRingHom))

set_option maxHeartbeats 400000 in
private theorem chartSections_rename_right (n m : ℕ) (i : Fin (n+1)) (j : Fin (m+1))
    (p : UniversalRing m) :
    g3c_chartSections n m i j (rename (fun l => (i, l)) p) =
      tensorChartEquiv n m i j (Algebra.TensorProduct.includeRight (R := ℤ)
        (A := Away (UniversalGrading n) (X i : UniversalRing n))
        (eval₂Hom ((fromZeroRingHom (UniversalGrading m) (.powers (X j))).comp
          (ProjectiveSpace.degreeZeroEquiv (Fin (m+1)) (ULift.{0} ℤ)).symm.toRingHom)
          (chartCoordinate j) p)) := by
  let ψ : UniversalRing m →+* Γ(g3c_chart n m i j, ⊤) :=
    (tensorChartEquiv n m i j).toRingHom.comp
      ((Algebra.TensorProduct.includeRight (R := ℤ)
        (A := Away (UniversalGrading n) (X i : UniversalRing n))).toRingHom.comp
        (eval₂Hom ((fromZeroRingHom (UniversalGrading m) (.powers (X j))).comp
          (ProjectiveSpace.degreeZeroEquiv (Fin (m+1)) (ULift.{0} ℤ)).symm.toRingHom)
          (chartCoordinate j)))
  change (g3c_chartSections n m i j).comp
    (rename (R := ULift.{0} ℤ) (fun l => (i,l))).toRingHom p = ψ p
  apply DFunLike.congr_fun _ p
  apply MvPolynomial.ringHom_ext'
  · ext c
    obtain ⟨c⟩ := c
    simp only [RingHom.comp_apply]
    unfold ψ g3c_chartSections
    simp
    change (c : Γ(g3c_chart n m i j, ⊤)) = _
    rw [← map_intCast (tensorChartEquiv n m i j) c]
    congr 1
    have hc : (fromZeroRingHom (UniversalGrading m) (.powers (X j)))
        ((ProjectiveSpace.degreeZeroEquiv (Fin (m+1)) (ULift.{0} ℤ)).symm
          (ULift.up c)) = (c : Away (UniversalGrading m) (X j)) := by
      let f : ℤ →+* Away (UniversalGrading m) (X j) :=
        (fromZeroRingHom (UniversalGrading m) (.powers (X j))).comp
          ((ProjectiveSpace.degreeZeroEquiv (Fin (m+1)) (ULift.{0} ℤ)).symm.toRingHom.comp
            (ULift.ringEquiv (R := ℤ)).symm.toRingHom)
      exact DFunLike.congr_fun (Subsingleton.elim f (Int.castRingHom _)) c
    rw [hc]
    change algebraMap ℤ _ c = _
    exact ((Algebra.TensorProduct.includeRight (R := ℤ)
      (A := Away (UniversalGrading n) (X i : UniversalRing n))).commutes c).symm
  intro l
  simp only [RingHom.comp_apply]
  rw [show (rename (R := ULift.{0} ℤ) (fun l => (i,l))).toRingHom (X l) = X (i,l) by simp]
  unfold ψ
  simp only [RingHom.comp_apply, eval₂Hom_X']
  rw [g3c_chartSections_X]
  change g3c_fstCoord n m i j i * g3c_sndCoord n m i j l =
    tensorChartEquiv n m i j (Algebra.TensorProduct.includeRight (R := ℤ)
      (A := Away (UniversalGrading n) (X i : UniversalRing n)) (chartCoordinate j l))
  rw [tensorChartEquiv_includeRight]
  simp [g3c_fstCoord, chartCoordinate_self]

set_option maxHeartbeats 400000 in
theorem spec_g3c_chartSections_surjective_aux (n m : ℕ)
    (i : Fin (n + 1)) (j : Fin (m + 1)) :
    Function.Surjective (g3c_chartSections n m i j) := by
  intro y
  let t := (tensorChartEquiv n m i j).symm y
  have ht : tensorChartEquiv n m i j t = y := (tensorChartEquiv n m i j).apply_symm_apply y
  suffices ∃ p, g3c_chartSections n m i j p = tensorChartEquiv n m i j t by
    obtain ⟨p, hp⟩ := this
    exact ⟨p, hp.trans ht⟩
  induction t using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | add x y hx hy =>
      obtain ⟨p, hp⟩ := hx
      obtain ⟨q, hq⟩ := hy
      refine ⟨p + q, ?_⟩
      calc
        g3c_chartSections n m i j (p + q) =
            g3c_chartSections n m i j p + g3c_chartSections n m i j q :=
          (g3c_chartSections n m i j).map_add p q
        _ = tensorChartEquiv n m i j x + tensorChartEquiv n m i j y :=
          congrArg₂ (fun a b : Γ(g3c_chart n m i j, ⊤) => a + b) hp hq
        _ = tensorChartEquiv n m i j (x + y) :=
          ((tensorChartEquiv n m i j).map_add x y).symm
  | tmul a b =>
      obtain ⟨p, hp⟩ := awayCoord_surj n i a
      obtain ⟨q, hq⟩ := awayCoord_surj m j b
      refine ⟨rename (fun k => (k,j)) p * rename (fun l => (i,l)) q, ?_⟩
      rw [map_mul, chartSections_rename_left, chartSections_rename_right, hp, hq]
      rw [← (tensorChartEquiv n m i j).map_mul]
      exact congrArg (tensorChartEquiv n m i j)
        (by simp [Algebra.TensorProduct.includeLeft_apply,
          Algebra.TensorProduct.includeRight_apply])
theorem spec_g3c_segre_isClosedImmersion_aux (n m : ℕ)
    (s : g3c_prod n m ⟶ g3c_segreTarget n m)
    (hs : ∀ i j, g3c_prodChartι n m i j ≫ s = g3c_chartMap n m i j) :
    IsClosedImmersion s := by
  rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := @IsClosedImmersion) _
    (Proj.iSup_basicOpen_eq_top _ _ (g3c_irrelevant_le_span_segre n m))]
  rintro ⟨i, j⟩
  refine g3c_isClosedImmersion_morphismRestrict_of_opensRange s _ (g3c_prodChartι n m i j)
    (spec_g3c_segre_preimage_basicOpen_aux n m s hs i j).symm ?_
  rw [hs, g3c_chartMap]
  exact g3c_isClosedImmersion_fromOfGlobalSections_restrict _ _ _
    (spec_g3c_chartSections_surjective_aux n m i j) (isHomogeneous_X _ (i, j))
    (g3c_chartSections_X_self n m i j)

/-! ### Part B: index bookkeeping and base change to `T` -/

theorem spec_g3c_nonempty_proj_iso_of_equiv_aux {ι ι' : Type} (e : ι ≃ ι') :
    Nonempty (Proj (homogeneousSubmodule ι (ULift.{0} ℤ)) ≅
      Proj (homogeneousSubmodule ι' (ULift.{0} ℤ))) := by
  let f : homogeneousSubmodule ι (ULift.{0} ℤ) →+*ᵍ
      homogeneousSubmodule ι' (ULift.{0} ℤ) :=
    { (rename e).toRingHom with
      map_mem := fun h => h.rename_isHomogeneous }
  let g : homogeneousSubmodule ι' (ULift.{0} ℤ) →+*ᵍ
      homogeneousSubmodule ι (ULift.{0} ℤ) :=
    { (rename e.symm).toRingHom with
      map_mem := fun h => h.rename_isHomogeneous }
  have hf : HomogeneousIdeal.irrelevant (homogeneousSubmodule ι' (ULift.{0} ℤ)) ≤
      (HomogeneousIdeal.irrelevant (homogeneousSubmodule ι (ULift.{0} ℤ))).map f := by
    intro x hx
    rw [← show f (g x) = x by simp [f, g]]
    apply Ideal.mem_map_of_mem
    rw [HomogeneousIdeal.mem_irrelevant_iff] at hx
    change GradedRing.proj (homogeneousSubmodule ι (ULift.{0} ℤ)) 0 (g x) = 0
    rw [GradedRing.proj_apply] at hx ⊢
    rw [← g.map_directSumDecompose, hx, map_zero]
  have hg : HomogeneousIdeal.irrelevant (homogeneousSubmodule ι (ULift.{0} ℤ)) ≤
      (HomogeneousIdeal.irrelevant (homogeneousSubmodule ι' (ULift.{0} ℤ))).map g := by
    intro x hx
    rw [← show g (f x) = x by simp [f, g]]
    apply Ideal.mem_map_of_mem
    rw [HomogeneousIdeal.mem_irrelevant_iff] at hx
    change GradedRing.proj (homogeneousSubmodule ι' (ULift.{0} ℤ)) 0 (f x) = 0
    rw [GradedRing.proj_apply] at hx ⊢
    rw [← f.map_directSumDecompose, hx, map_zero]
  let hom := Proj.map g hg
  let inv := Proj.map f hf
  refine ⟨⟨hom, inv, ?_, ?_⟩⟩
  · rw [← Proj.map_comp]
    have hgf : g.comp f = GradedRingHom.id _ := by
      ext x
      simp [f, g]
    simpa only [hgf] using
      (Proj.map_id (𝒜 := homogeneousSubmodule ι (ULift.{0} ℤ)))
  · rw [← Proj.map_comp]
    have hfg : f.comp g = GradedRingHom.id _ := by
      ext x
      simp [f, g]
    simpa only [hfg] using
      (Proj.map_id (𝒜 := homogeneousSubmodule ι' (ULift.{0} ℤ)))

theorem spec_g3c_pullback_projectiveSpace_iso_aux (T : Scheme.{0}) (n m : ℕ) :
    ∃ e : pullback (toBase (Fin (n + 1)) T) (toBase (Fin (m + 1)) T) ≅
        pullback (terminal.from T) (terminal.from (g3c_prod n m)),
      e.hom ≫ pullback.fst _ _ = pullback.fst _ _ ≫ toBase (Fin (n + 1)) T := by
  let L := pullback (toBase (Fin (n + 1)) T) (toBase (Fin (m + 1)) T)
  let R := pullback (terminal.from T) (terminal.from (g3c_prod n m))
  let toProd : L ⟶ g3c_prod n m := pullback.lift
    (pullback.fst _ _ ≫ pullback.snd _ _)
    (pullback.snd _ _ ≫ pullback.snd _ _)
    (terminal.hom_ext _ _)
  let hom : L ⟶ R := pullback.lift
    (pullback.fst _ _ ≫ pullback.fst _ _) toProd (terminal.hom_ext _ _)
  let toPn : R ⟶ ℙ(Fin (n + 1); T) := pullback.lift
    (pullback.fst _ _) (pullback.snd _ _ ≫ pullback.fst _ _) (terminal.hom_ext _ _)
  let toPm : R ⟶ ℙ(Fin (m + 1); T) := pullback.lift
    (pullback.fst _ _) (pullback.snd _ _ ≫ pullback.snd _ _) (terminal.hom_ext _ _)
  let inv : R ⟶ L := pullback.lift toPn toPm (by
    simp [toPn, toPm, ProjectiveSpace.toBase])
  have hom_inv : hom ≫ inv = 𝟙 L := by
    apply pullback.hom_ext
    · apply pullback.hom_ext <;> simp [hom, inv, toPn, toProd, L, R]
    · apply pullback.hom_ext
      · simpa [hom, inv, toPm, toProd, L, R, ProjectiveSpace.toBase] using
          (pullback.condition
            (f := toBase (Fin (n + 1)) T) (g := toBase (Fin (m + 1)) T))
      · simp [hom, inv, toPm, toProd, L, R]
  have inv_hom : inv ≫ hom = 𝟙 R := by
    apply pullback.hom_ext
    · simp [hom, inv, toPn, L, R]
    · apply pullback.hom_ext <;> simp [hom, inv, toPn, toPm, toProd, L, R]
  let e : L ≅ R := ⟨hom, inv, hom_inv, inv_hom⟩
  refine ⟨e, ?_⟩
  simp [e, hom, L, ProjectiveSpace.toBase]

theorem spec_g3c_segre_over_aux (T : Scheme.{0}) (n m : ℕ) :
    ∃ s : pullback (toBase (Fin (n + 1)) T) (toBase (Fin (m + 1)) T) ⟶
        ℙ(Fin (n * m + n + m + 1); T),
      IsClosedImmersion s ∧
        s ≫ toBase (Fin (n * m + n + m + 1)) T =
          pullback.fst _ _ ≫ toBase (Fin (n + 1)) T := by
  obtain ⟨σ, hσ, _⟩ := spec_g3c_existsUnique_segre_aux n m
  letI : IsClosedImmersion σ := spec_g3c_segre_isClosedImmersion_aux n m σ hσ
  let idxEquiv : Fin (n + 1) × Fin (m + 1) ≃ Fin (n * m + n + m + 1) :=
    finProdFinEquiv.trans (finCongr (by ring))
  obtain ⟨φ : g3c_segreTarget n m ≅ g3c_P (n * m + n + m)⟩ :=
    spec_g3c_nonempty_proj_iso_of_equiv_aux idxEquiv
  letI : IsClosedImmersion (σ ≫ φ.hom) := IsClosedImmersion.comp σ φ.hom
  obtain ⟨e, he⟩ := spec_g3c_pullback_projectiveSpace_iso_aux T n m
  let q := pullback.map (terminal.from T) (terminal.from (g3c_prod n m))
    (terminal.from T) (terminal.from (g3c_P (n * m + n + m)))
    (𝟙 T) (σ ≫ φ.hom) (𝟙 _) (by simp) (by simp)
  letI : MorphismProperty.IsStableUnderComposition @IsClosedImmersion :=
    MorphismProperty.IsMultiplicative.toIsStableUnderComposition
  have hq : IsClosedImmersion q := MorphismProperty.pullbackMap
    (P := @IsClosedImmersion) (i₁ := 𝟙 T) (i₂ := σ ≫ φ.hom)
    (by infer_instance) (by infer_instance) (by simp) (by simp)
  letI : IsClosedImmersion q := hq
  have hqfst : q ≫ pullback.fst _ _ = pullback.fst _ _ ≫ 𝟙 T := by
    dsimp [q]
    simp only [pullback.lift_fst]
  refine ⟨e.hom ≫ q, IsClosedImmersion.comp e.hom q, ?_⟩
  change (e.hom ≫ q) ≫ pullback.fst _ _ = _
  rw [Category.assoc, hqfst]
  simpa only [Category.comp_id] using he

theorem spec_g3c_isProjective_pullback_aux {X Y T : Scheme.{0}} (f : X ⟶ T) (g : Y ⟶ T)
    [IsProjective f] [IsProjective g] : IsProjective (pullback.fst f g ≫ f) := by
  obtain ⟨F⟩ := (inferInstance : IsProjective f).nonempty_presentation
  obtain ⟨G⟩ := (inferInstance : IsProjective g).nonempty_presentation
  letI : IsClosedImmersion F.immersion := F.isClosedImmersion
  letI : IsClosedImmersion G.immersion := G.isClosedImmersion
  obtain ⟨s, hs, hsover⟩ := spec_g3c_segre_over_aux T F.ambientDimension G.ambientDimension
  let i := pullback.map f g
    (toBase (Fin (F.ambientDimension + 1)) T)
    (toBase (Fin (G.ambientDimension + 1)) T)
    F.immersion G.immersion (𝟙 T)
    (by simpa using F.immersion_toBase.symm)
    (by simpa using G.immersion_toBase.symm)
  letI : MorphismProperty.IsStableUnderComposition @IsClosedImmersion :=
    MorphismProperty.IsMultiplicative.toIsStableUnderComposition
  have hi : IsClosedImmersion i := MorphismProperty.pullbackMap
    (P := @IsClosedImmersion) (i₁ := F.immersion) (i₂ := G.immersion)
    (by infer_instance) (by infer_instance) F.immersion_toBase.symm G.immersion_toBase.symm
  letI : IsClosedImmersion i := hi
  letI : IsClosedImmersion s := hs
  let d := F.ambientDimension * G.ambientDimension + F.ambientDimension + G.ambientDimension
  refine ⟨⟨{ ambientDimension := d, immersion := i ≫ s, immersion_toBase := ?_ }⟩⟩
  rw [Category.assoc, hsover]
  simp only [← Category.assoc]
  change (i ≫ pullback.fst _ _) ≫ toBase _ T = _
  rw [show i ≫ pullback.fst _ _ = pullback.fst f g ≫ F.immersion by
    dsimp [i]
    simp only [pullback.lift_fst]]
  rw [Category.assoc, F.immersion_toBase]

/-! ### Part C: the power `A^r` -/

theorem spec_g3c_isProjective_power_aux (A : Over (Spec ↧ℂ)) [IsProjective A.hom] (r : ℕ) :
    IsProjective (HodgeLean.Adapters.g3_power A r).hom := by
  induction r with
  | zero => exact HodgeLean.Adapters.spec_g3_isProjective_power_zero A
  | succ r ih =>
      exact spec_g3c_isProjective_pullback_aux A.hom
        (HodgeLean.Adapters.g3_power A r).hom

/-! ### Degenerate checks and falsification -/

set_option maxHeartbeats 400000 in
theorem spec_g3c_isIso_terminal_from_P_zero_aux : IsIso (terminal.from (g3c_P 0)) := by
  let G := homogeneousSubmodule (Fin 1) (ULift.{0} ℤ)
  let x : MvPolynomial (Fin 1) (ULift.{0} ℤ) := X 0
  let A := HomogeneousLocalization.Away G x
  let α : G 0 →+* A := HomogeneousLocalization.fromZeroRingHom G (Submonoid.powers x)
  have hα_surj : Function.Surjective α := by
    intro z
    have hgen := HomogeneousLocalization.Away.adjoin_mk_prod_pow_eq_top
      (MvPolynomial.isHomogeneous_X (ULift.{0} ℤ) (0 : Fin 1))
      (Fin 1) (fun j ↦ MvPolynomial.X j)
      (adjoin_coordinates_eq_top 0) (fun _ ↦ (1 : ℕ))
      (fun j ↦ MvPolynomial.isHomogeneous_X (ULift.{0} ℤ) j)
    have hbot : (⊥ : Subalgebra (G 0) A) = ⊤ := by
      rw [← hgen]
      apply le_antisymm bot_le
      rw [Algebra.adjoin_le_iff]
      rintro y ⟨a, ai, hai, hai_le, rfl⟩
      have hai' : ∑ j, ai j = a := by simpa using hai
      rw [chartGenerator_eq_prod (0 : Fin 1) ai hai']
      have hone : ∏ j, chartCoordinate (0 : Fin 1) j ^ ai j = (1 : A) := by
        rw [Fin.prod_univ_one]
        simp only [chartCoordinate_self, one_pow]
      rw [hone]
      exact one_mem _
    have hz : z ∈ (⊥ : Subalgebra (G 0) A) := by
      rw [hbot]
      trivial
    rw [Algebra.mem_bot] at hz
    simpa [α, G, A, HomogeneousLocalization.algebraMap_eq] using hz
  have hα_inj : Function.Injective α := by
    have hpow : Submonoid.powers x ≤
        nonZeroDivisors (MvPolynomial (Fin 1) (ULift.{0} ℤ)) := by
      intro y hy
      obtain ⟨k, rfl⟩ := hy
      exact (MvPolynomial.isRegular_X_pow
        (R := ULift.{0} ℤ) (n := (0 : Fin 1)) k).mem_nonZeroDivisors
    intro a b hab
    apply Subtype.ext
    exact IsLocalization.injective (Localization (Submonoid.powers x)) hpow
      (congrArg HomogeneousLocalization.val hab)
  let e : G 0 ≃+* A := RingEquiv.ofBijective α ⟨hα_inj, hα_surj⟩
  have hterminal0 : IsTerminal (Spec ↧(G 0)) :=
    IsTerminal.ofIso specULiftZIsTerminal
      (Scheme.Spec.mapIso
        (ProjectiveSpace.degreeZeroEquiv (Fin 1) (ULift.{0} ℤ)).toCommRingCatIso.op)
  have hterminalA : IsTerminal (Spec ↧A) :=
    hterminal0.ofIso (Scheme.Spec.mapIso e.toCommRingCatIso.op).symm
  let j : Spec ↧A ⟶ g3c_P 0 := Proj.awayι G x
    (MvPolynomial.isHomogeneous_X (ULift.{0} ℤ) (0 : Fin 1)) zero_lt_one
  have hjrange : j.opensRange = ⊤ := by
    rw [show j.opensRange = Proj.basicOpen G x by
      exact Proj.opensRange_awayι G x _ _]
    simpa [G, x] using iSup_coordinateBasicOpen_eq_top 0
  letI : IsIso j := isIso_of_isOpenImmersion_of_opensRange_eq_top j hjrange
  have hterminalP : IsTerminal (g3c_P 0) := hterminalA.ofIso (asIso j)
  exact isIso_of_isTerminal hterminalP terminalIsTerminal _

section D2General
universe u
variable {σ : Type*} {A : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜]

theorem g3c_d2_bijective_away {X : Scheme.{u}} (f : A →+* Γ(X, ⊤))
    (hf : Function.Surjective f) {t : A} (ht : t ∈ 𝒜 1) (h1 : f t = 1)
    (hinj : ∀ (k : ℕ) (a : A), a ∈ 𝒜 k → f a = 0 → a = 0)
    (φ : Away 𝒜 t →+* Localization.Away (f t))
    (hφ : ∀ (i : ℕ) (x : A) (hx : x ∈ 𝒜 (i • 1)),
      φ (Away.mk 𝒜 ht i x hx) = algebraMap _ _ (f x)) :
    Function.Bijective φ := by
  classical
  refine ⟨(injective_iff_map_eq_zero φ).mpr fun z hz => ?_, fun z => ?_⟩
  · obtain ⟨k, a, ha, rfl⟩ := Away.mk_surjective 𝒜 ht z
    rw [hφ] at hz
    have hinj1 : Function.Injective (algebraMap Γ(X, ⊤) (Localization.Away (f t))) :=
      IsLocalization.injective _ (M := Submonoid.powers (f t)) (by
        rw [h1, Submonoid.powers_one]; exact bot_le)
    have : f a = 0 := hinj1 (by rw [hz, map_zero])
    have ha0 := hinj _ a ha this
    subst ha0
    rw [HomogeneousLocalization.ext_iff_val]
    simp only [Away.val_mk, val_zero]
    exact Localization.mk_zero _
  · obtain ⟨⟨y, ⟨_, k, rfl⟩⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers (f t)) z
    obtain ⟨a, rfl⟩ := hf y
    have hk : (⟨f t ^ k, k, rfl⟩ : Submonoid.powers (f t)) = 1 := Subtype.ext (by simp [h1])
    rw [hk]
    dsimp only
    rw [IsLocalization.mk'_one, ← DirectSum.sum_support_decompose 𝒜 a, map_sum, map_sum]
    refine ⟨∑ i ∈ (DirectSum.decompose 𝒜 a).support,
      Away.mk 𝒜 ht i (DirectSum.decompose 𝒜 a i)
        (by rw [smul_eq_mul, mul_one]; exact (DirectSum.decompose 𝒜 a i).2), ?_⟩
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => hφ _ _ _

theorem g3c_d2_isIso_toBasicOpenOfGlobalSections {X : Scheme.{u}} [IsAffine X]
    (f : A →+* Γ(X, ⊤)) (hf : Function.Surjective f) {t : A} (ht : t ∈ 𝒜 1) (h1 : f t = 1)
    (hinj : ∀ (k : ℕ) (a : A), a ∈ 𝒜 k → f a = 0 → a = 0) :
    IsIso (Proj.toBasicOpenOfGlobalSections 𝒜 f rfl zero_lt_one ht) := by
  unfold Proj.toBasicOpenOfGlobalSections
  simp only [Category.assoc]
  change MorphismProperty.isomorphisms _ _
  rw [MorphismProperty.cancel_left_of_respectsIso (MorphismProperty.isomorphisms _),
    MorphismProperty.cancel_left_of_respectsIso (MorphismProperty.isomorphisms _),
    MorphismProperty.cancel_left_of_respectsIso (MorphismProperty.isomorphisms _),
    MorphismProperty.cancel_right_of_respectsIso (MorphismProperty.isomorphisms _)]
  change IsIso _
  rw [isIso_SpecMap_iff]
  refine g3c_d2_bijective_away 𝒜 f hf ht h1 hinj _ fun i x hx => ?_
  simp only [CommRingCat.hom_ofHom, RingHom.coe_comp, Function.comp_apply,
    HomogeneousLocalization.algebraMap_apply, HomogeneousLocalization.Away.val_mk,
    Localization.mk_eq_mk', IsLocalization.map_mk']
  rw [IsLocalization.mk'_eq_iff_eq_mul]
  simp [h1]

theorem g3c_d2_isIso_fromOfGlobalSections_restrict {X : Scheme.{u}} [IsAffine X]
    (f : A →+* Γ(X, ⊤)) (hf : (HomogeneousIdeal.irrelevant 𝒜).toIdeal.map f = ⊤)
    (hsurj : Function.Surjective f) {t : A} (ht : t ∈ 𝒜 1) (h1 : f t = 1)
    (hinj : ∀ (k : ℕ) (a : A), a ∈ 𝒜 k → f a = 0 → a = 0) :
    IsIso (Proj.fromOfGlobalSections 𝒜 f hf ∣_ Proj.basicOpen 𝒜 t) := by
  rw [Proj.fromOfGlobalSections_morphismRestrict _ _ _ zero_lt_one ht]
  have := g3c_d2_isIso_toBasicOpenOfGlobalSections 𝒜 f hsurj ht h1 hinj
  infer_instance

end D2General

theorem g3c_d2_isIso_morphismRestrict_of_opensRange {X Y Z : Scheme.{0}} (f : X ⟶ Y)
    (U : Y.Opens) (ι : Z ⟶ X) [IsOpenImmersion ι] (hι : ι.opensRange = f ⁻¹ᵁ U)
    (h : IsIso ((ι ≫ f) ∣_ U)) : IsIso (f ∣_ U) := by
  have : IsIso (ι ∣_ (f ⁻¹ᵁ U)) := by
    rw [isIso_iff_isOpenImmersion_and_surjective]
    refine ⟨inferInstance, ⟨fun y => ?_⟩⟩
    obtain ⟨z, hz⟩ : y.1 ∈ Set.range ι := by
      change y.1 ∈ ι.opensRange
      rw [hι]
      exact y.2
    refine ⟨⟨z, ?_⟩, Subtype.ext ?_⟩
    · change ι z ∈ f ⁻¹ᵁ U
      rw [hz]
      exact y.2
    · rw [morphismRestrict_base_coe]
      exact hz
  rw [morphismRestrict_comp] at h
  exact IsIso.of_isIso_comp_left (ι ∣_ (f ⁻¹ᵁ U)) _

theorem g3c_d2_irrelevant_le_span (n m : ℕ) :
    (HomogeneousIdeal.irrelevant (g3c_segreGrading n m)).toIdeal ≤
      Ideal.span (Set.range (MvPolynomial.X :
        Fin (n + 1) × Fin (m + 1) → MvPolynomial (Fin (n + 1) × Fin (m + 1)) (ULift.{0} ℤ))) := by
  rw [HomogeneousIdeal.irrelevant_eq_span, Ideal.span_le]
  intro r hr
  simp only [Set.mem_iUnion] at hr
  obtain ⟨d, hd0, hr⟩ := hr
  have hrpow : r ∈ Ideal.span (Set.range (MvPolynomial.X :
      Fin (n + 1) × Fin (m + 1) → MvPolynomial (Fin (n + 1) × Fin (m + 1)) (ULift.{0} ℤ))) ^ d := by
    rw [Ideal.span_pow_eq_map_homogeneousSubmodule]
    exact ⟨MvPolynomial.map MvPolynomial.C r, hr.map _, by simp⟩
  exact Ideal.pow_le_self hd0.ne' hrpow

set_option backward.isDefEq.respectTransparency true in
theorem g3c_d2_val_awayCoord (n : ℕ) (i : Fin (n + 1)) (k : ℕ) (p : UniversalRing.{0} n)
    (hp : p.IsHomogeneous k) :
    (eval₂Hom ((fromZeroRingHom (UniversalGrading n) (.powers (X i : UniversalRing n))).comp
          (ProjectiveSpace.degreeZeroEquiv (Fin (n+1)) (ULift.{0} ℤ)).symm.toRingHom)
          (chartCoordinate i) p).val =
      Localization.mk p (⟨X i ^ k, k, rfl⟩ : Submonoid.powers (X i : UniversalRing n)) := by
  conv_rhs => rw [p.as_sum]
  conv_lhs => rw [p.as_sum]
  rw [map_sum, Localization.mk_sum]
  rw [show ∀ (s : Finset _) (g : _ → Away (UniversalGrading.{0} n) (X i : UniversalRing.{0} n)),
      (∑ d ∈ s, g d).val = ∑ d ∈ s, (g d).val from fun s g => map_sum (algebraMap (Away (UniversalGrading.{0} n) (X i : UniversalRing.{0} n)) (Localization.Away (X i : UniversalRing.{0} n))) g s]
  refine Finset.sum_congr rfl fun d hd => ?_
  rw [eval₂Hom_monomial, monomial_eq, Finsupp.prod, Finsupp.prod, val_mul]
  have h1 : (((fromZeroRingHom (UniversalGrading.{0} n) (Submonoid.powers (X i))).comp
      (degreeZeroEquiv (Fin (n + 1)) (ULift.{0, 0} ℤ)).symm.toRingHom) (p.coeff d)).val =
      Localization.mk (C (p.coeff d)) 1 := rfl
  have h2 : (∏ a ∈ d.support, chartCoordinate i a ^ d a).val =
      ∏ a ∈ d.support, Localization.mk (X a ^ d a)
        ((⟨X i ^ 1, 1, rfl⟩ : Submonoid.powers (X i : UniversalRing.{0} n)) ^ d a) := by
    induction d.support using Finset.induction with
    | empty => exact HomogeneousLocalization.val_one
    | @insert a s has ih =>
        rw [Finset.prod_insert has, Finset.prod_insert has, HomogeneousLocalization.val_mul,
          HomogeneousLocalization.val_pow, ih, ← Localization.mk_pow]
        rfl
  rw [h1, h2, Localization.mk_prod, Localization.mk_mul, one_mul]
  congr 1
  apply Subtype.ext
  simp only [SubmonoidClass.coe_finsetProd, SubmonoidClass.coe_pow, pow_one]
  rw [Finset.prod_pow_eq_pow_sum, ← hp.degree_eq_sum_deg_support hd]

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- The ring map `ℤ[y_0/y_j, …, y_m/y_j] → ℤ` evaluating every ratio at `1`.
Source: Mathlib `Localization.awayLift`, `MvPolynomial.eval₂Hom`. -/
def g3c_d2_awayEval (m : ℕ) (j : Fin (m + 1)) :
    Away (UniversalGrading.{0} m) (X j : UniversalRing.{0} m) →+* ℤ :=
  (Localization.awayLift (eval₂Hom (ULift.ringEquiv.toRingHom) (fun _ => (1 : ℤ)))
      (X j : UniversalRing.{0} m) (by simp)).comp
    (algebraMap (Away (UniversalGrading.{0} m) (X j : UniversalRing.{0} m))
      (Localization.Away (X j : UniversalRing.{0} m)))

example (m : ℕ) (j : Fin (m + 1)) :
    Away (UniversalGrading.{0} m) (X j : UniversalRing.{0} m) →+* ℤ := g3c_d2_awayEval m j

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
theorem g3c_d2_includeLeft_injective (n m : ℕ) (i : Fin (n + 1)) (j : Fin (m + 1)) :
    Function.Injective (Algebra.TensorProduct.includeLeft (R := ℤ) (S := ℤ)
      (A := Away (UniversalGrading.{0} n) (X i : UniversalRing.{0} n))
      (B := Away (UniversalGrading.{0} m) (X j : UniversalRing.{0} m))) := by
  let L := (TensorProduct.rid ℤ
      (Away (UniversalGrading.{0} n) (X i : UniversalRing.{0} n))).toLinearMap.comp
    (LinearMap.lTensor _ (AddMonoidHom.toIntLinearMap
      (M := Away (UniversalGrading.{0} m) (X j : UniversalRing.{0} m)) (M₂ := ℤ)
      (g3c_d2_awayEval m j).toAddMonoidHom))
  refine Function.LeftInverse.injective (g := L) fun a => ?_
  simp [L, Algebra.TensorProduct.includeLeft_apply]

set_option backward.isDefEq.respectTransparency true in
theorem g3c_d2_chartSections_inj (n : ℕ) (i : Fin (n + 1)) (k : ℕ)
    (a : MvPolynomial (Fin (n + 1) × Fin 1) (ULift.{0} ℤ)) (ha : a ∈ g3c_segreGrading n 0 k)
    (h0 : g3c_chartSections n 0 i 0 a = 0) : a = 0 := by
  let p : UniversalRing.{0} n := rename Prod.fst a
  have hpa : rename (fun k => (k, (0 : Fin 1))) p = a := by
    simp only [p, rename_rename]
    convert rename_id_apply a
    ext ⟨k, l⟩
    · rfl
    · exact congrArg Fin.val (Fin.fin_one_eq_zero l).symm
  have hp : p.IsHomogeneous k := IsHomogeneous.rename_isHomogeneous ha
  rw [← hpa, chartSections_rename_left] at h0
  have h1 := (tensorChartEquiv n 0 i 0).injective (h0.trans (map_zero _).symm)
  have h2 := g3c_d2_includeLeft_injective n 0 i 0 (h1.trans (map_zero _).symm)
  have h3 := congrArg HomogeneousLocalization.val h2
  rw [g3c_d2_val_awayCoord n i k p hp, val_zero, Localization.mk_eq_mk',
    IsLocalization.mk'_eq_zero_iff] at h3
  obtain ⟨⟨_, N, rfl⟩, hN⟩ := h3
  have : IsDomain (ULift.{0} ℤ) := (ULift.ringEquiv (R := ℤ)).toMulEquiv.isDomain
  have hp0 : p = 0 := (mul_eq_zero.mp hN).resolve_left (pow_ne_zero _ (X_ne_zero _))
  rw [← hpa, hp0, map_zero]

theorem spec_g3c_segre_isIso_right_zero_aux (n : ℕ) (s : g3c_prod n 0 ⟶ g3c_segreTarget n 0)
    (hs : ∀ i j, g3c_prodChartι n 0 i j ≫ s = g3c_chartMap n 0 i j) : IsIso s := by
  change MorphismProperty.isomorphisms _ s
  rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := MorphismProperty.isomorphisms _) _
    (Proj.iSup_basicOpen_eq_top _ _ (g3c_d2_irrelevant_le_span n 0))]
  rintro ⟨i, j⟩
  obtain rfl : j = 0 := Fin.fin_one_eq_zero j
  refine g3c_d2_isIso_morphismRestrict_of_opensRange s _ (g3c_prodChartι n 0 i 0)
    (spec_g3c_segre_preimage_basicOpen_aux n 0 s hs i 0).symm ?_
  rw [hs, g3c_chartMap]
  exact g3c_d2_isIso_fromOfGlobalSections_restrict _ _ _
    (spec_g3c_chartSections_surjective_aux n 0 i 0) (isHomogeneous_X _ (i, 0))
    (g3c_chartSections_X_self n 0 i 0) (g3c_d2_chartSections_inj n i)

theorem spec_g3c_isEmpty_proj_fin_zero_aux :
    IsEmpty (Proj (homogeneousSubmodule (Fin 0) (ULift.{0} ℤ))) := by
  constructor
  intro x
  apply x.not_irrelevant_le
  intro p hp
  rw [HomogeneousIdeal.mem_irrelevant_iff] at hp
  have hhom : p.IsHomogeneous 0 :=
    MvPolynomial.isHomogeneous_of_isEmpty (σ := Fin 0) (ULift.{0} ℤ) p
  have hproj : GradedRing.proj (homogeneousSubmodule (Fin 0) (ULift.{0} ℤ)) 0 p = p := by
    exact DirectSum.decompose_of_mem_same _
      (show p ∈ homogeneousSubmodule (Fin 0) (ULift.{0} ℤ) 0 from hhom)
  rw [hproj] at hp
  simp [hp]

theorem spec_g3c_isProjective_of_isEmpty_aux {X T : Scheme.{0}} [IsEmpty X] (f : X ⟶ T) :
    IsProjective f := by
  refine ⟨⟨{
    ambientDimension := 0
    immersion := isInitialOfIsEmpty.to _
    immersion_toBase := isInitialOfIsEmpty.hom_ext _ _ }⟩⟩

private theorem g3c_not_isProper_affineLine :
    ¬ IsProper (𝔸(Fin 1; Spec ↧ℂ) ↘ Spec ↧ℂ) := by
  intro hproper
  have haffine : IsAffineHom (𝔸(Fin 1; Spec ↧ℂ) ↘ Spec ↧ℂ) := inferInstance
  have hfinite : IsFinite (𝔸(Fin 1; Spec ↧ℂ) ↘ Spec ↧ℂ) :=
    IsFinite.iff_isProper_and_isAffineHom.mpr ⟨hproper, haffine⟩
  letI : IsFinite (𝔸(Fin 1; Spec ↧ℂ) ↘ Spec ↧ℂ) := hfinite
  have hcomp : IsFinite ((AffineSpace.SpecIso (Fin 1) ↧ℂ).inv ≫
      (𝔸(Fin 1; Spec ↧ℂ) ↘ Spec ↧ℂ)) := inferInstance
  rw [AffineSpace.SpecIso_inv_over] at hcomp
  have hr := (IsFinite.SpecMap_iff _).mp hcomp
  have hint := hr.to_isIntegral (MvPolynomial.X (0 : Fin 1))
  have hint' : IsAlgebraic ℂ
      (MvPolynomial.X (0 : Fin 1) : MvPolynomial (Fin 1) ℂ) := by
    obtain ⟨p, hp, hroot⟩ := hint
    refine ⟨p, hp.ne_zero, ?_⟩
    change Polynomial.eval₂ (algebraMap ℂ (MvPolynomial (Fin 1) ℂ))
      (MvPolynomial.X (0 : Fin 1)) p = 0
    simpa only [CommRingCat.hom_ofHom, MvPolynomial.algebraMap_eq] using hroot
  exact (MvPolynomial.transcendental_X ℂ (0 : Fin 1)) hint'

theorem spec_g3c_not_isProjective_affineLine_aux :
    ¬ IsProjective (𝔸(Fin 1; Spec ↧ℂ) ↘ Spec ↧ℂ) := by
  intro hp
  letI : IsProjective (𝔸(Fin 1; Spec ↧ℂ) ↘ Spec ↧ℂ) := hp
  exact g3c_not_isProper_affineLine inferInstance

private theorem g3c_projectiveLine_toBase_surjective :
    Surjective (toBase (Fin 2) (Spec ↧ℂ)) := by
  let v : ComplexProjectiveSpace.CoordinateSpace 1 := fun _ => 1
  have hv : v ≠ 0 := by
    intro h
    have := congrFun h 0
    simp [v] at this
  let sec := ComplexProjectiveSpace.vectorToProjectiveSpace v hv
  have hs : sec ≫ toBase (Fin 2) (Spec ↧ℂ) = 𝟙 _ := by
    exact ComplexProjectiveSpace.vectorToProjectiveSpace_toBase v hv
  letI : Surjective (sec ≫ toBase (Fin 2) (Spec ↧ℂ)) := hs ▸ inferInstance
  exact Surjective.of_comp sec (toBase (Fin 2) (Spec ↧ℂ))

theorem spec_g3c_not_isProjective_affineLine_prod_aux :
    ¬ IsProjective (pullback.fst (𝔸(Fin 1; Spec ↧ℂ) ↘ Spec ↧ℂ) (toBase (Fin 2) (Spec ↧ℂ)) ≫
      (𝔸(Fin 1; Spec ↧ℂ) ↘ Spec ↧ℂ)) := by
  intro hp
  let f := (𝔸(Fin 1; Spec ↧ℂ) ↘ Spec ↧ℂ)
  let g := toBase (Fin 2) (Spec ↧ℂ)
  let p := pullback.fst f g
  letI : IsProjective (p ≫ f) := hp
  letI : UniversallyClosed (p ≫ f) := inferInstance
  letI : Surjective g := by
    dsimp [g]
    exact g3c_projectiveLine_toBase_surjective
  letI : Surjective p := by dsimp [p]; infer_instance
  letI : UniversallyClosed f := UniversallyClosed.of_comp_surjective p f
  have hproper : IsProper f := by constructor
  exact g3c_not_isProper_affineLine hproper

end HodgeLean.Foundations
