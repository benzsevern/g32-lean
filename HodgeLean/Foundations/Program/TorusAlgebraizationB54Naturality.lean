import HodgeLean.Foundations.SegreProjectiveProofs

noncomputable section
open CategoryTheory AlgebraicGeometry HomogeneousLocalization
namespace HodgeLean.Foundations.Program

universe u
variable {A B σ τ : Type u} [CommRing A] [CommRing B]
    [SetLike σ A] [AddSubgroupClass σ A] [SetLike τ B] [AddSubgroupClass τ B]
    {G : ℕ → σ} {H : ℕ → τ} [GradedRing G] [GradedRing H]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem b54_toBasic_graded_natural {X : Scheme.{u}} (f : G →+*ᵍ H)
    (hf : HomogeneousIdeal.irrelevant H ≤ (HomogeneousIdeal.irrelevant G).map f)
    (e : B →+* Γ(X, ⊤)) {r : A} {n : ℕ} (hr : r ∈ G n) (hn : 0 < n) :
    Proj.toBasicOpenOfGlobalSections H e rfl hn (f.map_mem hr) ≫
      (Proj.basicOpen H (f r)).ι ≫ Proj.map f hf =
    Proj.toBasicOpenOfGlobalSections G (e.comp f.toRingHom) rfl hn hr ≫
      (Proj.basicOpen G r).ι := by
  rw [g3c_toBasic_eq, g3c_toBasic_eq]
  simp only [Category.assoc, Proj.basicOpenIsoSpec_inv_ι, Proj.basicOpenIsoSpec_inv_ι_assoc]
  rw [← Category.assoc _ (Proj.basicOpen H (f r)).ι]
  change _ ≫ _ ≫ Proj.awayι H (f r) (f.map_mem hr) hn ≫ Proj.map f hf = _
  rw [Proj.awayι_comp_map]
  simp only [← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp]
  congr 2
  congr 1
  ext q
  obtain ⟨m, a, ha, rfl⟩ := Away.mk_surjective G hr q
  simp [Away.map_mk, RingHom.comp_apply, HomogeneousLocalization.algebraMap_apply,
    Away.val_mk, Localization.mk_eq_mk', IsLocalization.map_mk']
  all_goals assumption

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem b54_fromOfGlobalSections_graded_natural {X : Scheme.{u}} (f : G →+*ᵍ H)
    (hf : HomogeneousIdeal.irrelevant H ≤ (HomogeneousIdeal.irrelevant G).map f)
    (e : B →+* Γ(X, ⊤))
    (he : (HomogeneousIdeal.irrelevant H).toIdeal.map e = ⊤)
    (he' : (HomogeneousIdeal.irrelevant G).toIdeal.map (e.comp f.toRingHom) = ⊤) :
    Proj.fromOfGlobalSections H e he ≫ Proj.map f hf =
      Proj.fromOfGlobalSections G (e.comp f.toRingHom) he' := by
  refine (Proj.openCoverOfMapIrrelevantEqTop G _ he').hom_ext _ _ fun ri ↦ ?_
  obtain ⟨n, r, hn, hr⟩ := ri
  change (X.basicOpen (e (f r))).ι ≫ (Proj.fromOfGlobalSections H e he ≫ Proj.map f hf) =
    (X.basicOpen ((e.comp f.toRingHom) r)).ι ≫
      Proj.fromOfGlobalSections G (e.comp f.toRingHom) he'
  rw [← Category.assoc]
  erw [g3c_ι_fromOfGlobalSections H e he hn (f.map_mem hr),
    g3c_ι_fromOfGlobalSections G (e.comp f.toRingHom) he' hn hr, Category.assoc]
  exact b54_toBasic_graded_natural f hf e hr hn

def b54_awayEvaluation {K : Type*} [CommRing K] (q : A →+* K) (r : A)
    (hr : IsUnit (q r)) : Away G r →+* K :=
  (IsLocalization.Away.lift (S := Localization.Away r) r hr).comp
    (algebraMap (Away G r) (Localization.Away r))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem b54_fromOfGlobalSections_eq_awayEvaluation {K : Type u} [CommRing K]
    (q : A →+* K) {r : A} {n : ℕ} (hr : r ∈ G n) (hn : 0 < n)
    (hu : IsUnit (q r))
    (hq : (HomogeneousIdeal.irrelevant G).toIdeal.map
      ((Scheme.ΓSpecIso (.of K)).inv.hom.comp q) = ⊤) :
    Proj.fromOfGlobalSections G ((Scheme.ΓSpecIso (.of K)).inv.hom.comp q) hq =
      Spec.map (CommRingCat.ofHom (b54_awayEvaluation (G := G) q r hu)) ≫
        Proj.awayι G r hr hn := by
  let e := (Scheme.ΓSpecIso (.of K)).inv.hom.comp q
  have he : IsUnit (e r) := hu.map (Scheme.ΓSpecIso (.of K)).inv.hom
  have hU : (Spec (.of K)).basicOpen (e r) = ⊤ := Scheme.basicOpen_of_isUnit _ he
  have : IsIso ((Spec (.of K)).basicOpen (e r)).ι := by
    rw [hU]
    change IsIso (Spec (.of K)).topIso.hom
    infer_instance
  apply (cancel_epi ((Spec (.of K)).basicOpen (e r)).ι).mp
  rw [g3c_ι_fromOfGlobalSections G e hq hn hr, g3c_toBasic_eq]
  simp only [Category.assoc, Proj.basicOpenIsoSpec_inv_ι]
  have hmap : (IsLocalization.map (M := Submonoid.powers r)
      (T := Submonoid.powers (e r)) (Localization.Away (e r)) e
        (by rw [← Submonoid.map_le_iff_le_comap, Submonoid.map_powers])) =
      (algebraMap _ (Localization.Away (e r))).comp
        ((Scheme.ΓSpecIso (.of K)).inv.hom.comp
          (IsLocalization.Away.lift (S := Localization.Away r) r hu)) := by
    apply IsLocalization.ringHom_ext (M := Submonoid.powers r)
    ext a
    simp [IsLocalization.map_eq, IsLocalization.Away.lift_eq, e]
  rw [hmap, RingHom.comp_assoc, RingHom.comp_assoc]
  simp only [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]
  rw [g3c_basicOpenToSpecAway_spec_assoc]
  simp only [b54_awayEvaluation, CommRingCat.ofHom_comp, Spec.map_comp,
    Category.assoc, CommRingCat.ofHom_hom, toSpecΓ_SpecMap_ΓSpecIso_inv_assoc]

theorem b54_awayEvaluation_mk (q : A →+* ℂ) {r : A} {n : ℕ}
    (hr : r ∈ G n) (hu : IsUnit (q r)) (k : ℕ) (a : A) (ha : a ∈ G (k • n)) :
    b54_awayEvaluation (G := G) q r hu (Away.mk G hr k a ha) =
      q a * (q r)⁻¹ ^ k := by
  simp only [b54_awayEvaluation, RingHom.coe_comp, Function.comp_apply]
  change (Localization.awayLift q r hu)
      (Localization.mk a ⟨r ^ k, ⟨k, rfl⟩⟩) = _
  rw [Localization.awayLift_mk q r a (q r)⁻¹]
  exact mul_inv_cancel₀ hu.ne_zero

theorem b54_awayEvaluation_fromZero {K : Type*} [CommRing K]
    (q : A →+* K) (r : A) (hu : IsUnit (q r)) (a : G 0) :
    b54_awayEvaluation (G := G) q r hu (fromZeroRingHom G (.powers r) a) = q a := by
  change (IsLocalization.Away.lift (S := Localization.Away r) r hu)
    (algebraMap A (Localization.Away r) a) = q a
  exact IsLocalization.Away.lift_eq r hu a

end HodgeLean.Foundations.Program
