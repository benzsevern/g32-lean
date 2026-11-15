import HodgeLean.Foundations.Program.SchoenTowerI1aPre2Splits

/-! # Restriction maps between invariant affine spectra
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- The invariant restriction homomorphism gives the square of affine quotient maps.
Source: SGA 1, Exposé V, §1, affine quotient restrictions. -/
theorem s2v_i1alo_restriction_square
    (X : Over (Spec ↧ℂ)) (G : Type) (a : G → (X ⟶ X))
    (U V : X.left.Opens) (hVU : V ≤ U)
    (hiU : ∀ g, U ≤ (a g).left ⁻¹ᵁ U)
    (hiV : ∀ g, V ≤ (a g).left ⁻¹ᵁ V)
    (f : s2v_i1a_chartInvariants X G a U hiU →+*
      s2v_i1a_chartInvariants X G a V hiV)
    (hf : ∀ t, (f t).val = (X.left.presheaf.map (homOfLE hVU).op).hom t.val) :
    s2v_i1a_affineQuotientMap X G a V hiV ≫ Spec.map (CommRingCat.ofHom f) =
      X.left.homOfLE hVU ≫ s2v_i1a_affineQuotientMap X G a U hiU := by
  have hf' : CommRingCat.ofHom f ≫
      CommRingCat.ofHom (s2v_i1a_chartInvariants X G a V hiV).subtype =
      CommRingCat.ofHom (s2v_i1a_chartInvariants X G a U hiU).subtype ≫
        X.left.presheaf.map (homOfLE hVU).op := by
    ext t
    exact hf t
  dsimp [s2v_i1a_affineQuotientMap]
  rw [Category.assoc, ← Spec.map_comp, hf', Spec.map_comp,
    ← Category.assoc, Scheme.Opens.toSpecΓ_SpecMap_presheaf_map, Category.assoc]

/-- An invariant affine quotient map is surjective by integrality of invariants.
Source: SGA 1, Exposé V, §1; Mathlib, Algebra.IsInvariant.isIntegral. -/
theorem s2v_i1alo_affine_quotient_surjective
    (X : Over (Spec ↧ℂ)) (G : Type) [Group G] [Finite G]
    (a : G → (X ⟶ X)) (ha1 : a 1 = 𝟙 X)
    (hamul : ∀ g h, a (g * h) = a h ≫ a g)
    (U : X.left.Opens) (hU : IsAffineOpen U)
    (hiU : ∀ g, U ≤ (a g).left ⁻¹ᵁ U) :
    Surjective (s2v_i1a_affineQuotientMap X G a U hiU) := by
  obtain ⟨ρ, hρ, hI⟩ := s2v_i1alo_section_action X G a ha1 hamul U hiU
  letI := ρ
  let A := s2v_i1a_chartInvariants X G a U hiU
  letI := A.subtype.toAlgebra
  letI : Algebra.IsInvariant A Γ(X.left, U) G := hI
  have hi : A.subtype.IsIntegral := (Algebra.IsInvariant.isIntegral A Γ(X.left, U) G).1
  have hs := hi.comap_surjective Subtype.val_injective
  exact ⟨hs.comp hU.isoSpec.hom.homeomorph.surjective⟩

/-- The inverse image of an invariant principal spectrum open is the section basic open.
Source: Hartshorne, Algebraic Geometry, II.2, affine principal opens. -/
theorem s2v_i1alo_quotient_preimage_basicOpen
    (X : Over (Spec ↧ℂ)) (G : Type) (a : G → (X ⟶ X))
    (U : X.left.Opens) (hiU : ∀ g, U ≤ (a g).left ⁻¹ᵁ U)
    (r : s2v_i1a_chartInvariants X G a U hiU) :
    s2v_i1a_affineQuotientMap X G a U hiU ⁻¹ᵁ PrimeSpectrum.basicOpen r =
      U.ι ⁻¹ᵁ X.left.basicOpen r.val := by
  dsimp [s2v_i1a_affineQuotientMap]
  erw [Scheme.Hom.comp_preimage, SpecMap_preimage_basicOpen]
  exact Scheme.Opens.toSpecΓ_preimage_basicOpen U r.val

/-- A common source chart identifies a restricted morphism as an isomorphism.
Source: Hartshorne, Algebraic Geometry, II.2, gluing morphisms. -/
theorem s2v_i1alo_restriction_iso_of_charts
    (S Q C : Scheme) (j : S ⟶ Q) (U : Q.Opens) (V : S.Opens)
    (hV : j ⁻¹ᵁ U = V) (eU : C ≅ U.toScheme) (eV : C ≅ V.toScheme)
    (he : eV.hom ≫ V.ι ≫ j = eU.hom ≫ U.ι) : IsIso (j ∣_ U) := by
  subst V
  have hj : eV.hom ≫ (j ∣_ U) = eU.hom := by
    apply (cancel_mono U.ι).mp
    simpa only [Category.assoc, morphismRestrict_ι] using he
  haveI : IsIso (eV.hom ≫ (j ∣_ U)) := by rw [hj]; infer_instance
  exact IsIso.of_isIso_comp_left eV.hom (j ∣_ U)

/-- The actual affine quotient map detects equality of maps to an affine target.
Source: Hartshorne, Algebraic Geometry, II.2, affine spectra. -/
theorem s2v_i1alo_affine_quotient_cancel
    (X : Over (Spec ↧ℂ)) (G : Type) (a : G → (X ⟶ X))
    (U : X.left.Opens) (hU : IsAffineOpen U)
    (hiU : ∀ g, U ≤ (a g).left ⁻¹ᵁ U)
    (T : Scheme) [IsAffine T]
    (f g : Spec ↧(s2v_i1a_chartInvariants X G a U hiU) ⟶ T)
    (h : s2v_i1a_affineQuotientMap X G a U hiU ≫ f =
      s2v_i1a_affineQuotientMap X G a U hiU ≫ g) : f = g := by
  apply eq_of_SpecMap_comp_eq_of_isAffineOpen
    (CommRingCat.ofHom (s2v_i1a_chartInvariants X G a U hiU).subtype)
    Subtype.val_injective ⊤ (isAffineOpen_top _) (by simp) (by simp)
  apply (cancel_epi hU.isoSpec.hom).mp
  exact h

/-- A transition is an isomorphism over a principal open whose source lies in the subchart.
Source: SGA 1, Exposé V, §1, principal localization of invariant charts. -/
theorem s2v_i1alo_transition_principal_iso
    (X : Over (Spec ↧ℂ)) (G : Type) [Group G] [Finite G]
    (a : G → (X ⟶ X)) (ha1 : a 1 = 𝟙 X)
    (hamul : ∀ g h, a (g * h) = a h ≫ a g)
    (U V : X.left.Opens) (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (hiU : ∀ g, U ≤ (a g).left ⁻¹ᵁ U)
    (hiV : ∀ g, V ≤ (a g).left ⁻¹ᵁ V) (hVU : V ≤ U)
    (f : s2v_i1a_chartInvariants X G a U hiU →+*
      s2v_i1a_chartInvariants X G a V hiV)
    (hf : ∀ t, (f t).val = (X.left.presheaf.map (homOfLE hVU).op).hom t.val)
    (r : s2v_i1a_chartInvariants X G a U hiU)
    (hTV : X.left.basicOpen r.val ≤ V) :
    IsIso (Spec.map (CommRingCat.ofHom f) ∣_ PrimeSpectrum.basicOpen r) := by
  let T := X.left.basicOpen r.val
  have hTU : T ≤ U := X.left.basicOpen_le r.val
  have hTeqU : U.ι ⁻¹ᵁ T = s2v_i1a_affineQuotientMap X G a U hiU ⁻¹ᵁ
      PrimeSpectrum.basicOpen r := (s2v_i1alo_quotient_preimage_basicOpen X G a U hiU r).symm
  obtain ⟨hT, hiT, tU, htU, hlocU⟩ :=
    s2v_i1alo_principal_ring X G a ha1 hamul U hU hiU r T hTU hTeqU
  obtain ⟨eU, heU⟩ := s2v_i1alo_principal_square X G a U T hTU hiU hiT r tU htU hlocU
  have hbasic : X.left.basicOpen (f r).val = T := by
    rw [hf]
    change X.left.basicOpen ((X.left.presheaf.map (homOfLE hVU).op) r.val) = T
    rw [Scheme.basicOpen_res, inf_eq_right.mpr hTV]
  have hTeqV : V.ι ⁻¹ᵁ T = s2v_i1a_affineQuotientMap X G a V hiV ⁻¹ᵁ
      PrimeSpectrum.basicOpen (f r) := by
    rw [s2v_i1alo_quotient_preimage_basicOpen, hbasic]
  obtain ⟨_, hiT', tV, htV, hlocV⟩ :=
    s2v_i1alo_principal_ring X G a ha1 hamul V hV hiV (f r) T hTV hTeqV
  obtain ⟨eV, heV⟩ := s2v_i1alo_principal_square X G a V T hTV hiV hiT' (f r) tV htV hlocV
  have he : eV.hom ≫
      (show (Spec ↧(s2v_i1a_chartInvariants X G a V hiV)).Opens from
        PrimeSpectrum.basicOpen (f r)).ι ≫ Spec.map (CommRingCat.ofHom f) =
      eU.hom ≫ (show (Spec ↧(s2v_i1a_chartInvariants X G a U hiU)).Opens from
        PrimeSpectrum.basicOpen r).ι := by
    apply s2v_i1alo_affine_quotient_cancel X G a T hT hiT _
    rw [← Category.assoc eV.hom _ _, ← Category.assoc, heV, Category.assoc,
      s2v_i1alo_restriction_square X G a U V hVU hiU hiV f hf,
      ← Category.assoc, Scheme.homOfLE_homOfLE, ← heU]
  exact s2v_i1alo_restriction_iso_of_charts _ _ _ (Spec.map (CommRingCat.ofHom f))
    (PrimeSpectrum.basicOpen r) (PrimeSpectrum.basicOpen (f r))
    (SpecMap_preimage_basicOpen (CommRingCat.ofHom f) r) eU eV he

/-- Restricting a map into an open uses the same principal isomorphism as its composite.
Source: Hartshorne, Algebraic Geometry, II.2, restriction of scheme morphisms. -/
theorem s2v_i1alo_lift_restriction_iso
    (Q S : Scheme) (W U : Q.Opens) (hU : U ≤ W) (f : S ⟶ W.toScheme)
    (h : IsIso ((f ≫ W.ι) ∣_ U)) : IsIso (f ∣_ (W.ι ⁻¹ᵁ U)) := by
  have hi : W.ι ∣_ U = (Scheme.Opens.isoOfLE hU).hom := by
    apply (cancel_mono U.ι).mp
    rw [morphismRestrict_ι, Scheme.Opens.isoOfLE_hom_ι]
  haveI : IsIso (W.ι ∣_ U) := by rw [hi]; infer_instance
  haveI : IsIso ((f ∣_ (W.ι ⁻¹ᵁ U)) ≫ (W.ι ∣_ U)) := by
    rw [← morphismRestrict_comp]
    exact h
  exact IsIso.of_isIso_comp_right (f ∣_ (W.ι ⁻¹ᵁ U)) (W.ι ∣_ U)

/-- The saturated image identifies the invariant affine subchart as an open target restriction.
Source: SGA 1, Exposé V, §1, gluing invariant principal charts. -/
theorem s2v_i1alo_open_iso_of_saturated
    (X : Over (Spec ↧ℂ)) (G : Type) [Group G] [Finite G]
    (a : G → (X ⟶ X)) (ha1 : a 1 = 𝟙 X)
    (hamul : ∀ g h, a (g * h) = a h ≫ a g)
    (U V : X.left.Opens) (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (hiU : ∀ g, U ≤ (a g).left ⁻¹ᵁ U)
    (hiV : ∀ g, V ≤ (a g).left ⁻¹ᵁ V) (hVU : V ≤ U)
    (W : (Spec ↧(s2v_i1a_chartInvariants X G a U hiU)).Opens)
    (hpre : s2v_i1a_affineQuotientMap X G a U hiU ⁻¹ᵁ W = U.ι ⁻¹ᵁ V) :
    ∃ e : Spec ↧(s2v_i1a_chartInvariants X G a V hiV) ≅ W.toScheme,
      s2v_i1a_affineQuotientMap X G a V hiV ≫ e.hom ≫ W.ι =
        X.left.homOfLE hVU ≫ s2v_i1a_affineQuotientMap X G a U hiU := by
  obtain ⟨f, hf⟩ := s2v_i1alo_invariant_restriction X G a U V hVU hiU hiV
  let j := Spec.map (CommRingCat.ofHom f)
  have hjSquare := s2v_i1alo_restriction_square X G a U V hVU hiU hiV f hf
  letI := s2v_i1alo_affine_quotient_surjective X G a ha1 hamul V hV hiV
  have hj : Set.range j ⊆ Set.range W.ι := by
    rintro _ ⟨z, rfl⟩
    refine ⟨⟨j z, ?_⟩, rfl⟩
    obtain ⟨v, rfl⟩ := (s2v_i1a_affineQuotientMap X G a V hiV).surjective z
    have he := congrArg (fun k : V.toScheme ⟶ Spec ↧(s2v_i1a_chartInvariants X G a U hiU) => k v) hjSquare
    change j (s2v_i1a_affineQuotientMap X G a V hiV v) =
      s2v_i1a_affineQuotientMap X G a U hiU (X.left.homOfLE hVU v) at he
    rw [he]
    change X.left.homOfLE hVU v ∈ s2v_i1a_affineQuotientMap X G a U hiU ⁻¹ᵁ W
    rw [hpre]
    change U.ι (X.left.homOfLE hVU v) ∈ V
    have hh := congrArg (fun k : V.toScheme ⟶ X.left => k v) (Scheme.homOfLE_ι X.left hVU)
    change U.ι (X.left.homOfLE hVU v) = V.ι v at hh
    rw [hh]
    exact v.2
  let jbar := IsOpenImmersion.lift W.ι j hj
  have hfac : jbar ≫ W.ι = j := IsOpenImmersion.lift_fac _ _ _
  haveI : IsIso jbar := by
    apply s2v_i1alo_glued_iso _ W _ jbar
    intro r hr
    have hp : U.ι ⁻¹ᵁ X.left.basicOpen r.val ≤ U.ι ⁻¹ᵁ V := by
      rw [← hpre, ← s2v_i1alo_quotient_preimage_basicOpen X G a U hiU r]
      exact fun x hx => hr hx
    have hTV : X.left.basicOpen r.val ≤ V := by
      have hh := U.ι.image_mono hp
      simpa only [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι,
        inf_eq_right.mpr (X.left.basicOpen_le r.val), inf_eq_right.mpr hVU] using hh
    apply s2v_i1alo_lift_restriction_iso _ _ W (PrimeSpectrum.basicOpen r) hr jbar
    rw [hfac]
    exact s2v_i1alo_transition_principal_iso X G a ha1 hamul U V hU hV hiU hiV hVU f hf r hTV
  refine ⟨asIso jbar, ?_⟩
  change s2v_i1a_affineQuotientMap X G a V hiV ≫ jbar ≫ W.ι = _
  rw [hfac]
  exact hjSquare

/-- The canonical section principal open has its retained invariant spectrum chart.
Source: SGA 1, Exposé V, §1, principal localization of invariant rings. -/
theorem s2v_i1alo_canonical_principal_chart
    (X : Over (Spec ↧ℂ)) (G : Type) [Group G] [Finite G]
    (a : G → (X ⟶ X)) (ha1 : a 1 = 𝟙 X)
    (hamul : ∀ g h, a (g * h) = a h ≫ a g)
    (U : X.left.Opens) (hU : IsAffineOpen U)
    (hiU : ∀ g, U ≤ (a g).left ⁻¹ᵁ U)
    (r : s2v_i1a_chartInvariants X G a U hiU) :
    ∃ (hiT : ∀ g, X.left.basicOpen r.val ≤ (a g).left ⁻¹ᵁ X.left.basicOpen r.val)
      (e : Spec ↧(s2v_i1a_chartInvariants X G a (X.left.basicOpen r.val) hiT) ≅
        (show (Spec ↧(s2v_i1a_chartInvariants X G a U hiU)).Opens from PrimeSpectrum.basicOpen r).toScheme),
      s2v_i1a_affineQuotientMap X G a (X.left.basicOpen r.val) hiT ≫ e.hom ≫
        (show (Spec ↧(s2v_i1a_chartInvariants X G a U hiU)).Opens from PrimeSpectrum.basicOpen r).ι =
      X.left.homOfLE (X.left.basicOpen_le r.val) ≫ s2v_i1a_affineQuotientMap X G a U hiU := by
  have ht := (s2v_i1alo_quotient_preimage_basicOpen X G a U hiU r).symm
  obtain ⟨_, hiT, f, hf, hloc⟩ := s2v_i1alo_principal_ring X G a ha1 hamul U hU hiU r
    (X.left.basicOpen r.val) (X.left.basicOpen_le r.val) ht
  obtain ⟨e, he⟩ := s2v_i1alo_principal_square X G a U (X.left.basicOpen r.val)
    (X.left.basicOpen_le r.val) hiU hiT r f hf hloc
  exact ⟨hiT, e, he⟩

/-- A principal quotient chart maps into the source restriction over any containing open.
Source: SGA 1, Exposé V, §1, compatibility of quotient restrictions. -/
theorem s2v_i1alo_principal_source_square
    (X : Over (Spec ↧ℂ)) (G : Type) (a : G → (X ⟶ X))
    (U : X.left.Opens) (hiU : ∀ g, U ≤ (a g).left ⁻¹ᵁ U)
    (r : s2v_i1a_chartInvariants X G a U hiU)
    (hiT : ∀ g, X.left.basicOpen r.val ≤ (a g).left ⁻¹ᵁ X.left.basicOpen r.val)
    (e : Spec ↧(s2v_i1a_chartInvariants X G a (X.left.basicOpen r.val) hiT) ≅
      (show (Spec ↧(s2v_i1a_chartInvariants X G a U hiU)).Opens from PrimeSpectrum.basicOpen r).toScheme)
    (he : s2v_i1a_affineQuotientMap X G a (X.left.basicOpen r.val) hiT ≫ e.hom ≫
      (show (Spec ↧(s2v_i1a_chartInvariants X G a U hiU)).Opens from PrimeSpectrum.basicOpen r).ι =
        X.left.homOfLE (X.left.basicOpen_le r.val) ≫ s2v_i1a_affineQuotientMap X G a U hiU)
    (W : (Spec ↧(s2v_i1a_chartInvariants X G a U hiU)).Opens)
    (hr : PrimeSpectrum.basicOpen r ≤ W) :
    ∃ l : (X.left.basicOpen r.val).toScheme ⟶
        (s2v_i1a_affineQuotientMap X G a U hiU ⁻¹ᵁ W).toScheme,
      l ≫ (s2v_i1a_affineQuotientMap X G a U hiU ⁻¹ᵁ W).ι =
        X.left.homOfLE (X.left.basicOpen_le r.val) ∧
      l ≫ (s2v_i1a_affineQuotientMap X G a U hiU ∣_ W) =
        s2v_i1a_affineQuotientMap X G a (X.left.basicOpen r.val) hiT ≫ e.hom ≫
          (Spec ↧(s2v_i1a_chartInvariants X G a U hiU)).homOfLE hr := by
  let q := s2v_i1a_affineQuotientMap X G a U hiU
  let t := X.left.homOfLE (X.left.basicOpen_le r.val)
  have ht : Set.range t ⊆ Set.range (q ⁻¹ᵁ W).ι := by
    rintro _ ⟨z, rfl⟩
    refine ⟨⟨t z, ?_⟩, rfl⟩
    have hz := congrArg (fun k : (X.left.basicOpen r.val).toScheme ⟶
      Spec ↧(s2v_i1a_chartInvariants X G a U hiU) => k z) he
    change (e.hom (s2v_i1a_affineQuotientMap X G a (X.left.basicOpen r.val) hiT z)).val =
      q (t z) at hz
    change q (t z) ∈ W
    rw [← hz]
    exact hr (e.hom (s2v_i1a_affineQuotientMap X G a (X.left.basicOpen r.val) hiT z)).2
  let l := IsOpenImmersion.lift (q ⁻¹ᵁ W).ι t ht
  have hl : l ≫ (q ⁻¹ᵁ W).ι = t := IsOpenImmersion.lift_fac _ _ _
  refine ⟨l, hl, ?_⟩
  apply (cancel_mono W.ι).mp
  simp only [Category.assoc, morphismRestrict_ι, Scheme.homOfLE_ι]
  rw [← Category.assoc, hl]
  have hinc := Scheme.homOfLE_ι (Spec ↧(s2v_i1a_chartInvariants X G a U hiU)) hr
  exact he.symm.trans (congrArg (fun k =>
    s2v_i1a_affineQuotientMap X G a (X.left.basicOpen r.val) hiT ≫ e.hom ≫ k) hinc.symm)

end HodgeLean.Foundations.Program
