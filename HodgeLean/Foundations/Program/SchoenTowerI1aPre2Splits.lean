import HodgeLean.Foundations.Program.SchoenTowerI1aLocalization
import HodgeLean.Foundations.Program.SchoenTowerI1aProjectiveCharts
import HodgeLean.Foundations.Program.SchoenTowerI1aFiniteNeighborhoods

/-! # Local construction steps for invariant spectra
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- The retained principal inverse image is the basic open of the retained section.
Source: Hartshorne, Algebraic Geometry, II.2, affine principal opens. -/
theorem s2v_i1alo_principal_source_eq
    (X : Over (Spec ↧ℂ)) (G : Type) (a : G → (X ⟶ X))
    (U : X.left.Opens) (hiU : ∀ g, U ≤ (a g).left ⁻¹ᵁ U)
    (r : s2v_i1a_chartInvariants X G a U hiU)
    (V : X.left.Opens) (hVU : V ≤ U)
    (hVeq : U.ι ⁻¹ᵁ V = s2v_i1a_affineQuotientMap X G a U hiU ⁻¹ᵁ
      PrimeSpectrum.basicOpen r) : V = X.left.basicOpen r.val := by
  have hp : U.ι ⁻¹ᵁ V = U.ι ⁻¹ᵁ X.left.basicOpen r.val := by
    rw [hVeq]
    change (U.toSpecΓ ≫ Spec.map
      (CommRingCat.ofHom (s2v_i1a_chartInvariants X G a U hiU).subtype)) ⁻¹ᵁ
        PrimeSpectrum.basicOpen r = _
    erw [Scheme.Hom.comp_preimage, SpecMap_preimage_basicOpen]
    exact Scheme.Opens.toSpecΓ_preimage_basicOpen U r.val
  have hh := congrArg (fun T => U.ι ''ᵁ T) hp
  simpa only [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι,
    inf_eq_right.mpr hVU, inf_eq_right.mpr (X.left.basicOpen_le r.val)] using hh


/-- The specified principal inverse image is affine and preserved by every action map.
Source: Hartshorne, Algebraic Geometry, II.2, principal affine opens. -/
theorem s2v_i1alo_principal_source
    (X : Over (Spec ↧ℂ)) (G : Type) (a : G → (X ⟶ X))
    (U : X.left.Opens) (hU : IsAffineOpen U)
    (hiU : ∀ g, U ≤ (a g).left ⁻¹ᵁ U)
    (r : s2v_i1a_chartInvariants X G a U hiU)
    (V : X.left.Opens) (hVU : V ≤ U)
    (hVeq : U.ι ⁻¹ᵁ V = s2v_i1a_affineQuotientMap X G a U hiU ⁻¹ᵁ
      PrimeSpectrum.basicOpen r) :
    IsAffineOpen V ∧ ∀ g, V ≤ (a g).left ⁻¹ᵁ V := by
  have he := s2v_i1alo_principal_source_eq X G a U hiU r V hVU hVeq
  rw [he]
  refine ⟨hU.basicOpen r.val, fun g => ?_⟩
  have hb := Scheme.basicOpen_appLE (a g).left U U (hiU g) r.val
  change X.left.basicOpen (((a g).left.appLE U U (hiU g)).hom r.val) = _ at hb
  rw [r.property g] at hb
  exact (le_of_eq hb).trans inf_le_right

/-- Restriction to an invariant principal open localizes the invariant ring.
Source: SGA 1, Exposé V, §1, localization of invariant rings. -/
theorem s2v_i1alo_principal_ring
    (X : Over (Spec ↧ℂ)) (G : Type) [Group G] [Finite G]
    (a : G → (X ⟶ X)) (ha1 : a 1 = 𝟙 X)
    (hamul : ∀ g h, a (g * h) = a h ≫ a g)
    (U : X.left.Opens) (hU : IsAffineOpen U)
    (hiU : ∀ g, U ≤ (a g).left ⁻¹ᵁ U)
    (r : s2v_i1a_chartInvariants X G a U hiU)
    (V : X.left.Opens) (hVU : V ≤ U)
    (hVeq : U.ι ⁻¹ᵁ V = s2v_i1a_affineQuotientMap X G a U hiU ⁻¹ᵁ
      PrimeSpectrum.basicOpen r) :
    ∃ (hV : IsAffineOpen V) (hiV : ∀ g, V ≤ (a g).left ⁻¹ᵁ V)
      (f : s2v_i1a_chartInvariants X G a U hiU →+*
        s2v_i1a_chartInvariants X G a V hiV),
      (∀ t, (f t).val = (X.left.presheaf.map (homOfLE hVU).op).hom t.val) ∧
      (letI := f.toAlgebra
       IsLocalization (Submonoid.powers r) (s2v_i1a_chartInvariants X G a V hiV)) := by
  obtain ⟨hV, hiV⟩ := s2v_i1alo_principal_source X G a U hU hiU r V hVU hVeq
  obtain ⟨f, hf⟩ := s2v_i1alo_invariant_restriction X G a U V hVU hiU hiV
  obtain ⟨ρU, hρU, _⟩ := s2v_i1alo_section_action X G a ha1 hamul U hiU
  obtain ⟨ρV, hρV, _⟩ := s2v_i1alo_section_action X G a ha1 hamul V hiV
  letI := ρU
  letI := ρV
  let t := (X.left.presheaf.map (homOfLE hVU).op).hom
  letI := t.toAlgebra
  have he := s2v_i1alo_principal_source_eq X G a U hiU r V hVU hVeq
  letI : IsLocalization.Away r.val Γ(X.left, V) :=
    hU.isLocalization_of_eq_basicOpen r.val (homOfLE hVU) he
  refine ⟨hV, hiV, f, hf, ?_⟩
  exact s2v_i1alo_fixed_localization Γ(X.left, U) Γ(X.left, V) G
    (s2v_i1alo_section_restriction_equivariant X G a U V hVU hiU hiV ρU ρV hρU hρV)
    (s2v_i1a_chartInvariants X G a U hiU) (s2v_i1a_chartInvariants X G a V hiV)
    (s2v_i1alo_section_fixed_iff X G a U hiU ρU hρU)
    (s2v_i1alo_section_fixed_iff X G a V hiV ρV hρV) f hf r

/-- The localized invariant ring determines the principal-open scheme square.
Source: SGA 1, Exposé V, §1; Hartshorne, Algebraic Geometry, II.2. -/
theorem s2v_i1alo_principal_square
    (X : Over (Spec ↧ℂ)) (G : Type) [Group G]
    (a : G → (X ⟶ X))
    (U V : X.left.Opens) (hVU : V ≤ U)
    (hiU : ∀ g, U ≤ (a g).left ⁻¹ᵁ U)
    (hiV : ∀ g, V ≤ (a g).left ⁻¹ᵁ V)
    (r : s2v_i1a_chartInvariants X G a U hiU)
    (f : s2v_i1a_chartInvariants X G a U hiU →+*
      s2v_i1a_chartInvariants X G a V hiV)
    (hf : ∀ t, (f t).val = (X.left.presheaf.map (homOfLE hVU).op).hom t.val)
    (hloc : letI := f.toAlgebra
      IsLocalization (Submonoid.powers r) (s2v_i1a_chartInvariants X G a V hiV)) :
    ∃ e : Spec ↧(s2v_i1a_chartInvariants X G a V hiV) ≅
      (show (Spec ↧(s2v_i1a_chartInvariants X G a U hiU)).Opens from
        PrimeSpectrum.basicOpen r).toScheme,
      s2v_i1a_affineQuotientMap X G a V hiV ≫ e.hom ≫
        (show (Spec ↧(s2v_i1a_chartInvariants X G a U hiU)).Opens from
          PrimeSpectrum.basicOpen r).ι =
        X.left.homOfLE hVU ≫ s2v_i1a_affineQuotientMap X G a U hiU := by
  let A := s2v_i1a_chartInvariants X G a U hiU
  let B := s2v_i1a_chartInvariants X G a V hiV
  letI := f.toAlgebra
  letI : IsLocalization (Submonoid.powers r) B := hloc
  let j : Spec ↧B ⟶ Spec ↧A := Spec.map (CommRingCat.ofHom f)
  haveI : IsOpenImmersion j := IsOpenImmersion.of_isLocalization r
  let D : (Spec ↧A).Opens := PrimeSpectrum.basicOpen r
  have hj : Set.range j = Set.range D.ι := by
    rw [Scheme.Opens.range_ι]
    exact PrimeSpectrum.localization_away_comap_range B r
  let e := IsOpenImmersion.isoOfRangeEq j D.ι hj
  refine ⟨e, ?_⟩
  rw [show e.hom ≫ D.ι = j from IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _]
  have hf' : CommRingCat.ofHom f ≫ CommRingCat.ofHom B.subtype =
      CommRingCat.ofHom A.subtype ≫ X.left.presheaf.map (homOfLE hVU).op := by
    ext t
    exact hf t
  dsimp [s2v_i1a_affineQuotientMap, j]
  rw [Category.assoc, ← Spec.map_comp, hf', Spec.map_comp]
  rw [← Category.assoc, Scheme.Opens.toSpecΓ_SpecMap_presheaf_map, Category.assoc]

/-- An ambient affine complement avoids a finite set in a projective presentation.
Source: SGA 1, Exposé V, Proposition 1.8. -/
theorem s2v_i1alo_projective_separator
    (X : Over (Spec ↧ℂ)) [IsProjective X.hom]
    (N : X.left.Opens) (s : Finset X.left) (hs : ∀ x ∈ s, x ∈ N) :
    ∃ (P : ProjectiveSpace.Presentation X.hom)
      (H : (ProjectiveSpace (Fin (P.ambientDimension + 1)) (Spec ↧ℂ)).Opens),
      IsAffineOpen H ∧ P.immersion ⁻¹ᵁ H ≤ N ∧
        ∀ x ∈ s, P.immersion x ∈ H := by
  classical
  let P : ProjectiveSpace.Presentation X.hom :=
    IsProjective.nonempty_presentation.some
  letI := P.isClosedImmersion
  obtain ⟨M, hM⟩ := s2v_i1alo_ambient_open X.left _ P.immersion N
  obtain ⟨A, hA, hsA⟩ := s2v_i1alo_projectiveSpace_finite_affine
    P.ambientDimension (s.image P.immersion)
  obtain ⟨H, hH, hHM, _, hsH⟩ := s2v_i1alo_shrink_affine_finite _ A hA M
    (s.image P.immersion) hsA (by
      intro y hy
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
      change x ∈ P.immersion ⁻¹ᵁ M
      rw [hM]
      exact hs x hx)
  refine ⟨P, H, hH, ?_, ?_⟩
  · rw [← hM]
    exact P.immersion.preimage_mono hHM
  · intro x hx
    exact hsH _ (Finset.mem_image.mpr ⟨x, hx, rfl⟩)

/-- Pulling an ambient affine complement through a projective presentation is affine.
Source: Hartshorne, Algebraic Geometry, II.2, affine morphisms. -/
theorem s2v_i1alo_affine_complement
    (X : Over (Spec ↧ℂ)) (P : ProjectiveSpace.Presentation X.hom)
    (H : (ProjectiveSpace (Fin (P.ambientDimension + 1)) (Spec ↧ℂ)).Opens)
    (hH : IsAffineOpen H) : IsAffineOpen (P.immersion ⁻¹ᵁ H) := by
  letI := P.isClosedImmersion
  exact hH.preimage P.immersion

/-- A quotient image open is covered by principal opens contained in that image.
Source: Hartshorne, Algebraic Geometry, II.2, principal-open basis. -/
theorem s2v_i1alo_principal_cover (R : CommRingCat) (W : (Spec R).Opens)
    (y : Spec R) (hy : y ∈ W) :
    ∃ r : R, y ∈ PrimeSpectrum.basicOpen r ∧ PrimeSpectrum.basicOpen r ≤ W := by
  obtain ⟨_, ⟨r, rfl⟩, hyr, hrW⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hy W.isOpen
  exact ⟨r, hyr, hrW⟩

/-- Isomorphisms on the principal cover give an isomorphism onto the image open.
Source: Hartshorne, Algebraic Geometry, II.2, gluing morphisms. -/
theorem s2v_i1alo_glued_iso
    (R : CommRingCat) (W : (Spec R).Opens) (S : Scheme) (f : S ⟶ W.toScheme)
    (h : ∀ r : R, PrimeSpectrum.basicOpen r ≤ W →
      IsIso (f ∣_ (W.ι ⁻¹ᵁ PrimeSpectrum.basicOpen r))) : IsIso f := by
  apply IsZariskiLocalAtTarget.of_forall_exists_morphismRestrict
    (P := MorphismProperty.isomorphisms _) (f := f)
  intro x
  obtain ⟨r, hxr, hr⟩ := s2v_i1alo_principal_cover R W (W.ι x) x.2
  exact ⟨W.ι ⁻¹ᵁ PrimeSpectrum.basicOpen r, hxr, h r hr⟩

end HodgeLean.Foundations.Program
