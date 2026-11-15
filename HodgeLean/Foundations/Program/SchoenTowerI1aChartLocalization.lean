import HodgeLean.Foundations.Program.SchoenTowerI1aTransitionHelpers
import HodgeLean.Foundations.Program.SchoenTowerI1aInvariantLocalization

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

lemma s2v_i1ahi_basicOpen_invariant
    (X : Over (Spec ↧ℂ)) (G : Type) (a : G → (X ⟶ X))
    (U : X.left.Opens) (hiU : ∀ g, U ≤ (a g).left ⁻¹ᵁ U)
    (r : s2v_i1a_chartInvariants X G a U hiU) :
    ∀ g, X.left.basicOpen r.val ≤ (a g).left ⁻¹ᵁ X.left.basicOpen r.val := by
  intro g
  have he := Scheme.basicOpen_appLE (a g).left U U (hiU g) r.val
  rw [r.property g] at he
  exact (le_of_eq he).trans inf_le_right

lemma s2v_i1ahi_chart_fixed_iff
    (X : Over (Spec ↧ℂ)) (G : Type) [Group G]
    (a : G → (X ⟶ X)) (ha1 : a 1 = 𝟙 X)
    (hamul : ∀ g h, a (g * h) = a h ≫ a g)
    (U : X.left.Opens) (hiU : ∀ g, U ≤ (a g).left ⁻¹ᵁ U)
    (r : Γ(X.left, U)) :
    letI := s2v_i1ahi_chartAction X G a ha1 hamul U hiU
    r ∈ s2v_i1a_chartInvariants X G a U hiU ↔ ∀ g : G, g • r = r := by
  letI := s2v_i1ahi_chartAction X G a ha1 hamul U hiU
  constructor
  · intro hr g
    exact hr g⁻¹
  · intro hr g
    simpa only [show g⁻¹ • r = ((a (g⁻¹)⁻¹).left.appLE U U _).hom r from rfl,
      inv_inv] using hr g⁻¹

lemma s2v_i1ahi_chart_restriction_equivariant
    (X : Over (Spec ↧ℂ)) (G : Type) (a : G → (X ⟶ X))
    (U V : X.left.Opens) (hUV : U ≤ V)
    (hiU : ∀ g, U ≤ (a g).left ⁻¹ᵁ U)
    (hiV : ∀ g, V ≤ (a g).left ⁻¹ᵁ V)
    (g : G) (r : Γ(X.left, V)) :
    (X.left.presheaf.map (homOfLE hUV).op).hom
      (((a g).left.appLE V V (hiV g)).hom r) =
    ((a g).left.appLE U U (hiU g)).hom
      ((X.left.presheaf.map (homOfLE hUV).op).hom r) := by
  have he : (a g).left.appLE V V (hiV g) ≫ X.left.presheaf.map (homOfLE hUV).op =
      X.left.presheaf.map (homOfLE hUV).op ≫ (a g).left.appLE U U (hiU g) := by
    rw [Scheme.Hom.appLE_map, Scheme.Hom.map_appLE]
  exact congrArg (fun k : Γ(X.left, V) ⟶ Γ(X.left, U) => k.hom r) he

lemma s2v_i1ahi_chart_invariants_localization
    (X : Over (Spec ↧ℂ)) (G : Type) [Group G] [Finite G]
    (a : G → (X ⟶ X)) (ha1 : a 1 = 𝟙 X)
    (hamul : ∀ g h, a (g * h) = a h ≫ a g)
    (U V : X.left.Opens) (hU : IsAffineOpen U) (hVU : V ≤ U)
    (hiU : ∀ g, U ≤ (a g).left ⁻¹ᵁ U)
    (hiV : ∀ g, V ≤ (a g).left ⁻¹ᵁ V)
    (r : s2v_i1a_chartInvariants X G a U hiU)
    (hVeq : V = X.left.basicOpen r.val) :
    letI := (s2v_i1ahi_invariantRestriction X G a V U hVU hiV hiU).hom.toAlgebra
    IsLocalization.Away r (s2v_i1a_chartInvariants X G a V hiV) := by
  letI := s2v_i1ahi_chartAction X G a ha1 hamul U hiU
  letI := s2v_i1ahi_chartAction X G a ha1 hamul V hiV
  letI := (X.left.presheaf.map (homOfLE hVU).op).hom.toAlgebra
  letI : IsLocalization.Away r.val Γ(X.left, V) :=
    hU.isLocalization_of_eq_basicOpen r.val (homOfLE hVU) hVeq
  apply s2v_i1ahi_fixed_subrings_localization
    (s2v_i1a_chartInvariants X G a U hiU)
    (s2v_i1a_chartInvariants X G a V hiV)
    (s2v_i1ahi_chart_fixed_iff X G a ha1 hamul U hiU)
    (s2v_i1ahi_chart_fixed_iff X G a ha1 hamul V hiV) r
    (fun g x => s2v_i1ahi_chart_restriction_equivariant X G a V U hVU hiV hiU g⁻¹ x)
    (s2v_i1ahi_invariantRestriction X G a V U hVU hiV hiU).hom
    (fun _ => rfl)

lemma s2v_i1ahi_principal_transition_openImmersion
    (X : Over (Spec ↧ℂ)) (G : Type) [Group G] [Finite G]
    (a : G → (X ⟶ X)) (ha1 : a 1 = 𝟙 X)
    (hamul : ∀ g h, a (g * h) = a h ≫ a g)
    (U V : X.left.Opens) (hU : IsAffineOpen U) (hVU : V ≤ U)
    (hiU : ∀ g, U ≤ (a g).left ⁻¹ᵁ U)
    (hiV : ∀ g, V ≤ (a g).left ⁻¹ᵁ V)
    (r : s2v_i1a_chartInvariants X G a U hiU)
    (hVeq : V = X.left.basicOpen r.val) :
    IsOpenImmersion (Spec.map (s2v_i1ahi_invariantRestriction X G a V U hVU hiV hiU)) := by
  letI := (s2v_i1ahi_invariantRestriction X G a V U hVU hiV hiU).hom.toAlgebra
  letI := s2v_i1ahi_chart_invariants_localization X G a ha1 hamul U V hU hVU hiU hiV r hVeq
  exact IsOpenImmersion.of_isLocalization r

lemma s2v_i1ahi_principal_transition_range
    (X : Over (Spec ↧ℂ)) (G : Type) [Group G] [Finite G]
    (a : G → (X ⟶ X)) (ha1 : a 1 = 𝟙 X)
    (hamul : ∀ g h, a (g * h) = a h ≫ a g)
    (U V : X.left.Opens) (hU : IsAffineOpen U) (hVU : V ≤ U)
    (hiU : ∀ g, U ≤ (a g).left ⁻¹ᵁ U)
    (hiV : ∀ g, V ≤ (a g).left ⁻¹ᵁ V)
    (r : s2v_i1a_chartInvariants X G a U hiU)
    (hVeq : V = X.left.basicOpen r.val) :
    Set.range (Spec.map (s2v_i1ahi_invariantRestriction X G a V U hVU hiV hiU)) =
      (PrimeSpectrum.basicOpen r : Set (PrimeSpectrum (s2v_i1a_chartInvariants X G a U hiU))) := by
  letI := (s2v_i1ahi_invariantRestriction X G a V U hVU hiV hiU).hom.toAlgebra
  letI := s2v_i1ahi_chart_invariants_localization X G a ha1 hamul U V hU hVU hiU hiV r hVeq
  exact PrimeSpectrum.localization_away_comap_range _ r

lemma s2v_i1ahi_quotient_preimage_basicOpen
    (X : Over (Spec ↧ℂ)) (G : Type) (a : G → (X ⟶ X))
    (U : X.left.Opens) (hiU : ∀ g, U ≤ (a g).left ⁻¹ᵁ U)
    (r : s2v_i1a_chartInvariants X G a U hiU) :
    (s2v_i1a_affineQuotientMap X G a U hiU) ⁻¹ᵁ PrimeSpectrum.basicOpen r =
      U.ι ⁻¹ᵁ X.left.basicOpen r.val := by
  change (U.toSpecΓ ≫ Spec.map (CommRingCat.ofHom
    (s2v_i1a_chartInvariants X G a U hiU).subtype)) ⁻¹ᵁ _ = _
  rw [Scheme.Hom.comp_preimage, SpecMap_preimage_basicOpen]
  exact Scheme.Opens.toSpecΓ_preimage_basicOpen U r.val

lemma s2v_i1ahi_principal_chart_iso_square
    (X : Over (Spec ↧ℂ)) (G : Type) [Group G] [Finite G]
    (a : G → (X ⟶ X)) (ha1 : a 1 = 𝟙 X)
    (hamul : ∀ g h, a (g * h) = a h ≫ a g)
    (U V : X.left.Opens) (hU : IsAffineOpen U) (hVU : V ≤ U)
    (hiU : ∀ g, U ≤ (a g).left ⁻¹ᵁ U)
    (hiV : ∀ g, V ≤ (a g).left ⁻¹ᵁ V)
    (r : s2v_i1a_chartInvariants X G a U hiU)
    (hVeq : V = X.left.basicOpen r.val) :
    ∃ e : Spec ↧(s2v_i1a_chartInvariants X G a V hiV) ≅
        (show (Spec ↧(s2v_i1a_chartInvariants X G a U hiU)).Opens from
          PrimeSpectrum.basicOpen r).toScheme,
      s2v_i1a_affineQuotientMap X G a V hiV ≫ e.hom ≫
        (show (Spec ↧(s2v_i1a_chartInvariants X G a U hiU)).Opens from
          PrimeSpectrum.basicOpen r).ι =
        X.left.homOfLE hVU ≫ s2v_i1a_affineQuotientMap X G a U hiU := by
  let j := Spec.map (s2v_i1ahi_invariantRestriction X G a V U hVU hiV hiU)
  let W : (Spec ↧(s2v_i1a_chartInvariants X G a U hiU)).Opens := PrimeSpectrum.basicOpen r
  haveI : IsOpenImmersion j :=
    s2v_i1ahi_principal_transition_openImmersion X G a ha1 hamul U V hU hVU hiU hiV r hVeq
  have hrange : Set.range j = Set.range W.ι := by
    rw [Scheme.Opens.range_ι]
    exact s2v_i1ahi_principal_transition_range X G a ha1 hamul U V hU hVU hiU hiV r hVeq
  refine ⟨IsOpenImmersion.isoOfRangeEq j W.ι hrange, ?_⟩
  rw [IsOpenImmersion.isoOfRangeEq_hom_fac]
  exact s2v_i1ahi_transition_square X G a V U hVU hiV hiU

end HodgeLean.Foundations.Program
