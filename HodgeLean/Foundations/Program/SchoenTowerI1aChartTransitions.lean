import HodgeLean.Foundations.Program.SchoenTowerI1aChartTopology
import HodgeLean.Foundations.Program.SchoenTowerI1aChartLocalization
import HodgeLean.Foundations.Program.SchoenTowerI1aLocalAssembly

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry Topology
namespace HodgeLean.Foundations.Program

lemma s2v_i1ahi_transition_injective
    (X : Over (Spec ↧ℂ)) (G : Type) [Group G] [Finite G]
    (a : G → (X ⟶ X)) (ha1 : a 1 = 𝟙 X)
    (hamul : ∀ g h, a (g * h) = a h ≫ a g)
    (U V : X.left.Opens) (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (hUV : U ≤ V) (hiU : ∀ g, U ≤ (a g).left ⁻¹ᵁ U)
    (hiV : ∀ g, V ≤ (a g).left ⁻¹ᵁ V) :
    Function.Injective (Spec.map (s2v_i1ahi_invariantRestriction X G a U V hUV hiU hiV)) := by
  letI := s2v_i1ahi_chart_surjective X G a ha1 hamul U hU hiU
  intro p q hpq
  obtain ⟨x, rfl⟩ := (s2v_i1a_affineQuotientMap X G a U hiU).surjective p
  obtain ⟨y, rfl⟩ := (s2v_i1a_affineQuotientMap X G a U hiU).surjective q
  have hsq := s2v_i1ahi_transition_square X G a U V hUV hiU hiV
  have he : s2v_i1a_affineQuotientMap X G a V hiV (X.left.homOfLE hUV x) =
      s2v_i1a_affineQuotientMap X G a V hiV (X.left.homOfLE hUV y) := by
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, ← hsq]
    exact hpq
  obtain ⟨g, hg⟩ := s2v_i1ahi_chart_scheme_point_orbit X G a ha1 hamul V hV hiV
    (X.left.homOfLE hUV x) (X.left.homOfLE hUV y) he
  change (a g).left ((X.left.homOfLE hUV x).1) = (X.left.homOfLE hUV y).1 at hg
  have hxy : (a g).left.resLE U U (hiU g) x = y := by
    apply Subtype.ext
    simpa only [Scheme.Hom.coe_resLE_apply, Scheme.homOfLE_apply] using hg
  have hv := congrArg (fun f : U.toScheme ⟶
      Spec ↧(s2v_i1a_chartInvariants X G a U hiU) => f x)
    (s2v_i1ahi_chart_quotient_invariant X G a U hiU g)
  change s2v_i1a_affineQuotientMap X G a U hiU
    ((a g).left.resLE U U (hiU g) x) = _ at hv
  rw [hxy] at hv
  exact hv.symm

lemma s2v_i1ahi_invariant_principal_neighborhood
    (X : Over (Spec ↧ℂ)) (G : Type) [Group G] [Finite G]
    (a : G → (X ⟶ X)) (ha1 : a 1 = 𝟙 X)
    (hamul : ∀ g h, a (g * h) = a h ≫ a g)
    (U V : X.left.Opens) (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (hUV : U ≤ V) (hiU : ∀ g, U ≤ (a g).left ⁻¹ᵁ U)
    (hiV : ∀ g, V ≤ (a g).left ⁻¹ᵁ V)
    (z : Spec ↧(s2v_i1a_chartInvariants X G a U hiU)) :
    ∃ r : s2v_i1a_chartInvariants X G a V hiV,
      (Spec.map (s2v_i1ahi_invariantRestriction X G a U V hUV hiU hiV)) z ∈
        PrimeSpectrum.basicOpen r ∧ X.left.basicOpen r.val ≤ U := by
  letI := s2v_i1ahi_chart_surjective X G a ha1 hamul U hU hiU
  let W : (Spec ↧(s2v_i1a_chartInvariants X G a V hiV)).Opens :=
    ⟨s2v_i1a_affineQuotientMap X G a V hiV '' {x | V.ι x ∈ U},
      s2v_i1ahi_chart_open_image X G a ha1 hamul V hV hiV U hiU⟩
  have hzW : (Spec.map (s2v_i1ahi_invariantRestriction X G a U V hUV hiU hiV)) z ∈ W := by
    obtain ⟨x, hx⟩ := (s2v_i1a_affineQuotientMap X G a U hiU).surjective z
    refine ⟨X.left.homOfLE hUV x, ?_, ?_⟩
    · change (X.left.homOfLE hUV x).1 ∈ U
      rw [Scheme.homOfLE_apply]
      exact x.property
    · have hs := congrArg (fun f : U.toScheme ⟶
          Spec ↧(s2v_i1a_chartInvariants X G a V hiV) => f x)
        (s2v_i1ahi_transition_square X G a U V hUV hiU hiV)
      change (Spec.map (s2v_i1ahi_invariantRestriction X G a U V hUV hiU hiV))
        (s2v_i1a_affineQuotientMap X G a U hiU x) =
        s2v_i1a_affineQuotientMap X G a V hiV (X.left.homOfLE hUV x) at hs
      rw [hx] at hs
      exact hs.symm
  obtain ⟨_, ⟨_, ⟨r, rfl⟩, rfl⟩, hzr, hrW⟩ :=
    PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open hzW W.isOpen
  refine ⟨r, hzr, ?_⟩
  intro x hx
  let t : V.toScheme := ⟨x, (X.left.basicOpen_le r.val) hx⟩
  have ht : s2v_i1a_affineQuotientMap X G a V hiV t ∈ PrimeSpectrum.basicOpen r := by
    change t ∈ (s2v_i1a_affineQuotientMap X G a V hiV) ⁻¹ᵁ PrimeSpectrum.basicOpen r
    rw [s2v_i1ahi_quotient_preimage_basicOpen]
    exact hx
  exact (Set.ext_iff.mp (s2v_i1ahi_chart_saturated_preimage X G a ha1 hamul V hV hiV U hiU) t).mp
    (hrW ht)

lemma s2v_i1ahi_transition_local_charts
    (X : Over (Spec ↧ℂ)) (G : Type) [Group G] [Finite G]
    (a : G → (X ⟶ X)) (ha1 : a 1 = 𝟙 X)
    (hamul : ∀ g h, a (g * h) = a h ≫ a g)
    (U V : X.left.Opens) (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (hUV : U ≤ V) (hiU : ∀ g, U ≤ (a g).left ⁻¹ᵁ U)
    (hiV : ∀ g, V ≤ (a g).left ⁻¹ᵁ V) :
    ∀ z : Spec ↧(s2v_i1a_chartInvariants X G a U hiU),
      ∃ (T : Scheme) (u : T ⟶ Spec ↧(s2v_i1a_chartInvariants X G a U hiU)),
        IsOpenImmersion u ∧ IsOpenImmersion
          (u ≫ Spec.map (s2v_i1ahi_invariantRestriction X G a U V hUV hiU hiV)) ∧
          ∃ t : T, u t = z := by
  intro z
  obtain ⟨r, hzr, hSU⟩ :=
    s2v_i1ahi_invariant_principal_neighborhood X G a ha1 hamul U V hU hV hUV hiU hiV z
  let S := X.left.basicOpen r.val
  have hSV : S ≤ V := X.left.basicOpen_le r.val
  let hiS := s2v_i1ahi_basicOpen_invariant X G a V hiV r
  let rU := (s2v_i1ahi_invariantRestriction X G a U V hUV hiU hiV).hom r
  have hSeq : S = X.left.basicOpen rU.val := by
    change X.left.basicOpen r.val =
      X.left.basicOpen ((X.left.presheaf.map (homOfLE hUV).op).hom r.val)
    rw [Scheme.basicOpen_res]
    exact (inf_eq_right.mpr hSU).symm
  let u := Spec.map (s2v_i1ahi_invariantRestriction X G a S U hSU hiS hiU)
  let v := Spec.map (s2v_i1ahi_invariantRestriction X G a S V hSV hiS hiV)
  haveI : IsOpenImmersion u :=
    s2v_i1ahi_principal_transition_openImmersion X G a ha1 hamul U S hU hSU hiU hiS rU hSeq
  haveI : IsOpenImmersion v :=
    s2v_i1ahi_principal_transition_openImmersion X G a ha1 hamul V S hV hSV hiV hiS r rfl
  have hcomp : u ≫ Spec.map (s2v_i1ahi_invariantRestriction X G a U V hUV hiU hiV) = v := by
    dsimp only [u, v]
    rw [← Spec.map_comp, s2v_i1ahi_invariantRestriction_comp]
  have hz : z ∈ Set.range u := by
    rw [s2v_i1ahi_principal_transition_range X G a ha1 hamul U S hU hSU hiU hiS rU hSeq]
    exact hzr
  refine ⟨_, u, inferInstance, ?_, hz⟩
  rw [hcomp]
  infer_instance

lemma s2v_i1ahi_transition_openImmersion
    (X : Over (Spec ↧ℂ)) (G : Type) [Group G] [Finite G]
    (a : G → (X ⟶ X)) (ha1 : a 1 = 𝟙 X)
    (hamul : ∀ g h, a (g * h) = a h ≫ a g)
    (U V : X.left.Opens) (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (hUV : U ≤ V) (hiU : ∀ g, U ≤ (a g).left ⁻¹ᵁ U)
    (hiV : ∀ g, V ≤ (a g).left ⁻¹ᵁ V) :
    IsOpenImmersion (Spec.map (s2v_i1ahi_invariantRestriction X G a U V hUV hiU hiV)) :=
  s2v_i1ahi_openImmersion_of_local_charts _
    (s2v_i1ahi_transition_injective X G a ha1 hamul U V hU hV hUV hiU hiV)
    (s2v_i1ahi_transition_local_charts X G a ha1 hamul U V hU hV hUV hiU hiV)

lemma s2v_i1ahi_transition_range
    (X : Over (Spec ↧ℂ)) (G : Type) [Group G] [Finite G]
    (a : G → (X ⟶ X)) (ha1 : a 1 = 𝟙 X)
    (hamul : ∀ g h, a (g * h) = a h ≫ a g)
    (U V : X.left.Opens) (hU : IsAffineOpen U)
    (hUV : U ≤ V) (hiU : ∀ g, U ≤ (a g).left ⁻¹ᵁ U)
    (hiV : ∀ g, V ≤ (a g).left ⁻¹ᵁ V) :
    Set.range (Spec.map (s2v_i1ahi_invariantRestriction X G a U V hUV hiU hiV)) =
      s2v_i1a_affineQuotientMap X G a V hiV '' {x | V.ι x ∈ U} := by
  letI := s2v_i1ahi_chart_surjective X G a ha1 hamul U hU hiU
  have hsq := s2v_i1ahi_transition_square X G a U V hUV hiU hiV
  ext z
  constructor
  · rintro ⟨p, rfl⟩
    obtain ⟨x, rfl⟩ := (s2v_i1a_affineQuotientMap X G a U hiU).surjective p
    refine ⟨X.left.homOfLE hUV x, ?_, ?_⟩
    · change (X.left.homOfLE hUV x).1 ∈ U
      rw [Scheme.homOfLE_apply]
      exact x.property
    · exact (congrArg (fun f : U.toScheme ⟶
        Spec ↧(s2v_i1a_chartInvariants X G a V hiV) => f x) hsq).symm
  · rintro ⟨x, hx, rfl⟩
    let t : U.toScheme := ⟨x.1, hx⟩
    refine ⟨s2v_i1a_affineQuotientMap X G a U hiU t, ?_⟩
    have ht : X.left.homOfLE hUV t = x := by
      apply Subtype.ext
      exact Scheme.homOfLE_apply hUV t
    have he := congrArg (fun f : U.toScheme ⟶
      Spec ↧(s2v_i1a_chartInvariants X G a V hiV) => f t) hsq
    change _ = s2v_i1a_affineQuotientMap X G a V hiV (X.left.homOfLE hUV t) at he
    rw [ht] at he
    exact he

end HodgeLean.Foundations.Program
