import HodgeLean.Foundations.Program.SchoenTowerI1aPrincipalFactors

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry Topology
namespace HodgeLean.Foundations.Program

lemma s2v_i1ahi_principal_target_factor
    (X : Over (Spec ↧ℂ)) (G : Type) [Group G] [Finite G]
    (a : G → (X ⟶ X)) (ha1 : a 1 = 𝟙 X)
    (hamul : ∀ g h, a (g * h) = a h ≫ a g)
    (U : X.left.Opens) (hU : IsAffineOpen U)
    (hiU : ∀ g, U ≤ (a g).left ⁻¹ᵁ U)
    (T : Scheme) (f : U.toScheme ⟶ T)
    (hf : ∀ g, (a g).left.resLE U U (hiU g) ≫ f = f)
    (O : T.Opens) (hO : IsAffineOpen O)
    (W : (Spec ↧(s2v_i1a_chartInvariants X G a U hiU)).Opens)
    (hW : (s2v_i1a_affineQuotientMap X G a U hiU) ⁻¹ᵁ W = f ⁻¹ᵁ O)
    (r : s2v_i1a_chartInvariants X G a U hiU) (hr : PrimeSpectrum.basicOpen r ≤ W) :
    ∃ v : (show (Spec ↧(s2v_i1a_chartInvariants X G a U hiU)).Opens from
        PrimeSpectrum.basicOpen r).toScheme ⟶ T,
      (s2v_i1a_affineQuotientMap X G a U hiU ∣_ PrimeSpectrum.basicOpen r) ≫ v =
        ((s2v_i1a_affineQuotientMap X G a U hiU) ⁻¹ᵁ PrimeSpectrum.basicOpen r).ι ≫ f := by
  let q := s2v_i1a_affineQuotientMap X G a U hiU
  let V := X.left.basicOpen r.val
  have hVU : V ≤ U := X.left.basicOpen_le r.val
  have hV : IsAffineOpen V := hU.basicOpen r.val
  let hiV := s2v_i1ahi_basicOpen_invariant X G a U hiU r
  let j := X.left.homOfLE hVU
  have hjO : Set.range (j ≫ f) ⊆ (O : Set T) := by
    rintro _ ⟨x, rfl⟩
    have hx : j x ∈ q ⁻¹ᵁ PrimeSpectrum.basicOpen r := by
      rw [s2v_i1ahi_quotient_preimage_basicOpen]
      change (j x).1 ∈ V
      exact (Scheme.homOfLE_apply hVU x) ▸ x.property
    have hxW : j x ∈ q ⁻¹ᵁ W := hr hx
    rw [hW] at hxW
    exact hxW
  let fV := IsOpenImmersion.lift O.ι (j ≫ f) (by simpa only [Scheme.Opens.range_ι] using hjO)
  have hfV : fV ≫ O.ι = j ≫ f := IsOpenImmersion.lift_fac _ _ _
  have hi : ∀ g, (a g).left.resLE V V (hiV g) ≫ fV = fV := by
    intro g
    apply (cancel_mono O.ι).mp
    rw [Category.assoc, hfV, ← Category.assoc]
    have hj : (a g).left.resLE V V (hiV g) ≫ j =
        j ≫ (a g).left.resLE U U (hiU g) := by
      simp only [j, Scheme.Hom.resLE_map, Scheme.Hom.map_resLE]
    rw [hj, Category.assoc, hf]
  letI : IsAffine O.toScheme := hO
  obtain ⟨v, hv, _⟩ := s2v_i1ahi_affine_target_factor X G a V hV hiV O.toScheme fV hi
  obtain ⟨e, he⟩ := s2v_i1ahi_principal_chart_iso_square X G a ha1 hamul U V hU hVU hiU hiV r rfl
  refine ⟨e.inv ≫ v ≫ O.ι, ?_⟩
  apply s2v_i1ahi_factor_square_on_open q j _ e
    (s2v_i1a_affineQuotientMap X G a V hiV) he
  · rw [s2v_i1ahi_quotient_preimage_basicOpen]
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      change (j y).1 ∈ V
      exact (Scheme.homOfLE_apply hVU y) ▸ y.property
    · intro hx
      exact ⟨⟨x.1, hx⟩, Subtype.ext (Scheme.homOfLE_apply hVU _)⟩
  · rw [← Category.assoc, hv, hfV]

end HodgeLean.Foundations.Program
