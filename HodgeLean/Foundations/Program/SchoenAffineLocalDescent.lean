import HodgeLean.Foundations.Program.SchoenDescentChartTransfer
import HodgeLean.Foundations.Program.SchoenLocalQuotientDescent
import HodgeLean.Foundations.Program.SchoenQuotientOpenImmersions

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.Program

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- An invariant morphism from an affine integral scheme descends on an open
neighborhood of the image of each source point. -/
theorem s2_affineQuotient_localDescent (X : Scheme.{0}) [IsAffine X] [IsIntegral X]
    (G : Type) [Group G] [Finite G] (ρ : G →* Aut X)
    {T : Scheme.{0}} (f : X ⟶ T) (hf : ∀ g : G, (ρ g).asIso.hom ≫ f = f) (x : X) :
    letI := s2_schemeSectionAction X G ρ
    ∃ W : (Spec (CommRingCat.of (FixedPoints.subring Γ(X, ⊤) G))).Opens,
      s2_affineSchemeQuotientMap X G ρ x ∈ W ∧
      ∃ e : W.toScheme ⟶ T,
        (s2_affineSchemeQuotientMap X G ρ ∣_ W) ≫ e =
          (s2_affineSchemeQuotientMap X G ρ ⁻¹ᵁ W).ι ≫ f := by
  letI := s2_schemeSectionAction X G ρ
  obtain ⟨V, hV, hxV, _⟩ := exists_isAffineOpen_mem_and_subset
    (show f x ∈ (⊤ : T.Opens) from trivial)
  obtain ⟨r, hrx, hrV⟩ := s2_invariantMap_principal_refinement X G ρ f hf V x hxV
  let U := X.basicOpen (r : Γ(X, ⊤))
  let hInv := s2_fixedSection_basicOpen_invariant X G ρ r
  let ρU := s2_fixedSection_basicOpenAction X G ρ r
  let hEquiv := s2_fixedSection_basicOpenAction_ι X G ρ r
  have hU : IsAffineOpen U := (isAffineOpen_top X).basicOpen r.val
  haveI : IsAffine U.toScheme := hU
  have hne : (U : Set X).Nonempty := ⟨x, hrx⟩
  haveI : Nonempty U.toScheme := hne.to_subtype
  haveI : IsIntegral U.toScheme := isIntegral_of_isOpenImmersion U.ι
  let q := s2_affineSchemeQuotientMap X G ρ
  let p := s2_affineSchemeQuotientMap U.toScheme G ρU
  let i := s2_quotientComparison G ρU ρ U.ι hEquiv
  haveI : IsOpenImmersion i := s2_quotientComparison_openImmersion G ρU ρ U.ι hEquiv
  have hcomm : U.ι ≫ q = p ≫ i :=
    (s2_affineSchemeQuotientMap_naturality G ρU ρ U.ι hEquiv).symm
  have hrange : q ⁻¹' Set.range i = Set.range U.ι := by
    rw [s2_commutative_square_range U.ι p q i hcomm
      (s2_affineSchemeQuotientMap_surjective U.toScheme G ρU)]
    exact s2_affineQuotient_preimage_image_range G ρU ρ U.ι hEquiv
  obtain ⟨d, hd, _⟩ := s2_invariantOpen_quotientDesc G ρ f hf U hU hne hInv V hV hrV
  obtain ⟨e, he⟩ := s2_descent_chart_transfer U.ι p q i hcomm hrange f d hd
  refine ⟨i.opensRange, ?_, e, he⟩
  change q x ∈ Set.range i
  refine ⟨p ⟨x, hrx⟩, ?_⟩
  exact (congrArg (fun k => k ⟨x, hrx⟩) hcomm).symm

end HodgeLean.Foundations.Program
