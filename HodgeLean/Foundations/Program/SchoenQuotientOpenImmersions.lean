import HodgeLean.Foundations.Program.SchoenQuotientOverlapNeighborhoods
import HodgeLean.Foundations.Program.SchoenEquivariantOpenLifts
import HodgeLean.Foundations.Program.SchoenInvariantSpectrumMaps

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Equivariant open immersions of affine domains induce scheme open immersions
between their finite-group invariant spectra. -/
theorem s2_quotientComparison_openImmersion
    {X Y : Scheme.{0}} [IsAffine X] [IsAffine Y]
    [IsDomain Γ(X, ⊤)] [IsDomain Γ(Y, ⊤)]
    (G : Type) [Group G] [Finite G] (ρX : G →* Aut X) (ρY : G →* Aut Y)
    (f : X ⟶ Y) [IsOpenImmersion f]
    (hf : ∀ g : G, f ≫ (ρY g).asIso.hom = (ρX g).asIso.hom ≫ f) :
    IsOpenImmersion (s2_quotientComparison G ρX ρY f hf) := by
  letI := s2_schemeSectionAction X G ρX
  letI := s2_schemeSectionAction Y G ρY
  let k := s2_quotientComparison G ρX ρY f hf
  apply IsOpenImmersion.of_forall_source_exists k
    (s2_affineSchemeQuotientMap_injective_of_openImmersion G ρX ρY f hf)
  intro p
  obtain ⟨x, hxp⟩ := s2_affineSchemeQuotientMap_surjective X G ρX p
  obtain ⟨r, hrx, hrim⟩ := s2_equivariantOpenImmersion_principal_refinement G ρX ρY f hf x
  let rX := s2_fixedSectionPullback G ρX ρY f hf r
  let U := X.basicOpen (rX : Γ(X, ⊤))
  let V := Y.basicOpen (r : Γ(Y, ⊤))
  have hpre : f ⁻¹ᵁ V = U := Scheme.preimage_basicOpen_top f (r : Γ(Y, ⊤))
  have hxr : x ∈ U := (congrArg (fun W : X.Opens => x ∈ W) hpre).mp hrx
  have hr0 : (r : Γ(Y, ⊤)) ≠ 0 := by
    intro he
    simpa only [he, Scheme.basicOpen_zero, TopologicalSpace.Opens.mem_bot] using hrx
  have hrX0 : (rX : Γ(X, ⊤)) ≠ 0 := by
    intro he
    have hxzero : x ∈ X.basicOpen (0 : Γ(X, ⊤)) := he ▸ hxr
    simpa only [Scheme.basicOpen_zero, TopologicalSpace.Opens.mem_bot] using hxzero
  let ρU := s2_fixedSection_basicOpenAction X G ρX rX
  let ρV := s2_fixedSection_basicOpenAction Y G ρY r
  haveI : IsAffine U.toScheme := (isAffineOpen_top X).basicOpen (rX : Γ(X, ⊤))
  haveI : IsAffine V.toScheme := (isAffineOpen_top Y).basicOpen (r : Γ(Y, ⊤))
  have hU := s2_fixedSection_basicOpenAction_ι X G ρX rX
  have hV := s2_fixedSection_basicOpenAction_ι Y G ρY r
  obtain ⟨t, htiso, htfac, hteq⟩ := s2_equivariantOpenImmersion_openLift G ρX ρY f hf
    U V hpre ρU ρV hU hV hrim
  haveI : IsIso t := htiso
  let jX := s2_quotientComparison G ρU ρX U.ι hU
  let jY := s2_quotientComparison G ρV ρY V.ι hV
  haveI : IsOpenImmersion jX := s2_principalOpen_quotientComparison_openImmersion X G ρX rX hrX0
  haveI : IsOpenImmersion jY := s2_principalOpen_quotientComparison_openImmersion Y G ρY r hr0
  haveI : IsIso (s2_quotientComparison G ρU ρV t hteq) :=
    s2_affineSchemeQuotientMap_isIso_of_isIso G ρU ρV t hteq
  have hsq : jX ≫ k = s2_quotientComparison G ρU ρV t hteq ≫ jY :=
    s2_quotientComparison_square G ρU ρV ρX ρY U.ι f t V.ι hU hf hteq hV htfac.symm
  refine ⟨_, jX, inferInstance, ?_, ?_⟩
  · change p ∈ Set.range jX
    let u : U.toScheme := ⟨x, hxr⟩
    refine ⟨s2_affineSchemeQuotientMap U.toScheme G ρU u, ?_⟩
    have he := congrArg (fun m => m u) (s2_affineSchemeQuotientMap_naturality G ρU ρX U.ι hU)
    exact he.trans hxp
  · rw [hsq]
    infer_instance

end HodgeLean.Foundations.Program
