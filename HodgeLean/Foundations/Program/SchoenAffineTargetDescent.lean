import HodgeLean.Foundations.Program.SchoenAffineLocalDescent

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.Program

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Invariant morphisms from affine integral schemes descend uniquely to arbitrary scheme targets. -/
theorem s2_affineSchemeQuotientDesc_arbitrary (X : Scheme.{0}) [IsAffine X] [IsIntegral X]
    (G : Type) [Group G] [Finite G] (ρ : G →* Aut X)
    {T : Scheme.{0}} (f : X ⟶ T) (hf : ∀ g : G, (ρ g).asIso.hom ≫ f = f) :
    letI := s2_schemeSectionAction X G ρ
    ∃! d : Spec (CommRingCat.of (FixedPoints.subring Γ(X, ⊤) G)) ⟶ T,
      s2_affineSchemeQuotientMap X G ρ ≫ d = f := by
  letI := s2_schemeSectionAction X G ρ
  let q := s2_affineSchemeQuotientMap X G ρ
  choose W hW d hd using s2_affineQuotient_localDescent X G ρ f hf
  have hcover : TopologicalSpace.IsOpenCover W := by
    change (⨆ x, W x) = ⊤
    apply top_unique
    intro y _
    obtain ⟨x, rfl⟩ := s2_affineSchemeQuotientMap_surjective X G ρ y
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hW x⟩
  haveI : Surjective q := ⟨s2_affineSchemeQuotientMap_surjective X G ρ⟩
  obtain ⟨e, he⟩ := s2_descent_of_openCover q
    (s2_affineSchemeQuotientMap_stalkMap_injective X G ρ) f W hcover d hd
  haveI := s2_affineSchemeQuotientMap_epi X G ρ
  refine ⟨e, he, ?_⟩
  intro e' he'
  exact (cancel_epi q).mp (he'.trans he.symm)

end HodgeLean.Foundations.Program
