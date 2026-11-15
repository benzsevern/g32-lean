import HodgeLean.Foundations.Program.SchoenQuotientOverlapProducts

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.Program

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The quotient of an invariant affine intersection is the actual intersection
of the two glued quotient charts. -/
theorem s2_quotientOverlap_isPullback (X : Scheme.{0}) [IsIntegral X]
    [IsAffineHom (pullback.diagonal (terminal.from X))]
    (G : Type) [Group G] [Finite G] (ρ : G →* Aut X)
    (hcover : ∀ x : X, ∃ U : s2_InvariantAffineOpen X G ρ, x ∈ U.val)
    (U V : s2_InvariantAffineOpen X G ρ) :
    let W := s2_invariantAffineOpenInf X G ρ U V
    IsPullback
      (s2_invariantAffineQuotientMap X G ρ W V (by change U.val ⊓ V.val ≤ V.val; exact inf_le_right))
      (s2_invariantAffineQuotientMap X G ρ W U (by change U.val ⊓ V.val ≤ U.val; exact inf_le_left))
      (s2_invariantAffineGluedι X G ρ V) (s2_invariantAffineGluedι X G ρ U) := by
  let W := s2_invariantAffineOpenInf X G ρ U V
  have hWU : W ≤ U := by change U.val ⊓ V.val ≤ U.val; exact inf_le_left
  have hWV : W ≤ V := by change U.val ⊓ V.val ≤ V.val; exact inf_le_right
  let a := s2_invariantAffineQuotientMap X G ρ W U hWU
  let b := s2_invariantAffineQuotientMap X G ρ W V hWV
  haveI : IsOpenImmersion a := s2_invariantAffineDiagram_map_openImmersion X G ρ (homOfLE hWU)
  have ha := s2_invariantAffineQuotientMap_gluedι X G ρ W U hWU
  have hb := s2_invariantAffineQuotientMap_gluedι X G ρ W V hWV
  apply IsOpenImmersion.isPullback b a (s2_invariantAffineGluedι X G ρ V)
    (s2_invariantAffineGluedι X G ρ U) (ha.trans hb.symm)
  apply TopologicalSpace.Opens.ext
  ext u
  change s2_invariantAffineGluedι X G ρ U u ∈ Set.range (s2_invariantAffineGluedι X G ρ V) ↔
    u ∈ Set.range a
  constructor
  · intro hu
    obtain ⟨x, rfl⟩ := s2_affineSchemeQuotientMap_surjective U.val.toScheme G
      (s2_invariantAffineOpenAction X G ρ U) u
    have hp : s2_gluedQuotientMap X G ρ hcover x.val ∈
        Set.range (s2_invariantAffineGluedι X G ρ V) := by
      have he : s2_gluedQuotientMap X G ρ hcover x.val =
          s2_invariantAffineGluedι X G ρ U (s2_invariantAffineProjection X G ρ U x) :=
        congrArg (fun f => f x) (s2_gluedQuotientMap_ι X G ρ hcover U)
      rw [he]
      exact hu
    have hxV : x.val ∈ V.val :=
      (congrArg (fun A : Set X => x.val ∈ A) (s2_gluedQuotientMap_preimage_chart X G ρ hcover V)).mp hp
    let w : W.val.toScheme := ⟨x.val, x.property, hxV⟩
    refine ⟨s2_invariantAffineProjection X G ρ W w, ?_⟩
    have he := congrArg (fun f => f w) (s2_invariantAffineProjection_naturality X G ρ W U hWU)
    have hx : X.homOfLE hWU w = x := by
      apply U.val.ι.isOpenEmbedding.injective
      exact congrArg (fun f => f w) (Scheme.homOfLE_ι X hWU)
    exact he.trans (congrArg (s2_invariantAffineProjection X G ρ U) hx)
  · rintro ⟨w, rfl⟩
    exact ⟨b w, congrArg (fun f => f w) (hb.trans ha.symm)⟩

end HodgeLean.Foundations.Program
