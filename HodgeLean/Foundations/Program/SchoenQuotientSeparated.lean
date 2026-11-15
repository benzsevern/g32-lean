import HodgeLean.Foundations.Program.SchoenQuotientOverlapFiniteness
import HodgeLean.Foundations.Program.SchoenQuotientOverlapPullbacks

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.Program

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The induced structure on the glued invariant scheme is separated over a
Noetherian affine base when its source is separated and locally of finite type. -/
theorem s2_gluedQuotientStructure_separated {X S : Scheme.{0}} [IsIntegral X]
    [IsAffineHom (pullback.diagonal (terminal.from X))] [IsAffine S] [IsLocallyNoetherian S]
    (s : X ⟶ S) [LocallyOfFiniteType s] [IsSeparated s]
    (G : Type) [Group G] [Finite G] (ρ : G →* Aut X)
    (hover : ∀ g : G, (ρ g).asIso.hom ≫ s = s)
    (hcover : ∀ x : X, ∃ U : s2_InvariantAffineOpen X G ρ, x ∈ U.val) :
    IsSeparated (s2_gluedQuotientStructure s G ρ hover hcover) := by
  let t := s2_gluedQuotientStructure s G ρ hover hcover
  let C := Scheme.IsLocallyDirected.openCover (s2_invariantAffineDiagram X G ρ)
  constructor
  apply IsZariskiLocalAtTarget.of_openCover (Scheme.Pullback.openCoverOfLeftRight C C t t)
  rintro ⟨U, V⟩
  let iU := s2_invariantAffineGluedι X G ρ U
  let iV := s2_invariantAffineGluedι X G ρ V
  let H := (s2_quotientOverlap_isPullback X G ρ hcover U V).flip
  let B := pullback.map (iU ≫ t) (iV ≫ t) t t iU iV (𝟙 _) (Category.comp_id _) (Category.comp_id _)
  have hEq : H.isoPullback.hom ≫ pullback.mapDesc iU iV t =
      s2_quotientOverlapPair s G ρ hover hcover U V := by
    apply pullback.hom_ext
    · simp only [Category.assoc, pullback.mapDesc, pullback.map, pullback.lift_fst,
        Category.comp_id, s2_quotientOverlapPair, iU, iV, t]
      exact H.isoPullback_hom_fst
    · simp only [Category.assoc, pullback.mapDesc, pullback.map, pullback.lift_snd,
        Category.comp_id, s2_quotientOverlapPair, iU, iV, t]
      exact H.isoPullback_hom_snd
  haveI : IsClosedImmersion (s2_quotientOverlapPair s G ρ hover hcover U V) :=
    s2_quotientOverlapPair_closedImmersion s G ρ hover hcover U V
  have hEq' : pullback.mapDesc iU iV t = H.isoPullback.inv ≫
      s2_quotientOverlapPair s G ρ hover hcover U V := by
    rw [← hEq, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  haveI : IsClosedImmersion (pullback.mapDesc iU iV t) := by
    rw [hEq']
    infer_instance
  let K := pullback_map_diagonal_isPullback iU iV t
  change IsClosedImmersion (pullback.snd (pullback.diagonal t) B)
  rw [← K.isoPullback_inv_snd]
  infer_instance

end HodgeLean.Foundations.Program
