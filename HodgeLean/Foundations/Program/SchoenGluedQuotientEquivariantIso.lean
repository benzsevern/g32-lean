import HodgeLean.Foundations.Program.SchoenGlobalTargetDescent
import HodgeLean.Foundations.Program.SchoenQuotientBase
import HodgeLean.Foundations.Program.SchoenProjectiveBaseIso

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace HodgeLean.Foundations.Program

/-- An equivariant source isomorphism induces an actual isomorphism of the glued invariant quotients. -/
theorem s2_gluedQuotient_iso_of_equivariantIso {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y]
    [IsAffineHom (pullback.diagonal (terminal.from X))]
    [IsAffineHom (pullback.diagonal (terminal.from Y))]
    (G : Type) [Group G] [Finite G] (ρX : G →* Aut X) (ρY : G →* Aut Y)
    (hX : ∀ x : X, ∃ U : s2_InvariantAffineOpen X G ρX, x ∈ U.val)
    (hY : ∀ y : Y, ∃ U : s2_InvariantAffineOpen Y G ρY, y ∈ U.val)
    (e : X ≅ Y)
    (he : ∀ g : G, (ρX g).asIso.hom ≫ e.hom = e.hom ≫ (ρY g).asIso.hom) :
    ∃ eQ : s2_invariantAffineGlued X G ρX ≅ s2_invariantAffineGlued Y G ρY,
      s2_gluedQuotientMap X G ρX hX ≫ eQ.hom = e.hom ≫ s2_gluedQuotientMap Y G ρY hY := by
  have hei (g : G) : (ρY g).asIso.hom ≫ e.inv = e.inv ≫ (ρX g).asIso.hom := by
    apply (cancel_mono e.hom).mp
    simp only [Category.assoc, e.inv_hom_id, Category.comp_id]
    rw [he, ← Category.assoc, e.inv_hom_id, Category.id_comp]
  obtain ⟨f, hf, _⟩ := s2_gluedQuotientDesc_arbitrary X G ρX hX _
    (e.hom ≫ s2_gluedQuotientMap Y G ρY hY) (by
      intro g
      rw [← Category.assoc, he, Category.assoc, s2_gluedQuotientMap_invariant])
  obtain ⟨g, hg, _⟩ := s2_gluedQuotientDesc_arbitrary Y G ρY hY _
    (e.inv ≫ s2_gluedQuotientMap X G ρX hX) (by
      intro g
      rw [← Category.assoc, hei, Category.assoc, s2_gluedQuotientMap_invariant])
  haveI := s2_gluedQuotientMap_epi X G ρX hX
  haveI := s2_gluedQuotientMap_epi Y G ρY hY
  have hfg : f ≫ g = 𝟙 _ := by
    apply (cancel_epi (s2_gluedQuotientMap X G ρX hX)).mp
    rw [← Category.assoc, hf, Category.assoc, hg, ← Category.assoc,
      e.hom_inv_id, Category.id_comp, Category.comp_id]
  have hgf : g ≫ f = 𝟙 _ := by
    apply (cancel_epi (s2_gluedQuotientMap Y G ρY hY)).mp
    rw [← Category.assoc, hg, Category.assoc, hf, ← Category.assoc,
      e.inv_hom_id, Category.id_comp, Category.comp_id]
  exact ⟨⟨f, g, hfg, hgf⟩, hf⟩

/-- Projectivity of the actual glued quotient transports through an equivariant source isomorphism over the base. -/
theorem s2_gluedQuotient_projective_of_equivariantIso {X Y S : Scheme.{0}}
    [IsIntegral X] [IsIntegral Y] [IsAffine S]
    [IsAffineHom (pullback.diagonal (terminal.from X))]
    [IsAffineHom (pullback.diagonal (terminal.from Y))]
    (G : Type) [Group G] [Finite G] (ρX : G →* Aut X) (ρY : G →* Aut Y)
    (hX : ∀ x : X, ∃ U : s2_InvariantAffineOpen X G ρX, x ∈ U.val)
    (hY : ∀ y : Y, ∃ U : s2_InvariantAffineOpen Y G ρY, y ∈ U.val)
    (e : X ≅ Y)
    (he : ∀ g : G, (ρX g).asIso.hom ≫ e.hom = e.hom ≫ (ρY g).asIso.hom)
    (sX : X ⟶ S) (sY : Y ⟶ S) (hes : e.hom ≫ sY = sX)
    (hXs : ∀ g : G, (ρX g).asIso.hom ≫ sX = sX)
    (hYs : ∀ g : G, (ρY g).asIso.hom ≫ sY = sY)
    [IsProjective (s2_gluedQuotientStructure sY G ρY hYs hY)] :
    IsProjective (s2_gluedQuotientStructure sX G ρX hXs hX) := by
  obtain ⟨eQ, hQ⟩ := s2_gluedQuotient_iso_of_equivariantIso G ρX ρY hX hY e he
  haveI := s2_gluedQuotientMap_epi X G ρX hX
  have hbase : eQ.hom ≫ s2_gluedQuotientStructure sY G ρY hYs hY =
      s2_gluedQuotientStructure sX G ρX hXs hX := by
    apply (cancel_epi (s2_gluedQuotientMap X G ρX hX)).mp
    rw [← Category.assoc, hQ, Category.assoc, s2_gluedQuotientStructure_fac,
      hes, s2_gluedQuotientStructure_fac]
  have h := s2_projective_precomp_iso eQ.hom (s2_gluedQuotientStructure sY G ρY hYs hY)
  rwa [hbase] at h

end HodgeLean.Foundations.Program
