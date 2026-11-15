import HodgeLean.Foundations.Program.SchoenInvariantSourceGluing
import HodgeLean.Foundations.Program.SchoenProjectiveInvariantAtlas

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Projective characteristic-zero sources are covered by the index opens of the quotient diagram. -/
theorem s2_projective_invariantAffineIndex_cover (K : Type) [Field K] [CharZero K]
    (X : Scheme.{0}) (s : X ⟶ Spec (CommRingCat.of K)) [IsProjective s]
    (G : Type) [Group G] [Finite G] (ρ : G →* Aut X) :
    ∀ x : X, ∃ U : s2_InvariantAffineOpen X G ρ, x ∈ U.val := by
  intro x
  obtain ⟨U, hU, hx, hinv⟩ := s2_projective_invariantAffineNeighborhood K X s G ρ x
  exact ⟨⟨U, hU, ⟨x, hx⟩, hinv⟩, hx⟩

section
variable (X : Scheme.{0}) [IsIntegral X] [IsAffineHom (pullback.diagonal (terminal.from X))]
    (G : Type) [Group G] [Finite G] (ρ : G →* Aut X)

/-- The affine quotient projections form a cocone to the glued invariant spectra. -/
def s2_invariantQuotientCocone : Cocone (s2_invariantAffineSourceDiagram X G ρ) where
  pt := s2_invariantAffineGlued X G ρ
  ι.app U := s2_invariantAffineProjection X G ρ U ≫ s2_invariantAffineGluedι X G ρ U
  ι.naturality {U V} i := by
    simp only [Functor.const_obj_map, Category.comp_id]
    change X.homOfLE i.le ≫ (s2_invariantAffineProjection X G ρ V ≫
      s2_invariantAffineGluedι X G ρ V) = _
    rw [← Category.assoc, ← s2_invariantAffineProjection_naturality, Category.assoc]
    exact congrArg (fun m => s2_invariantAffineProjection X G ρ U ≫ m)
      (colimit.w (s2_invariantAffineDiagram X G ρ) i)

/-- The map from source-chart gluing to invariant-chart gluing. -/
def s2_sourceToGluedQuotient :
    colimit (s2_invariantAffineSourceDiagram X G ρ) ⟶ s2_invariantAffineGlued X G ρ :=
  colimit.desc _ (s2_invariantQuotientCocone X G ρ)

/-- The glued morphism restricts to each original affine quotient projection. -/
@[reassoc]
theorem s2_sourceToGluedQuotient_ι (U : s2_InvariantAffineOpen X G ρ) :
    colimit.ι (s2_invariantAffineSourceDiagram X G ρ) U ≫ s2_sourceToGluedQuotient X G ρ =
      s2_invariantAffineProjection X G ρ U ≫ s2_invariantAffineGluedι X G ρ U :=
  colimit.ι_desc _ U

/-- The global morphism from a covered scheme to its glued invariant spectra. -/
def s2_gluedQuotientMap
    (hcover : ∀ x : X, ∃ U : s2_InvariantAffineOpen X G ρ, x ∈ U.val) :
    X ⟶ s2_invariantAffineGlued X G ρ :=
  letI := s2_invariantSourceToScheme_isIso X G ρ hcover
  inv (s2_invariantSourceToScheme X G ρ) ≫ s2_sourceToGluedQuotient X G ρ

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The global morphism agrees with the actual affine quotient map on every invariant chart. -/
@[reassoc]
theorem s2_gluedQuotientMap_ι
    (hcover : ∀ x : X, ∃ U : s2_InvariantAffineOpen X G ρ, x ∈ U.val)
    (U : s2_InvariantAffineOpen X G ρ) :
    U.val.ι ≫ s2_gluedQuotientMap X G ρ hcover =
      s2_invariantAffineProjection X G ρ U ≫ s2_invariantAffineGluedι X G ρ U := by
  haveI := s2_invariantSourceToScheme_isIso X G ρ hcover
  unfold s2_gluedQuotientMap
  rw [← s2_invariantSourceToScheme_ι X G ρ U]
  simp only [Category.assoc, IsIso.hom_inv_id_assoc]
  exact s2_sourceToGluedQuotient_ι X G ρ U

/-- The global morphism is surjective because every quotient chart projection is surjective. -/
theorem s2_gluedQuotientMap_surjective
    (hcover : ∀ x : X, ∃ U : s2_InvariantAffineOpen X G ρ, x ∈ U.val) :
    Function.Surjective (s2_gluedQuotientMap X G ρ hcover) := by
  intro p
  obtain ⟨U, a, rfl⟩ := s2_invariantAffineGluedι_jointly_surjective X G ρ p
  obtain ⟨u, hu⟩ := s2_affineSchemeQuotientMap_surjective U.val.toScheme G
    (s2_invariantAffineOpenAction X G ρ U) a
  refine ⟨u.val, ?_⟩
  have he := congrArg (fun m => m u) (s2_gluedQuotientMap_ι X G ρ hcover U)
  exact he.trans (congrArg (s2_invariantAffineGluedι X G ρ U) hu)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The original scheme action preserves the globally glued invariant projection. -/
theorem s2_gluedQuotientMap_invariant
    (hcover : ∀ x : X, ∃ U : s2_InvariantAffineOpen X G ρ, x ∈ U.val) (g : G) :
    (ρ g).asIso.hom ≫ s2_gluedQuotientMap X G ρ hcover = s2_gluedQuotientMap X G ρ hcover := by
  haveI := s2_invariantSourceToScheme_isIso X G ρ hcover
  apply (cancel_epi (s2_invariantSourceToScheme X G ρ)).mp
  apply colimit.hom_ext
  intro U
  simp only [s2_invariantSourceToScheme_ι_assoc]
  have hU : U.val.ι ≫ (ρ g).asIso.hom =
      (s2_invariantAffineOpenAction X G ρ U g).asIso.hom ≫ U.val.ι :=
    (s2_invariantOpenMap_ι U.val (ρ g).asIso.hom (U.property.2.2 g).ge).symm
  calc
    U.val.ι ≫ (ρ g).asIso.hom ≫ s2_gluedQuotientMap X G ρ hcover =
        (s2_invariantAffineOpenAction X G ρ U g).asIso.hom ≫ U.val.ι ≫
          s2_gluedQuotientMap X G ρ hcover := by rw [← Category.assoc, hU, Category.assoc]
    _ = (s2_invariantAffineOpenAction X G ρ U g).asIso.hom ≫
        s2_invariantAffineProjection X G ρ U ≫ s2_invariantAffineGluedι X G ρ U := by
      rw [s2_gluedQuotientMap_ι]
    _ = s2_invariantAffineProjection X G ρ U ≫ s2_invariantAffineGluedι X G ρ U := by
      rw [← Category.assoc]
      exact congrArg (fun m => m ≫ s2_invariantAffineGluedι X G ρ U)
        (s2_affineSchemeQuotientMap_invariant U.val.toScheme G
          (s2_invariantAffineOpenAction X G ρ U) g)
    _ = U.val.ι ≫ s2_gluedQuotientMap X G ρ hcover := (s2_gluedQuotientMap_ι X G ρ hcover U).symm

end
end HodgeLean.Foundations.Program
