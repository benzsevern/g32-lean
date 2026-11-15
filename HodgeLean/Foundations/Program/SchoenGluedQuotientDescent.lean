import HodgeLean.Foundations.Program.SchoenQuotientFiniteness

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.Program

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The globally glued invariant projection is an epimorphism for arbitrary scheme targets. -/
theorem s2_gluedQuotientMap_epi (X : Scheme.{0}) [IsIntegral X]
    [IsAffineHom (pullback.diagonal (terminal.from X))]
    (G : Type) [Group G] [Finite G] (ρ : G →* Aut X)
    (hcover : ∀ x : X, ∃ U : s2_InvariantAffineOpen X G ρ, x ∈ U.val) :
    Epi (s2_gluedQuotientMap X G ρ hcover) := by
  constructor
  intro T f g hfg
  apply colimit.hom_ext
  intro U
  haveI : Epi (s2_invariantAffineProjection X G ρ U) :=
    s2_affineSchemeQuotientMap_epi U.val.toScheme G (s2_invariantAffineOpenAction X G ρ U)
  apply (cancel_epi (s2_invariantAffineProjection X G ρ U)).mp
  have he := congrArg (fun k : X ⟶ T => U.val.ι ≫ k) hfg
  simp only [Category.assoc, s2_gluedQuotientMap_ι_assoc] at he
  exact he

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Every invariant morphism from the source to an affine scheme descends
uniquely through the globally glued projection. -/
theorem s2_gluedQuotientDesc_affine (X : Scheme.{0}) [IsIntegral X]
    [IsAffineHom (pullback.diagonal (terminal.from X))]
    (G : Type) [Group G] [Finite G] (ρ : G →* Aut X)
    (hcover : ∀ x : X, ∃ U : s2_InvariantAffineOpen X G ρ, x ∈ U.val)
    (T : Scheme.{0}) [IsAffine T] (f : X ⟶ T)
    (hf : ∀ g : G, (ρ g).asIso.hom ≫ f = f) :
    ∃! d : s2_invariantAffineGlued X G ρ ⟶ T, s2_gluedQuotientMap X G ρ hcover ≫ d = f := by
  have hlocal (U : s2_InvariantAffineOpen X G ρ) :
      ∃! d : s2_invariantAffineQuotientObj X G ρ U ⟶ T,
        s2_invariantAffineProjection X G ρ U ≫ d = U.val.ι ≫ f := by
    apply s2_affineSchemeQuotientDesc G (s2_invariantAffineOpenAction X G ρ U) (U.val.ι ≫ f)
    intro g
    change s2_invariantOpenMap U.val (ρ g).asIso.hom (U.property.2.2 g).ge ≫ U.val.ι ≫ f = _
    rw [s2_invariantOpenMap_ι_assoc, hf g]
  choose d hd huniq using hlocal
  let C : Cocone (s2_invariantAffineDiagram X G ρ) :=
    { pt := T
      ι.app := d
      ι.naturality := by
        intro U V i
        simp only [Functor.const_obj_map, Category.comp_id]
        haveI : Epi (s2_invariantAffineProjection X G ρ U) :=
          s2_affineSchemeQuotientMap_epi U.val.toScheme G (s2_invariantAffineOpenAction X G ρ U)
        apply (cancel_epi (s2_invariantAffineProjection X G ρ U)).mp
        change s2_invariantAffineProjection X G ρ U ≫
          (s2_invariantAffineQuotientMap X G ρ U V i.le ≫ d V) = _
        rw [← Category.assoc, s2_invariantAffineProjection_naturality, Category.assoc, hd V,
          ← Category.assoc, Scheme.homOfLE_ι, ← hd U]
        exact congrArg (fun m => s2_invariantAffineProjection X G ρ U ≫ m)
          (Category.comp_id (d U)).symm }
  let dglobal := colimit.desc (s2_invariantAffineDiagram X G ρ) C
  have hdglobal : s2_gluedQuotientMap X G ρ hcover ≫ dglobal = f := by
    haveI := s2_invariantSourceToScheme_isIso X G ρ hcover
    apply (cancel_epi (s2_invariantSourceToScheme X G ρ)).mp
    apply colimit.hom_ext
    intro U
    simp only [s2_invariantSourceToScheme_ι_assoc, s2_gluedQuotientMap_ι_assoc,
      s2_invariantAffineGluedι, dglobal, Category.assoc, colimit.ι_desc]
    exact hd U
  haveI := s2_gluedQuotientMap_epi X G ρ hcover
  refine ⟨dglobal, hdglobal, ?_⟩
  intro e he
  exact (cancel_epi (s2_gluedQuotientMap X G ρ hcover)).mp (he.trans hdglobal.symm)

end HodgeLean.Foundations.Program
