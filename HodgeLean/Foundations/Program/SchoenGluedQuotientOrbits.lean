import HodgeLean.Foundations.Program.SchoenGluedQuotientProjection

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Two translates of one scheme point differ by a group translate. -/
theorem s2_autAction_orbit_transfer (X : Scheme.{0}) (G : Type) [Group G]
    (ρ : G →* Aut X) (a b : G) (z x y : X)
    (hx : (ρ a).asIso.hom z = x) (hy : (ρ b).asIso.hom z = y) :
    ∃ g : G, (ρ g).asIso.hom x = y := by
  refine ⟨b * a⁻¹, ?_⟩
  rw [map_mul, map_inv]
  change (ρ b).asIso.hom ((ρ a).asIso.inv x) = y
  have hcan : (ρ a).asIso.inv ((ρ a).asIso.hom z) = z :=
    congrArg (fun f : X ⟶ X => f z) (ρ a).asIso.hom_inv_id
  rw [← hx, hcan]
  exact hy

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The globally glued invariant projection has precisely the original group
orbits as its scheme-point fibres. -/
theorem s2_gluedQuotientMap_fibres (X : Scheme.{0}) [IsIntegral X]
    [IsAffineHom (pullback.diagonal (terminal.from X))]
    (G : Type) [Group G] [Finite G] (ρ : G →* Aut X)
    (hcover : ∀ x : X, ∃ U : s2_InvariantAffineOpen X G ρ, x ∈ U.val) (x y : X) :
    s2_gluedQuotientMap X G ρ hcover x = s2_gluedQuotientMap X G ρ hcover y ↔
      ∃ g : G, (ρ g).asIso.hom x = y := by
  constructor
  · intro hxy
    obtain ⟨U, hx⟩ := hcover x
    obtain ⟨V, hy⟩ := hcover y
    let u : U.val.toScheme := ⟨x, hx⟩
    let v : V.val.toScheme := ⟨y, hy⟩
    have heU := congrArg (fun m => m u) (s2_gluedQuotientMap_ι X G ρ hcover U)
    have heV := congrArg (fun m => m v) (s2_gluedQuotientMap_ι X G ρ hcover V)
    have hEq : s2_invariantAffineGluedι X G ρ U (s2_invariantAffineProjection X G ρ U u) =
        s2_invariantAffineGluedι X G ρ V (s2_invariantAffineProjection X G ρ V v) :=
      heU.symm.trans (hxy.trans heV)
    obtain ⟨L, i, j, a, haU, haV⟩ :=
      (Scheme.IsLocallyDirected.ι_eq_ι_iff (s2_invariantAffineDiagram X G ρ)).mp hEq
    obtain ⟨z, hz⟩ := s2_affineSchemeQuotientMap_surjective L.val.toScheme G
      (s2_invariantAffineOpenAction X G ρ L) a
    change s2_invariantAffineProjection X G ρ L z = a at hz
    have hzu : s2_invariantAffineProjection X G ρ U (X.homOfLE i.le z) =
        s2_invariantAffineProjection X G ρ U u := by
      have hn := congrArg (fun m => m z) (s2_invariantAffineProjection_naturality X G ρ L U i.le)
      simp only [Scheme.Hom.comp_apply] at hn
      have he : (s2_invariantAffineDiagram X G ρ).map i (s2_invariantAffineProjection X G ρ L z) =
          s2_invariantAffineProjection X G ρ U u := by rw [hz]; exact haU
      exact hn.symm.trans he
    have hzv : s2_invariantAffineProjection X G ρ V (X.homOfLE j.le z) =
        s2_invariantAffineProjection X G ρ V v := by
      have hn := congrArg (fun m => m z) (s2_invariantAffineProjection_naturality X G ρ L V j.le)
      simp only [Scheme.Hom.comp_apply] at hn
      have he : (s2_invariantAffineDiagram X G ρ).map j (s2_invariantAffineProjection X G ρ L z) =
          s2_invariantAffineProjection X G ρ V v := by rw [hz]; exact haV
      exact hn.symm.trans he
    obtain ⟨gU, hgU⟩ := (s2_affineSchemeQuotientMap_fibres U.val.toScheme G
      (s2_invariantAffineOpenAction X G ρ U) (X.homOfLE i.le z) u).mp hzu
    obtain ⟨gV, hgV⟩ := (s2_affineSchemeQuotientMap_fibres V.val.toScheme G
      (s2_invariantAffineOpenAction X G ρ V) (X.homOfLE j.le z) v).mp hzv
    have huX : (ρ gU).asIso.hom z.val = x := by
      have he := congrArg (fun w : U.val.toScheme => w.val) hgU
      simpa only [s2_invariantAffineOpenAction_apply, Scheme.homOfLE_apply] using he
    have hvX : (ρ gV).asIso.hom z.val = y := by
      have he := congrArg (fun w : V.val.toScheme => w.val) hgV
      simpa only [s2_invariantAffineOpenAction_apply, Scheme.homOfLE_apply] using he
    exact s2_autAction_orbit_transfer X G ρ gU gV z.val x y huX hvX
  · rintro ⟨g, hg⟩
    rw [← hg]
    exact (congrArg (fun f => f x) (s2_gluedQuotientMap_invariant X G ρ hcover g)).symm

/-- Each target quotient chart pulls back to exactly its original invariant affine open. -/
theorem s2_gluedQuotientMap_preimage_chart (X : Scheme.{0}) [IsIntegral X]
    [IsAffineHom (pullback.diagonal (terminal.from X))]
    (G : Type) [Group G] [Finite G] (ρ : G →* Aut X)
    (hcover : ∀ x : X, ∃ U : s2_InvariantAffineOpen X G ρ, x ∈ U.val)
    (U : s2_InvariantAffineOpen X G ρ) :
    s2_gluedQuotientMap X G ρ hcover ⁻¹' Set.range (s2_invariantAffineGluedι X G ρ U) =
      (U.val : Set X) := by
  ext x
  constructor
  · rintro ⟨a, ha⟩
    obtain ⟨u, hu⟩ := s2_affineSchemeQuotientMap_surjective U.val.toScheme G
      (s2_invariantAffineOpenAction X G ρ U) a
    have he := congrArg (fun m => m u) (s2_gluedQuotientMap_ι X G ρ hcover U)
    have hqx : s2_gluedQuotientMap X G ρ hcover u.val =
        s2_gluedQuotientMap X G ρ hcover x :=
      he.trans ((congrArg (s2_invariantAffineGluedι X G ρ U) hu).trans ha)
    obtain ⟨g, hg⟩ := (s2_gluedQuotientMap_fibres X G ρ hcover u.val x).mp hqx
    have hval : ((s2_invariantAffineOpenAction X G ρ U g).asIso.hom u).val = x :=
      (s2_invariantAffineOpenAction_apply X G ρ U g u).trans hg
    exact hval ▸ ((s2_invariantAffineOpenAction X G ρ U g).asIso.hom u).property
  · intro hx
    let u : U.val.toScheme := ⟨x, hx⟩
    refine ⟨s2_invariantAffineProjection X G ρ U u, ?_⟩
    exact (congrArg (fun m => m u) (s2_gluedQuotientMap_ι X G ρ hcover U)).symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The actual affine quotient projection is the pullback of the global projection
along its target chart immersion. -/
theorem s2_gluedQuotientMap_chart_isPullback (X : Scheme.{0}) [IsIntegral X]
    [IsAffineHom (pullback.diagonal (terminal.from X))]
    (G : Type) [Group G] [Finite G] (ρ : G →* Aut X)
    (hcover : ∀ x : X, ∃ U : s2_InvariantAffineOpen X G ρ, x ∈ U.val)
    (U : s2_InvariantAffineOpen X G ρ) :
    IsPullback (s2_invariantAffineProjection X G ρ U) U.val.ι
      (s2_invariantAffineGluedι X G ρ U) (s2_gluedQuotientMap X G ρ hcover) := by
  apply IsOpenImmersion.isPullback _ _ _ _ (s2_gluedQuotientMap_ι X G ρ hcover U)
  apply TopologicalSpace.Opens.ext
  change s2_gluedQuotientMap X G ρ hcover ⁻¹' Set.range (s2_invariantAffineGluedι X G ρ U) =
    Set.range U.val.ι
  rw [Scheme.Opens.range_ι]
  exact s2_gluedQuotientMap_preimage_chart X G ρ hcover U

end HodgeLean.Foundations.Program
