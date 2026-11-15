import HodgeLean.Foundations.Program.SchoenTowerI1aProjectiveFiniteNeighborhood
import HodgeLean.Foundations.Program.SchoenTowerI1aProjectiveCover
import HodgeLean.Foundations.Program.SchoenTowerI1aQuotientAssembly
import HodgeLean.Foundations.Program.SchoenTowerI1aChartDominance
import HodgeLean.Foundations.Program.SchoenTowerI1aAffineDescent
import HodgeLean.Foundations.Program.SchoenTowerI1aPreDefs
import HodgeLean.Foundations.Program.SchoenTowerI1aFiniteHelpers
import HodgeLean.Foundations.Program.SchoenTowerI1aChartTransitions
import HodgeLean.Foundations.Program.SchoenCycleCanonicalGraphAlgebraic

/-! # Shared finite-quotient predecessors for I1a
Implications from finite group actions and projectivity, with actual invariant
chart maps and compatibility squares. HC no distance; AV milestone no distance.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
namespace HodgeLean.Foundations.Program

private lemma chart_pullback_id (X : Scheme) (U : X.Opens)
    (h : U ≤ (𝟙 X) ⁻¹ᵁ U) : (𝟙 X : X ⟶ X).appLE U U h = 𝟙 _ := by
  simp only [Scheme.Hom.appLE, Scheme.Hom.id_app, Category.id_comp]
  exact X.presheaf.map_id _

private abbrev chartAction
    (X : Over (Spec ↧ℂ)) (G : Type) [Group G]
    (a : G → (X ⟶ X)) (ha1 : a 1 = 𝟙 X)
    (hamul : ∀ g h, a (g * h) = a h ≫ a g)
    (U : X.left.Opens) (hinvU : ∀ g, U ≤ (a g).left ⁻¹ᵁ U) :
    MulSemiringAction G Γ(X.left, U) where
  smul g r := ((a g⁻¹).left.appLE U U (hinvU g⁻¹)).hom r
  one_smul r := by
    have h : (a 1).left = 𝟙 X.left := congrArg Over.Hom.left ha1
    change ((a (1 : G)⁻¹).left.appLE U U _).hom r = r
    simp only [inv_one, h, chart_pullback_id, CommRingCat.hom_id, RingHom.id_apply]
  mul_smul g h r := by
    have he := Scheme.Hom.appLE_comp_appLE (a g⁻¹).left (a h⁻¹).left U U U
      (hinvU h⁻¹) (hinvU g⁻¹)
    have hm : (a (h⁻¹ * g⁻¹)).left = (a g⁻¹).left ≫ (a h⁻¹).left :=
      congrArg Over.Hom.left (hamul h⁻¹ g⁻¹)
    change ((a (g * h)⁻¹).left.appLE U U _).hom r =
      ((a g⁻¹).left.appLE U U _).hom (((a h⁻¹).left.appLE U U _).hom r)
    simp only [mul_inv_rev, hm]
    rw [← he]
    rfl
  smul_zero g := map_zero _
  smul_one g := map_one _
  smul_add g := map_add _
  smul_mul g := map_mul _

private lemma chart_base_comp
    (X Y : Over (Spec ↧ℂ)) (f : X ⟶ Y)
    (U : Y.left.Opens) (V : X.left.Opens) (h : V ≤ f.left ⁻¹ᵁ U) :
    Y.hom.appLE ⊤ U le_top ≫ f.left.appLE U V h =
      X.hom.appLE ⊤ V le_top := by
  rw [Scheme.Hom.appLE_comp_appLE, f.w]

private def chartBase (X : Over (Spec ↧ℂ)) (U : X.left.Opens) :
    CommRingCat.of ℂ ⟶ Γ(X.left, U) :=
  (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv ≫ X.hom.appLE ⊤ U le_top

private lemma chart_eval_base (X : Over (Spec ↧ℂ)) (U : X.left.Opens)
    (x : ComplexPoint X) (hx : ⊤ ≤ x.left ⁻¹ᵁ U) :
    chartBase X U ≫ x.left.appLE U ⊤ hx ≫
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom = 𝟙 _ := by
  dsimp [chartBase]
  simp only [Category.assoc]
  rw [← Category.assoc (X.hom.appLE ⊤ U le_top), chart_base_comp]
  simp [chart_pullback_id]

/-- Distinct finite orbits in an affine chart are separated by an invariant section.
Source: SGA 1, Exposé V, §1, finite affine quotients; Mathlib, Algebra.IsInvariant.exists_smul_of_under_eq. -/
theorem s2v_i1a_pre_affine_separation_aux
    (X : Over (Spec ↧ℂ)) (G : Type) [Group G] [Finite G]
    (a : G → (X ⟶ X)) (ha1 : a 1 = 𝟙 X)
    (hamul : ∀ g h, a (g * h) = a h ≫ a g)
    (U : X.left.Opens) (hU : IsAffineOpen U)
    (hinvU : ∀ g, U ≤ (a g).left ⁻¹ᵁ U)
    (x y : ComplexPoint X)
    (hx : ⊤ ≤ x.left ⁻¹ᵁ U) (hy : ⊤ ≤ y.left ⁻¹ᵁ U)
    (hne : ¬ ∃ g, Point.map (a g) x = y) :
    ∃ r : s2v_i1a_chartInvariants X G a U hinvU,
      (x.left.appLE U ⊤ hx ≫ (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom).hom r.val ≠
      (y.left.appLE U ⊤ hy ≫ (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom).hom r.val := by
  letI : Algebra ℂ Γ(X.left, U) := (chartBase X U).hom.toAlgebra
  letI := chartAction X G a ha1 hamul U hinvU
  have hbase (g : G) : chartBase X U ≫ (a g).left.appLE U U (hinvU g) =
      chartBase X U := by
    dsimp [chartBase]
    rw [Category.assoc, chart_base_comp]
  letI : SMulCommClass G ℂ Γ(X.left, U) := ⟨by
    intro g c r
    change ((a g⁻¹).left.appLE U U _).hom ((chartBase X U).hom c * r) =
      (chartBase X U).hom c * ((a g⁻¹).left.appLE U U _).hom r
    rw [map_mul]
    have hc := congrArg (fun f : CommRingCat.of ℂ ⟶ Γ(X.left, U) => f.hom c) (hbase g⁻¹)
    exact congrArg (fun t => t * ((a g⁻¹).left.appLE U U _).hom r) hc⟩
  let ev (z : ComplexPoint X) (hz : ⊤ ≤ z.left ⁻¹ᵁ U) : Γ(X.left, U) →ₐ[ℂ] ℂ :=
    { (z.left.appLE U ⊤ hz ≫ (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom).hom with
      commutes' := fun c => congrArg (fun f : CommRingCat.of ℂ ⟶ CommRingCat.of ℂ => f.hom c)
        (chart_eval_base X U z hz) }
  have hno : ¬ ∃ g : G, ∀ r : Γ(X.left, U), ev y hy r = ev x hx (g • r) := by
    rintro ⟨g, hg⟩
    apply hne
    refine ⟨g⁻¹, ?_⟩
    have he : (a g⁻¹).left.appLE U U (hinvU g⁻¹) ≫ x.left.appLE U ⊤ hx =
        y.left.appLE U ⊤ hy := by
      apply (cancel_mono (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom).mp
      ext r
      exact (hg r).symm
    have hc := Scheme.Hom.appLE_comp_appLE x.left (a g⁻¹).left U U ⊤ (hinvU g⁻¹) hx
    rw [hc] at he
    have hf := hU.SpecMap_appLE_fromSpec (x.left ≫ (a g⁻¹).left)
      (isAffineOpen_top (Spec (CommRingCat.of ℂ))) (hx.trans ((TopologicalSpace.Opens.map x.left.base).map
        (homOfLE (hinvU g⁻¹))).le)
    have hf' := hU.SpecMap_appLE_fromSpec y.left
      (isAffineOpen_top (Spec (CommRingCat.of ℂ))) hy
    rw [he] at hf
    have hh : x.left ≫ (a g⁻¹).left = y.left := by
      apply (cancel_epi (isAffineOpen_top (Spec (CommRingCat.of ℂ))).fromSpec).mp
      exact hf.symm.trans hf'
    apply Over.OverMorphism.ext
    exact hh
  obtain ⟨r, hr, hneval⟩ := s2e_invariant_separates_evaluation_orbits (ev x hx) (ev y hy) hno
  refine ⟨⟨r, fun g => ?_⟩, hneval⟩
  simpa only [show g⁻¹ • r = ((a (g⁻¹)⁻¹).left.appLE U U _).hom r from rfl,
    inv_inv] using hr g⁻¹

/-- The canonical invariant-ring chart map is finite and surjective.
Source: SGA 1, Exposé V, §1, finite affine quotients; Mathlib, Algebra.IsInvariant.isIntegral. -/
theorem s2v_i1a_pre_affine_finite_aux
    (X : Over (Spec ↧ℂ)) (G : Type) [Group G] [Finite G]
    (a : G → (X ⟶ X)) (ha1 : a 1 = 𝟙 X)
    (hamul : ∀ g h, a (g * h) = a h ≫ a g)
    [LocallyOfFiniteType X.hom]
    (U : X.left.Opens) (hU : IsAffineOpen U)
    (hinvU : ∀ g, U ≤ (a g).left ⁻¹ᵁ U)
    : IsFinite (s2v_i1a_affineQuotientMap X G a U hinvU) ∧
      Surjective (s2v_i1a_affineQuotientMap X G a U hinvU) := by
  letI := s2v_i1ahi_chartAction X G a ha1 hamul U hinvU
  letI := (s2v_i1a_chartInvariants X G a U hinvU).subtype.toAlgebra
  letI := s2v_i1ahi_chart_isInvariant X G a ha1 hamul U hinvU
  let f : Γ(Spec ↧ℂ, ⊤) →+* s2v_i1a_chartInvariants X G a U hinvU :=
    { (X.hom.appLE ⊤ U le_top).hom with
      toFun := fun c => ⟨(X.hom.appLE ⊤ U le_top).hom c, fun g => by
        have he := chart_base_comp X X (a g) U U (hinvU g)
        exact congrArg (fun k : Γ(Spec ↧ℂ, ⊤) ⟶ Γ(X.left, U) => k.hom c) he⟩
      map_one' := Subtype.ext (map_one _)
      map_mul' := fun c d => Subtype.ext (map_mul _ c d)
      map_zero' := Subtype.ext (map_zero _)
      map_add' := fun c d => Subtype.ext (map_add _ c d) }
  have hft : ((s2v_i1a_chartInvariants X G a U hinvU).subtype.comp f).FiniteType :=
    X.hom.finiteType_appLE (isAffineOpen_top _) hU le_top
  have hfin := s2v_i1ahi_finite_invariant_inclusion G
    (s2v_i1a_chartInvariants X G a U hinvU) f hft
  haveI := Algebra.IsInvariant.isIntegral
    (s2v_i1a_chartInvariants X G a U hinvU) Γ(X.left, U) G
  exact s2v_i1ahi_chart_finite_transport X G a U hU hinvU hfin
    (show (s2v_i1a_chartInvariants X G a U hinvU).subtype.IsIntegral from
      Algebra.IsIntegral.isIntegral)

/-- Invariant maps from an affine chart descend uniquely to its invariant spectrum.
Source: SGA 1, Exposé V, §1, categorical property of finite affine quotients. -/
theorem s2v_i1a_pre_affine_descent_aux
    (X : Over (Spec ↧ℂ)) (G : Type) [Group G] [Finite G]
    (a : G → (X ⟶ X)) (ha1 : a 1 = 𝟙 X)
    (hamul : ∀ g h, a (g * h) = a h ≫ a g)
    (U : X.left.Opens) (hU : IsAffineOpen U)
    (hinvU : ∀ g, U ≤ (a g).left ⁻¹ᵁ U)
    (T : Scheme) (f : U.toScheme ⟶ T)
    (hf : ∀ g, (a g).left.resLE U U (hinvU g) ≫ f = f) :
    ∃! v : Spec ↧(s2v_i1a_chartInvariants X G a U hinvU) ⟶ T,
      s2v_i1a_affineQuotientMap X G a U hinvU ≫ v = f := by
  exact s2v_i1ahi_affine_descent X G a ha1 hamul U hU hinvU T f hf

/-- Every orbit in an invariant open of a projective scheme has an invariant affine neighborhood.
Source: SGA 1, Exposé V, Proposition 1.8, quasi-projective finite-group quotients. -/
theorem s2v_i1a_pre_invariant_neighborhood_aux
    (X : Over (Spec ↧ℂ)) (G : Type) [Group G] [Finite G]
    (a : G → (X ⟶ X)) (ha1 : a 1 = 𝟙 X)
    (hamul : ∀ g h, a (g * h) = a h ≫ a g)
    [IsProjective X.hom]
    (N : X.left.Opens) (hN : ∀ g, N ≤ (a g).left ⁻¹ᵁ N)
    (x : X.left) (hx : x ∈ N) :
    ∃ U : X.left.Opens, IsAffineOpen U ∧ U ≤ N ∧
      (∀ g, U ≤ (a g).left ⁻¹ᵁ U) ∧ ∀ g, (a g).left x ∈ U := by
  exact s2v_i1ahi_neighborhood_from_finite_set_affines X G a ha1 hamul N hN
    (s2v_i1ahi_projective_finite_neighborhood X N) x hx

/-- Nested invariant affine charts induce unique open transition maps on their quotients.
Source: SGA 1, Exposé V, §1, restriction of finite quotients to invariant opens. -/
theorem s2v_i1a_pre_affine_transition_aux
    (X : Over (Spec ↧ℂ)) (G : Type) [Group G] [Finite G]
    (a : G → (X ⟶ X)) (ha1 : a 1 = 𝟙 X)
    (hamul : ∀ g h, a (g * h) = a h ≫ a g)
    (U : X.left.Opens) (hU : IsAffineOpen U)
    (hinvU : ∀ g, U ≤ (a g).left ⁻¹ᵁ U)
    (V : X.left.Opens) (hV : IsAffineOpen V)
    (hinvV : ∀ g, V ≤ (a g).left ⁻¹ᵁ V) (hUV : U ≤ V) :
    ∃! j : Spec ↧(s2v_i1a_chartInvariants X G a U hinvU) ⟶
        Spec ↧(s2v_i1a_chartInvariants X G a V hinvV),
      IsOpenImmersion j ∧
      s2v_i1a_affineQuotientMap X G a U hinvU ≫ j =
        X.left.homOfLE hUV ≫ s2v_i1a_affineQuotientMap X G a V hinvV ∧
      (s2v_i1a_affineQuotientMap X G a V hinvV) ⁻¹' Set.range j =
        {x | V.ι x ∈ U} := by
  let j := Spec.map (s2v_i1ahi_invariantRestriction X G a U V hUV hinvU hinvV)
  have hsq := s2v_i1ahi_transition_square X G a U V hUV hinvU hinvV
  refine ⟨j, ⟨s2v_i1ahi_transition_openImmersion X G a ha1 hamul U V hU hV hUV hinvU hinvV,
    hsq, ?_⟩, fun k hk => ?_⟩
  · dsimp only [j]
    rw [s2v_i1ahi_transition_range X G a ha1 hamul U V hU hUV hinvU hinvV]
    exact s2v_i1ahi_chart_saturated_preimage X G a ha1 hamul V hV hinvV U hinvU
  · exact (s2v_i1ahi_transition_unique X G a U V hU hUV hinvU hinvV).unique hk.2.1 hsq

/-- Invariant affine quotient charts glue to a finite scheme map with the prescribed chart squares.
Source: SGA 1, Exposé V, Proposition 1.8; Mathlib, Scheme.GlueData.gluedScheme. -/
theorem s2v_i1a_pre_glue_aux
    (X : Over (Spec ↧ℂ)) (G : Type) [Group G] [Finite G]
    (a : G → (X ⟶ X)) (ha1 : a 1 = 𝟙 X)
    (hamul : ∀ g h, a (g * h) = a h ≫ a g)
    [IsProjective X.hom]
    : ∃ (Q : Over (Spec ↧ℂ)) (q : X ⟶ Q),
      IsFinite q.left ∧ Surjective q.left ∧ (∀ g, a g ≫ q = q) ∧
      ∀ (U : X.left.Opens), IsAffineOpen U →
        ∀ (hU : ∀ g, U ≤ (a g).left ⁻¹ᵁ U),
        ∃ (V : Q.left.Opens) (e : Spec ↧(s2v_i1a_chartInvariants X G a U hU) ≅ V.toScheme),
          q.left ⁻¹ᵁ V = U ∧
          U.ι ≫ q.left = s2v_i1a_affineQuotientMap X G a U hU ≫ e.hom ≫ V.ι := by
  haveI : X.left.IsSeparated := ⟨by
    rw [← CategoryTheory.Limits.terminal.comp_from X.hom]
    infer_instance⟩
  exact s2v_i1ahi_quotient_from_affine_cover X G a ha1 hamul
    (s2v_i1ahi_cover_from_finite_set_affines X G a ha1 hamul
      (s2v_i1ahi_projective_finite_neighborhood X))
    (fun U hU hi => (s2v_i1a_pre_affine_finite_aux X G a ha1 hamul U hU hi).1)

/-- The chart squares imply the categorical property for the glued map.
Source: SGA 1, Exposé V, §1, gluing the categorical property of affine quotients. -/
theorem s2v_i1a_pre_glued_descent_aux
    (X : Over (Spec ↧ℂ)) (G : Type) [Group G] [Finite G]
    (a : G → (X ⟶ X)) (ha1 : a 1 = 𝟙 X)
    (hamul : ∀ g h, a (g * h) = a h ≫ a g)
    [IsProjective X.hom]
    (Q : Over (Spec ↧ℂ)) (q : X ⟶ Q) [IsFinite q.left] [Surjective q.left]
    (hinv : ∀ g, a g ≫ q = q)
    (hcharts : ∀ (U : X.left.Opens), IsAffineOpen U →
      ∀ (hU : ∀ g, U ≤ (a g).left ⁻¹ᵁ U),
      ∃ (V : Q.left.Opens) (e : Spec ↧(s2v_i1a_chartInvariants X G a U hU) ≅ V.toScheme),
        q.left ⁻¹ᵁ V = U ∧
        U.ι ≫ q.left = s2v_i1a_affineQuotientMap X G a U hU ≫ e.hom ≫ V.ι)
    (T : Over (Spec ↧ℂ)) (f : X ⟶ T) (hf : ∀ g, a g ≫ f = f) :
    ∃! v : Q ⟶ T, q ≫ v = f := by
  have hlocal (O : Q.left.Opens) (hO : IsAffineOpen O) :
      ∃ (hi : ∀ g, q.left ⁻¹ᵁ O ≤ (a g).left ⁻¹ᵁ (q.left ⁻¹ᵁ O))
        (e : Spec ↧(s2v_i1a_chartInvariants X G a (q.left ⁻¹ᵁ O) hi) ≅ O.toScheme),
        q.left ∣_ O = s2v_i1a_affineQuotientMap X G a (q.left ⁻¹ᵁ O) hi ≫ e.hom := by
    have hi : ∀ g, q.left ⁻¹ᵁ O ≤ (a g).left ⁻¹ᵁ (q.left ⁻¹ᵁ O) := by
      intro g x hx
      change ((a g).left ≫ q.left) x ∈ O
      rw [show (a g).left ≫ q.left = q.left from congrArg Over.Hom.left (hinv g)]
      exact hx
    obtain ⟨V, e, hp, hs⟩ := hcharts (q.left ⁻¹ᵁ O) (hO.preimage q.left) hi
    obtain ⟨e', he⟩ := s2v_i1ahi_chart_restricted_square X G a Q.left q.left O V hi e hp hs
    exact ⟨hi, e', he⟩
  haveI : IsSchemeTheoreticallyDominant q.left := by
    apply s2v_i1ahi_dominance_of_affine_restrictions
    intro O
    obtain ⟨hi, e, he⟩ := hlocal O O.property
    letI := s2v_i1ahi_chart_schematic_dominance X G a (q.left ⁻¹ᵁ O)
      (O.property.preimage q.left) hi
    rw [he]
    infer_instance
  have hfU (U : X.left.Opens) (hi : ∀ g, U ≤ (a g).left ⁻¹ᵁ U) (g : G) :
      (a g).left.resLE U U (hi g) ≫ (U.ι ≫ f.left) = U.ι ≫ f.left := by
    rw [← Category.assoc, Scheme.Hom.resLE_comp_ι, Category.assoc]
    rw [show (a g).left ≫ f.left = f.left from congrArg Over.Hom.left (hf g)]
  have hl (z : Q.left) : ∃ O : Q.left.Opens, z ∈ O ∧ ∃ v : O.toScheme ⟶ T.left,
      (q.left ∣_ O) ≫ v = (q.left ⁻¹ᵁ O).ι ≫ f.left := by
    obtain ⟨O, hO, hz, _⟩ := exists_isAffineOpen_mem_and_subset
      (show z ∈ (⊤ : Q.left.Opens) from trivial)
    obtain ⟨hi, e, he⟩ := hlocal O hO
    obtain ⟨v, hv, _⟩ := s2v_i1a_pre_affine_descent_aux X G a ha1 hamul
      (q.left ⁻¹ᵁ O) (hO.preimage q.left) hi T.left ((q.left ⁻¹ᵁ O).ι ≫ f.left)
      (hfU _ hi)
    refine ⟨O, hz, e.inv ≫ v, ?_⟩
    rw [he]
    simpa only [Category.assoc, Iso.hom_inv_id_assoc] using hv
  choose O hz v hv using hl
  have hO : (⨆ z, O z) = ⊤ := by
    apply top_unique
    intro z _
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨z, hz z⟩
  obtain ⟨g, hg, huniq⟩ := s2v_i1ahi_assemble_descended_factors q.left f.left O hO v hv
  letI := s2v_i1ahi_scheme_epi_of_schematic_dominance q.left
  have hbase : g ≫ T.hom = Q.hom := by
    apply (cancel_epi q.left).mp
    rw [← Category.assoc, hg, f.w, q.w]
  refine ⟨Over.homMk g hbase, ?_, ?_⟩
  · apply Over.OverMorphism.ext
    exact hg
  · intro w hw
    apply Over.OverMorphism.ext
    exact huniq w.left (congrArg Over.Hom.left hw)

/-- The chart squares identify complex-point fibres with the actual finite action orbits.
Source: SGA 1, Exposé V, §1, geometric fibres of finite quotients. -/
theorem s2v_i1a_pre_glued_orbits_aux
    (X : Over (Spec ↧ℂ)) (G : Type) [Group G] [Finite G]
    (a : G → (X ⟶ X)) (ha1 : a 1 = 𝟙 X)
    (hamul : ∀ g h, a (g * h) = a h ≫ a g)
    [IsProjective X.hom]
    (Q : Over (Spec ↧ℂ)) (q : X ⟶ Q) [IsFinite q.left] [Surjective q.left]
    (hinv : ∀ g, a g ≫ q = q)
    (hcharts : ∀ (U : X.left.Opens), IsAffineOpen U →
      ∀ (hU : ∀ g, U ≤ (a g).left ⁻¹ᵁ U),
      ∃ (V : Q.left.Opens) (e : Spec ↧(s2v_i1a_chartInvariants X G a U hU) ≅ V.toScheme),
        q.left ⁻¹ᵁ V = U ∧
        U.ι ≫ q.left = s2v_i1a_affineQuotientMap X G a U hU ≫ e.hom ≫ V.ι)
    (x y : ComplexPoint X) :
    Point.map q x = Point.map q y ↔ ∃ g, Point.map (a g) x = y := by
  constructor
  · intro hxy
    have heq : x.left ≫ q.left = y.left ≫ q.left := congrArg Over.Hom.left hxy
    obtain ⟨_, ⟨V, hV, rfl⟩, hxV, _⟩ :=
      Q.left.isBasis_affineOpens.exists_subset_of_mem_open
        (show q.left (x.left (IsLocalRing.closedPoint ℂ)) ∈ (⊤ : Q.left.Opens) from trivial)
        (⊤ : Q.left.Opens).isOpen
    let U := q.left ⁻¹ᵁ V
    have hU : IsAffineOpen U := hV.preimage q.left
    have hiU : ∀ g, U ≤ (a g).left ⁻¹ᵁ U := by
      intro g z hz
      change ((a g).left ≫ q.left) z ∈ V
      rw [show (a g).left ≫ q.left = q.left from congrArg Over.Hom.left (hinv g)]
      exact hz
    have hx : ⊤ ≤ x.left ⁻¹ᵁ U := by
      intro z _
      have hz : z = IsLocalRing.closedPoint ℂ := Subsingleton.elim (α := Spec ↧ℂ) _ _
      subst z
      exact hxV
    have hy : ⊤ ≤ y.left ⁻¹ᵁ U := by
      intro z _
      change (y.left ≫ q.left) z ∈ V
      rw [← heq]
      exact hx (show z ∈ (⊤ : (Spec ↧ℂ).Opens) from trivial)
    by_contra hn
    obtain ⟨r, hr⟩ := s2v_i1a_pre_affine_separation_aux X G a ha1 hamul U hU hiU x y hx hy hn
    obtain ⟨W, e, _, hsq⟩ := hcharts U hU hiU
    exact hr (s2v_i1ahi_chart_evaluations_equal X G a U hU hiU Q.left q.left W e hsq
      x.left y.left hx hy heq r)
  · rintro ⟨g, hg⟩
    rw [← hg]
    change x ≫ q = (x ≫ a g) ≫ q
    rw [Category.assoc, hinv g]

/-- The constructed categorical quotient identifies with the supplied one over the original source.
Source: Mathlib, CategoryTheory.Iso; SGA 1, Exposé V, §1, uniqueness of categorical quotients. -/
theorem s2v_i1a_pre_categorical_identification_aux
    (X : Over (Spec ↧ℂ)) (G : Type) [Group G] [Finite G]
    (a : G → (X ⟶ X)) (ha1 : a 1 = 𝟙 X)
    (hamul : ∀ g h, a (g * h) = a h ≫ a g)
    (Q Y : Over (Spec ↧ℂ)) (q : X ⟶ Q) (p : X ⟶ Y)
    (hqinv : ∀ g, a g ≫ q = q) (hpinv : ∀ g, a g ≫ p = p)
    (hq : ∀ (T : Over (Spec ↧ℂ)) (f : X ⟶ T),
      (∀ g, a g ≫ f = f) → ∃! v : Q ⟶ T, q ≫ v = f)
    (hp : ∀ (T : Over (Spec ↧ℂ)) (f : X ⟶ T),
      (∀ g, a g ≫ f = f) → ∃! v : Y ⟶ T, p ≫ v = f) :
    ∃ e : Q ≅ Y, q ≫ e.hom = p ∧ p ≫ e.inv = q := by
  obtain ⟨v, hv, _⟩ := hq Y p hpinv
  obtain ⟨w, hw, _⟩ := hp Q q hqinv
  have hvw : v ≫ w = 𝟙 Q := by
    apply (hq Q q hqinv).unique
    · rw [← Category.assoc, hv, hw]
    · exact Category.comp_id q
  have hwv : w ≫ v = 𝟙 Y := by
    apply (hp Y p hpinv).unique
    · rw [← Category.assoc, hw, hv]
    · exact Category.comp_id p
  exact ⟨⟨v, w, hvw, hwv⟩, hv, hw⟩

end HodgeLean.Foundations.Program
