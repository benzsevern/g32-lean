import HodgeConjecture.Statement
import HodgeConjecture.Lemmas.AlgebraicGeometry.Cycle.Component.SmoothClosedLift
import HodgeConjecture.Lemmas.AlgebraicGeometry.Cycle.Component.NormalGeometry
import HodgeConjecture.Lemmas.AlgebraicTopology.LocalHomology.NormalProjectionCoclass
import HodgeConjecture.Lemmas.AlgebraicTopology.Support.RelativeCohomologySheaf
import HodgeConjecture.Lemmas.AlgebraicGeometry.Cycle.SmoothPair.CoclassSection
import HodgeConjecture.Lemmas.AlgebraicGeometry.Cycle.SmoothPair.CoclassOverlap
import HodgeLean.Meta.Tags

/-! # The degree-zero case of the Hodge conjecture

Against the pinned definitions of `HodgeConjecture`, the codimension-zero statement
`Hdg^0(X; ℚ) ≤ algebraicCycleClassSpan X 0` holds as soon as the analytic space `X(ℂ)` is
preconnected, which is the one hypothesis, `ComplexPointsPreconnected`.

* Global sections of a constant sheaf on a preconnected space are constant
  (`exists_eq_constSection`), so `H^0(X(ℂ); ℚ)` has rank at most one (`rank_H0_le_one`).
* The cycle class of the generic point is nonzero (`cycleComponentSheafClass_genericPoint_ne_zero`):
  its support is all of `X(ℂ)`, so forgetting the support is injective, and the normalized coclass
  section has a nonzero germ at any complex point of the smooth locus, because the chart coclass
  pairs to `1` with the normal class on arbitrarily small neighbourhoods.
* The Hodge condition plays no role: the span is all of `H^0`. -/

open CategoryTheory TopologicalSpace Opposite Limits AlgebraicGeometry ComplexPoint
open AlgebraicTopology.Singular

namespace HodgeLean.RealDefs

noncomputable section ConstantSheaf

variable {T : TopCat.{0}} (A : AddCommGrpCat.{0})

/-- The constant presheaf with value `A`. -/
abbrev constPresheaf : TopCat.Presheaf AddCommGrpCat.{0} T := (Functor.const (Opens T)ᵒᵖ).obj A

/-- The constant sheaf with value `A`. -/
abbrev constSheaf : TopCat.Sheaf AddCommGrpCat.{0} T := (TopCat.Sheaf.constantFunctor T).obj A

/-- The constant section with value `a` over `U`. -/
abbrev constSection (U : Opens T) (a : A) : (constSheaf (T := T) A).obj.obj (op U) :=
  (toSheafify (Opens.grothendieckTopology T) (constPresheaf (T := T) A)).app (op U) a

/-- The stalk of a constant presheaf maps back to its value. -/
def constStalkDesc (x : T) : (constPresheaf (T := T) A).stalk x ⟶ A :=
  colimit.desc ((OpenNhds.inclusion x).op ⋙ constPresheaf (T := T) A)
    ⟨A, { app := fun _ => 𝟙 A, naturality := fun _ _ _ => rfl }⟩

/-- The descended map recovers the value from a germ of a constant section. -/
lemma constStalkDesc_germ (x : T) (U : Opens T) (hx : x ∈ U) (a : A) :
    constStalkDesc A x ((constPresheaf (T := T) A).germ U x hx a) = a := by
  change (colimit.ι ((OpenNhds.inclusion x).op ⋙ constPresheaf (T := T) A)
    (op ⟨U, hx⟩) ≫ constStalkDesc A x) a = a
  rw [constStalkDesc, colimit.ι_desc]
  rfl

/-- The stalk map of the unit of sheafification, for the constant presheaf. -/
abbrev constStalkMap (x : T) :
    (constPresheaf (T := T) A).stalk x ⟶ (constSheaf (T := T) A).presheaf.stalk x :=
  (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{0} x).map
    (toSheafify (Opens.grothendieckTopology T) (constPresheaf (T := T) A))

instance (x : T) : IsIso (constStalkMap A x) :=
  TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x _ _

/-- The germ of a constant section is the stalk image of the presheaf germ. -/
lemma germ_constSection (U : Opens T) (x : T) (hx : x ∈ U) (a : A) :
    (constSheaf (T := T) A).presheaf.germ U x hx (constSection A U a) =
      constStalkMap A x ((constPresheaf (T := T) A).germ U x hx a) :=
  (TopCat.Presheaf.stalkFunctor_map_germ_apply (F := constPresheaf (T := T) A)
    (G := (constSheaf (T := T) A).presheaf) U x hx
    (toSheafify (Opens.grothendieckTopology T) (constPresheaf (T := T) A)) a).symm

/-- The germ of a constant section does not depend on the open it is taken over. -/
lemma germ_constSection_top (U : Opens T) (x : T) (hx : x ∈ U) (a : A) :
    (constSheaf (T := T) A).presheaf.germ U x hx (constSection A U a) =
      (constSheaf (T := T) A).presheaf.germ ⊤ x (Opens.mem_top x) (constSection A ⊤ a) := by
  rw [germ_constSection, germ_constSection]
  congr 1
  exact TopCat.Presheaf.germ_res_apply (constPresheaf (T := T) A) (homOfLE le_top) x hx a

omit A in
/-- An isomorphism of abelian groups followed by its inverse is the identity on elements. -/
lemma inv_apply_self {X Y : AddCommGrpCat.{0}} (f : X ⟶ Y) [IsIso f] (u : X) :
    inv f (f u) = u := by
  rw [← ConcreteCategory.comp_apply, IsIso.hom_inv_id]; rfl

omit A in
/-- The inverse of an isomorphism of abelian groups followed by it is the identity on elements. -/
lemma apply_inv_self {X Y : AddCommGrpCat.{0}} (f : X ⟶ Y) [IsIso f] (u : Y) :
    f (inv f u) = u := by
  rw [← ConcreteCategory.comp_apply, IsIso.inv_hom_id]; rfl

/-- Distinct constants have distinct germs at every point. -/
lemma germ_constSection_injective (x : T) {a b : A}
    (h : (constSheaf (T := T) A).presheaf.germ ⊤ x (Opens.mem_top x) (constSection A ⊤ a) =
      (constSheaf (T := T) A).presheaf.germ ⊤ x (Opens.mem_top x) (constSection A ⊤ b)) :
    a = b := by
  rw [germ_constSection, germ_constSection] at h
  have h' := congrArg (constStalkDesc A x) (congrArg (inv (constStalkMap A x)) h)
  rwa [inv_apply_self, inv_apply_self, constStalkDesc_germ, constStalkDesc_germ] at h'

/-- Every germ of a constant sheaf is the germ of a constant section. -/
lemma exists_germ_eq_constSection (s : (constSheaf (T := T) A).obj.obj (op ⊤)) (x : T) :
    ∃ a : A, (constSheaf (T := T) A).presheaf.germ ⊤ x (Opens.mem_top x) s =
      (constSheaf (T := T) A).presheaf.germ ⊤ x (Opens.mem_top x) (constSection A ⊤ a) := by
  obtain ⟨t, ht⟩ : ∃ t, constStalkMap A x t =
      (constSheaf (T := T) A).presheaf.germ ⊤ x (Opens.mem_top x) s :=
    ⟨inv (constStalkMap A x) ((constSheaf (T := T) A).presheaf.germ ⊤ x (Opens.mem_top x) s),
      apply_inv_self _ _⟩
  obtain ⟨U, hxU, a, rfl⟩ := (constPresheaf (T := T) A).exists_germ_eq t
  exact ⟨a, by rw [← ht, ← germ_constSection, germ_constSection_top]⟩

/-- On a preconnected space, every global section of a constant sheaf is constant. -/
theorem exists_eq_constSection [PreconnectedSpace T]
    (s : (constSheaf (T := T) A).obj.obj (op ⊤)) : ∃ a : A, s = constSection A ⊤ a := by
  choose f hf using exists_germ_eq_constSection A s
  have hlc : IsLocallyConstant f := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    obtain ⟨W, hxW, iU, iV, heq⟩ :=
      (constSheaf (T := T) A).presheaf.germ_eq x (Opens.mem_top x) (Opens.mem_top x) _ _ (hf x)
    filter_upwards [W.isOpen.mem_nhds hxW] with y hy
    apply germ_constSection_injective A y
    rw [← hf y, ← TopCat.Presheaf.germ_res_apply _ iU y hy,
      ← TopCat.Presheaf.germ_res_apply _ iV y hy]
    exact congrArg _ heq
  by_cases hT : Nonempty T
  · obtain ⟨x₀⟩ := hT
    refine ⟨f x₀, TopCat.Presheaf.section_ext _ _ _ _ fun x _ => ?_⟩
    rw [hf x, hlc.apply_eq_of_preconnectedSpace x x₀]
  · exact ⟨0, TopCat.Presheaf.section_ext _ _ _ _ fun x _ => (hT ⟨x⟩).elim⟩

end ConstantSheaf

section Rank

open AlgebraicGeometry ComplexPoint

variable (X : Over (Spec ↧ℂ))

/-- Scalar multiplication by `q` sends the constant section `a` to the constant section `q * a`. -/
lemma fieldScalarSheaf_constSection (q a : ℚ) :
    (fieldScalarSheaf ℚ X q).hom.app (op ⊤)
        (constSection (T := TopCat.of (ComplexPoint X)) (AddCommGrpCat.of ℚ) ⊤ a) =
      constSection (T := TopCat.of (ComplexPoint X)) (AddCommGrpCat.of ℚ) ⊤ (q * a) := by
  have h := NatTrans.congr_app
    (toSheafify_naturality (Opens.grothendieckTopology (TopCat.of (ComplexPoint X)))
    ((Functor.const (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ).map
      (AddCommGrpCat.ofHom (AddMonoidHom.mulLeft q)))) (op ⊤)
  have h' := ConcreteCategory.congr_hom h a
  simp only [NatTrans.comp_app, ConcreteCategory.comp_apply] at h'
  exact h'.symm.trans rfl

/-- If `X(ℂ)` is preconnected, `H^0(X(ℂ); ℚ)` has rank at most one. -/
theorem rank_H0_le_one [PreconnectedSpace (ComplexPoint X)] :
    Module.rank ℚ (H^0(X; ℚ)) ≤ 1 := by
  have : PreconnectedSpace (TopCat.of (ComplexPoint X)) := ‹PreconnectedSpace (ComplexPoint X)›
  let e := Sheaf.H.equiv₀
    ((TopCat.Sheaf.constantFunctor ↧(ComplexPoint X)).obj (AddCommGrpCat.of ℚ)) isTerminalTop
  rw [rank_le_one_iff]
  refine ⟨e.symm (constSection (T := TopCat.of (ComplexPoint X)) (AddCommGrpCat.of ℚ) ⊤ 1),
    fun v => ?_⟩
  obtain ⟨a, ha⟩ := exists_eq_constSection (AddCommGrpCat.of ℚ) (e v)
  refine ⟨a, e.injective ?_⟩
  rw [field_smul_eq, ← Sheaf.H.equiv₀_naturality, e.apply_symm_apply, ha,
    fieldScalarSheaf_constSection, mul_one]

end Rank

/-- For a smooth integral projective `X` over `ℂ`, the analytic space `X(ℂ)` is preconnected.

Source: Shafarevich, *Basic Algebraic Geometry 2*, 3rd ed., Ch. VII, §2.2, Theorem 7.1 (an irreducible complex algebraic variety is connected in the complex topology). -/
@[hodge_hypothesis]
structure ComplexPointsPreconnected : Prop where
  preconnected : ∀ (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom],
    PreconnectedSpace (ComplexPoint X)

/-- The generic point of an integral scheme has coheight zero. -/
theorem coheight_genericPoint (Y : Scheme) [IsIntegral Y] :
    Order.coheight (genericPoint Y) = 0 :=
  Order.coheight_eq_zero.mpr fun y _ => genericPoint_specializes y

section ChartCoclass

variable {M : Type} [TopologicalSpace M]
  (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (c : ℕ)
  (e : OpenPartialHomeomorph M (E × (Fin c → ℂ))) (S : Set M)
  (hS : ∀ y ∈ e.source, y ∈ S ↔ (e y).2 = 0)

/-- The chart coclass is nonzero on every open neighbourhood of a support point. -/
theorem chartNormalProjectionCoclass_ne_zero {W : Set M} (hWo : IsOpen W) (hW : W ⊆ e.source)
    {x : M} (hxW : x ∈ W) (h0 : (e x).2 = 0) :
    chartNormalProjectionCoclass E c e S hS W hW ≠ 0 := by
  intro hzero
  let e' := e.restrOpen W hWo
  have hx' : x ∈ e'.source := by
    rw [OpenPartialHomeomorph.restrOpen_source]; exact ⟨hW hxW, hxW⟩
  have hS' : ∀ y ∈ e'.source, y ∈ S ↔ (e' y).2 = 0 := by
    intro y hy
    rw [OpenPartialHomeomorph.restrOpen_source] at hy
    exact hS y hy.1
  have hN := flattenedSupportNeighborhood_subset_source E c e' x hx'
  have hNW : (flattenedSupportNeighborhood E c e' x hx' : Set M) ⊆ W := fun y hy => by
    have := hN hy
    rw [OpenPartialHomeomorph.restrOpen_source] at this
    exact this.2
  have hres := chartNormalProjectionCoclass_restrict E c e S hS hNW hW
  rw [hzero, map_zero] at hres
  have hone := chartNormalProjectionCoclass_apply_normalClass E c e' S hS' x hx' h0
  have heq : chartNormalProjectionCoclass E c e' S hS' (flattenedSupportNeighborhood E c e' x hx')
      hN = chartNormalProjectionCoclass E c e S hS _ (hNW.trans hW) := rfl
  rw [heq, ← hres, map_zero] at hone
  rw [LinearMap.zero_apply] at hone
  exact zero_ne_one hone

end ChartCoclass

section Germ

variable (X : TopCat.{0}) (S : Set X) (n : ℕ)

/-- A relative class whose restriction to every smaller neighbourhood of `x` is nonzero has a
nonzero germ at `x` in the sheafified relative cohomology. -/
theorem supportRelativeCohomologyGerm_ne_zero (V : Opens X) (x : X) (hx : x ∈ V)
    (a : RelativeCohomology ℚ (neighborhoodSupportComplementPair (V : Set X) S) n)
    (h : ∀ (W : Opens X), x ∈ W → ∀ (hWV : W ≤ V),
      relativeCohomologyMap ℚ n
        (neighborhoodSupportInclusionPairMap (W := (W : Set X)) (V := (V : Set X)) hWV S) a ≠ 0) :
    supportRelativeCohomologyGerm X S n V x hx a ≠ 0 := by
  intro hzero
  let P := supportRelativeCohomologyPresheaf X S n
  let m := (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{0} x).map
    (supportRelativeCohomologyToSheaf X S n)
  have : IsIso m := TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x AddCommGrpCat _
  have h1 : m (P.germ V x hx a) = 0 :=
    (TopCat.Presheaf.stalkFunctor_map_germ_apply (F := P)
      (G := (supportRelativeCohomologySheaf X S n).presheaf) V x hx
      (supportRelativeCohomologyToSheaf X S n) a).trans hzero
  have h2 : P.germ V x hx a = P.germ V x hx 0 := by
    have h3 := congrArg (inv m) h1
    erw [inv_apply_self m, map_zero] at h3
    rw [h3]; exact (map_zero _).symm
  obtain ⟨W, hxW, iU, iV, heq⟩ := P.germ_eq x hx hx _ _ h2
  rw [map_zero] at heq
  exact h W hxW (leOfHom iU) heq

end Germ

section OpenTransport

variable {X Y : TopCat.{0}} (f : Y ⟶ X) (hf : Topology.IsOpenEmbedding f)
  (S : Set X) (B : Set Y) (hB : f ⁻¹' S = B)

/-- Transport of a section to the open image is injective. -/
theorem supportRelativeCohomologySectionOnOpen_ne_zero (n : ℕ) (U : Opens X)
    (hU : hf.functor.obj ⊤ = U) (s : (𝓗_[B]^n(Y; ℚ)).presheaf.obj (op ⊤)) (hs : s ≠ 0) :
    supportRelativeCohomologySectionOnOpen f hf S B hB n U hU s ≠ 0 := by
  intro hzero
  apply hs
  let φ := (supportRelativeCohomologySheafOpenIso f hf S B hB n).hom.hom.app (op ⊤)
  let ρ := (𝓗_[S]^n(X; ℚ)).presheaf.map (eqToHom hU.symm).op
  have : IsIso φ := (((sheafToPresheaf _ _).mapIso
    (supportRelativeCohomologySheafOpenIso f hf S B hB n)).app (op ⊤)).isIso_hom
  have h1 : ρ (φ s) = 0 := hzero
  have h2 := congrArg (inv φ) (congrArg (inv ρ) h1)
  erw [inv_apply_self ρ, inv_apply_self φ, map_zero, map_zero] at h2
  exact h2

end OpenTransport

section SmoothPair

open AlgebraicGeometry ComplexPoint

variable (X Y : Over (Spec ↧ℂ)) (i : Y ⟶ X) (m d : ℕ)
  [SmoothOfRelativeDimension m Y.hom] [SmoothOfRelativeDimension d X.hom]
  [IsClosedImmersion i.left]

/-- The normalized chart germ is nonzero at every point of the support. -/
theorem smoothClosedSupportChartCoclassGerm_ne_zero (z : ComplexPoint Y) (x : ComplexPoint X)
    (hx : x ∈ smoothClosedSupportChartOpen X Y i m d z) (hxS : x ∈ Set.range (Point.map i)) :
    smoothClosedSupportChartCoclassGerm X Y i m d z x hx ≠ 0 := by
  apply supportRelativeCohomologyGerm_ne_zero
  intro W hxW hWV hz
  have hr := smoothClosedSupportChartCoclass_restrict X Y i m d z
    (W := (W : Set (ComplexPoint X)))
    (V := (smoothClosedSupportChartOpen X Y i m d z : Set (ComplexPoint X))) hWV (le_refl _)
  exact chartNormalProjectionCoclass_ne_zero _ _ _ _ _ W.isOpen _ hxW
    ((closedImmersionHolomorphicFlatteningChart_mem_range_iff X Y i m d z x hx).mp hxS)
    (hr.symm.trans hz)

/-- The glued normalized coclass section is nonzero as soon as `Y(ℂ)` is nonempty. -/
theorem smoothClosedSupportCoclassSection_ne_zero (w : ComplexPoint Y) :
    smoothClosedSupportCoclassSection X Y i m d ≠ 0 := by
  intro hzero
  have h := smoothClosedSupportCoclassSection_germ X Y i m d (Point.map i w)
  rw [hzero, map_zero, smoothClosedSupportCoclassStalk_eq_chartGerm X Y i m d w (Point.map i w)
    (mem_smoothClosedSupportChartOpen X Y i m d w)] at h
  exact smoothClosedSupportChartCoclassGerm_ne_zero X Y i m d w _ _ ⟨w, rfl⟩ h.symm

end SmoothPair

section Component

open AlgebraicGeometry ComplexPoint

variable (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
  (x : X.left) {p : ℕ} (hx : Order.coheight x = p)

/-- The normalized coclass section on the smooth locus of a cycle component is nonzero, given a
complex point of that smooth locus. -/
theorem cycleComponentSmoothClosedLiftCoclassSection_ne_zero
    (w : ComplexPoint (cycleComponentSmoothLocusOver X x)) :
    cycleComponentSmoothClosedLiftCoclassSection X x hx ≠ 0 := by
  let := cycleComponentSmoothLocusOver_hom_smoothOfRelativeDimension X x hx
  have hs := smoothClosedSupportCoclassSection_ne_zero
    (cycleComponentSmoothLocusAmbientOpenOver X x) (cycleComponentSmoothLocusOver X x)
    (cycleComponentSmoothLocusClosedLiftOver X x) (dim X.left - p) (dim X.left) w
  have key : ∀ (k : ℕ) (hk : k = p)
      (t : (𝓗_[Set.range (Point.map (cycleComponentSmoothLocusClosedLiftOver X x))]^(2 * k)
        (TopCat.of (ComplexPoint (cycleComponentSmoothLocusAmbientOpenOver X x)); ℚ)).presheaf.obj
          (op ⊤)), t ≠ 0 →
      (hk ▸ t : (𝓗_[Set.range (Point.map (cycleComponentSmoothLocusClosedLiftOver X x))]^(2 * p)
        (TopCat.of (ComplexPoint (cycleComponentSmoothLocusAmbientOpenOver X x)); ℚ)).presheaf.obj
          (op ⊤)) ≠ 0 := by
    intro k hk t ht
    subst hk
    exact ht
  exact key _ (cycleComponentSmoothClosedLift_codimension X x hx) _ hs

/-- The coclass section transported to `X(ℂ) \ Z_sing(ℂ)` is nonzero. -/
theorem cycleComponentSmoothSupportCoclassSection_ne_zero
    (w : ComplexPoint (cycleComponentSmoothLocusOver X x)) :
    cycleComponentSmoothSupportCoclassSection X x hx ≠ 0 :=
  supportRelativeCohomologySectionOnOpen_ne_zero _ _ _ _ _ _ _ _ _
    (cycleComponentSmoothClosedLiftCoclassSection_ne_zero X x hx w)

/-- The supported cycle class in `H^{2p}_{Z(ℂ)}(X(ℂ); ℚ)` is nonzero. -/
theorem cycleComponentSupportedInjectiveClass_ne_zero
    (w : ComplexPoint (cycleComponentSmoothLocusOver X x)) :
    cycleComponentSupportedInjectiveClass X x hx ≠ 0 := by
  intro h
  apply cycleComponentSmoothSupportCoclassSection_ne_zero X x hx w
  have := congrArg (cycleComponentSupportedClassNormalizationIso X x hx) h
  rw [map_zero] at this
  rw [← this]
  exact ((cycleComponentSupportedClassNormalizationIso X x hx).apply_symm_apply _).symm

/-- The smooth locus of a cycle component has a complex point. -/
theorem nonempty_complexPoint_cycleComponentSmoothLocusOver :
    Nonempty (ComplexPoint (cycleComponentSmoothLocusOver X x)) := by
  obtain ⟨z, hzA, hzClosed⟩ := (dense_cycleComponent_smooth_closedPoints X x).nonempty
  let A := (cycleComponentι X.left x ≫ X.hom).smoothLocus
  let zA : A.toScheme := ⟨z, hzA⟩
  have hzAClosed : IsClosed ({zA} : Set A) := by
    have he : A.ι ⁻¹' ({z} : Set (cycleComponent X.left x)) = {zA} := by
      ext a
      exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
    exact he ▸ hzClosed.preimage A.ι.continuous
  let q := (pointEquivClosedPoint (cycleComponentSmoothLocusOver X x).hom).symm ⟨zA, hzAClosed⟩
  exact ⟨Over.homMk q.1 q.2⟩

/-- The support of the generic point is all of `X(ℂ)`. -/
theorem cycleComponentAnalyticClosedSupport_genericPoint :
    cycleComponentAnalyticClosedSupport X (genericPoint X.left) = ⊤ := by
  ext y
  simp [cycleComponentAnalyticClosedSupport, cycleComponentSupport, genericPoint_closure]

/-- The cycle class of the generic point is nonzero. -/
theorem cycleComponentSheafClass_genericPoint_ne_zero
    (hη : Order.coheight (genericPoint X.left) = 0) :
    cycleComponentSheafClass X (genericPoint X.left) hη ≠ 0 := by
  obtain ⟨w⟩ := nonempty_complexPoint_cycleComponentSmoothLocusOver X (genericPoint X.left)
  intro h
  apply cycleComponentSupportedInjectiveClass_ne_zero X _ hη w
  apply forgetSupport_injective_of_eq_top ℚ X _
    (cycleComponentAnalyticClosedSupport_genericPoint X) (2 * 0)
  rw [map_zero]
  exact h

end Component

/-- In a vector space of rank at most one, any nonzero vector spans. -/
theorem span_singleton_eq_top_of_rank_le_one {K V : Type*} [DivisionRing K] [AddCommGroup V]
    [Module K V] (h : Module.rank K V ≤ 1) {c : V} (hc : c ≠ 0) :
    Submodule.span K {c} = ⊤ := by
  obtain ⟨v₀, hv₀⟩ := (rank_le_one_iff (K := K) (V := V)).mp h
  obtain ⟨r, rfl⟩ := hv₀ c
  have hr : r ≠ 0 := by rintro rfl; exact hc (zero_smul _ _)
  refine eq_top_iff.mpr fun v _ => ?_
  obtain ⟨s, rfl⟩ := hv₀ v
  rw [Submodule.mem_span_singleton]
  exact ⟨s * r⁻¹, by rw [smul_smul, mul_assoc, inv_mul_cancel₀ hr, mul_one]⟩

/-- With `X(ℂ)` preconnected, the codimension-zero cycle classes span all of `H^0(X(ℂ); ℚ)`. -/
theorem algebraicCycleClassSpan_zero_eq_top (hconn : ComplexPointsPreconnected)
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] :
    algebraicCycleClassSpan X 0 = ⊤ := by
  have := hconn.preconnected X
  have hη := coheight_genericPoint X.left
  refine eq_top_iff.mpr ?_
  rw [← span_singleton_eq_top_of_rank_le_one (rank_H0_le_one X)
    (cycleComponentSheafClass_genericPoint_ne_zero X hη)]
  exact le_sSup ⟨genericPoint X.left, hη, rfl⟩

/-- The degree-zero case of the Hodge conjecture.

Source: Deligne, *The Hodge Conjecture* (Clay), statement with p = 0.

Checks: F-1658 -/
@[hodge_milestone] theorem hodge_degree_zero (hconn : ComplexPointsPreconnected) :
    ∀ (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom],
      Hdg^0(X; ℚ) ≤ algebraicCycleClassSpan X 0 := by
  intro X _ _ _
  rw [algebraicCycleClassSpan_zero_eq_top hconn X]
  exact le_top

/-- The conclusion of `hodge_degree_zero` is the `p = 0` instance of `HodgeConjecture`. -/
example (h : HodgeConjecture) :
    ∀ (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom],
      Hdg^0(X; ℚ) ≤ algebraicCycleClassSpan X 0 :=
  fun X _ _ _ => h X 0

end HodgeLean.RealDefs
