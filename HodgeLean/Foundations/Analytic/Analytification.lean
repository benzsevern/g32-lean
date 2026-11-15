import HodgeLean.Foundations.Analytic.AnalytificationProofs

/-!
# Analytification of complex schemes (FROZEN SPEC)

Track F4 of the full-formalization program, prefixed `f4_`. It is the stage of the `spread` plan
(`docs/specs/CycleSpreading.md`) that turns finite-type complex schemes, the relative Hilbert
components of F6 in particular, into the reduced complex analytic spaces of F2 (`an_ReducedSpace`),
so that Remmert's theorem (F3, `an_remmert`) applies to them.

**The space.** For `X : Over (Spec ℂ)` the underlying space is `ComplexPoint X` with the upstream
analytic topology. The definitions (`AnalytificationDefs`) give algebraic charts
(`f4_RawChart`: an affine open, regular coordinates, polynomial equations), the atlas of all
admissible ones (`f4_atlas`) and the bundled space `f4_an`. The statements here:

* the charts: generating coordinates embed the points of an affine open
  (`f4_isEmbedding_of_generates`),
  the image of a presentation is the zero set of its equations (`f4_image_eq_of_isPresentation`),
  every affine open of a scheme locally of finite type has a presentation
  (`f4_exists_presentation`), so the admissible charts cover (`f4_covers`), and the atlas is
  analytic (`f4_atlas_isAnalytic`);
* the topology: Hausdorff for separated `X` (`f4_t2Space`) and second countable for
  quasi-compact `X` (`f4_secondCountable`); the analytification `f4_analytification X` of a
  separated scheme of finite type is built from these;
* degenerate cases: the cusp chart `(x², x³)` of `𝔸¹` embeds onto the cusp but is not generating
  (`f4_cuspChart_not_generates`), and some non-separated scheme of finite type (the line with a
  doubled origin) has a non-Hausdorff space of complex points (`f4_exists_not_t2Space`).

**Functoriality.** Regular functions are holomorphic (`f4_isHolFun_evaluate`); a morphism gives a
holomorphic map (`f4_map_isHom`), compatibly with composition (`Point.map_comp_apply`, by
definition); the complex points of a fibre product are the pairs agreeing in the base, with the
subspace topology of the product (`f4_pullbackPair_range`, `f4_pullbackPair_isEmbedding`); the
complex points of a Zariski closed subset are closed analytic (`f4_isClosedAnalytic_preimage`),
so a closed immersion lands onto a closed analytic subset (`f4_isClosedAnalytic_range`) whose
holomorphic functions are locally the restrictions of ambient ones
(`f4_closedImmersion_isHolFun_iff`).

**Properness.** `ℙᵈ_Y(ℂ) ≅ ℙᵈ(ℂ) × Y(ℂ)` (`f4_projOver_homeomorph`), so the projection is proper
(`f4_isProperMap_projToBase`) and so is every projective morphism
(`f4_isProperMap_of_isProjective`), the case Hilbert schemes need. For proper morphisms the route
is Chow's lemma (`f4_chow`), surjectivity on complex points (`f4_map_surjective`), and the
projective case (`f4_isProperMap_of_isProper`, `f4_isProperHom`).

**Comparisons.** For a scheme smooth of relative dimension `d`, the holomorphic functions and
maps agree with the `ContMDiff … ω` ones of the upstream charted space on `ComplexPoint X`, the
structure used by B2 and the abelian-variety files (`f4_isHolFun_iff_contMDiffOn`,
`f4_isHom_iff_contMDiff`). `𝔸ⁿ` is `ℂⁿ` (`f4_affineSpace_isHom`) and the node
`Spec ℂ[x, y]/(xy)` is `an_nodeSpace` (`f4_node_isHom`).

Not claimed: nonreduced analytic spaces (the structure sheaf of `f4_an` is the reduced one, so a
nonreduced scheme gives the space of its reduction), coherent sheaves and GAGA comparisons of
cohomology, the converse that a Hausdorff analytification forces separatedness, Zariski open
immersions, local dimension, or any statement about schemes not locally of finite type.
HC no distance; AV milestone no distance.
-/

noncomputable section

open Set Topology CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.ComplexPoint
open scoped ContDiff Manifold

namespace HodgeLean.Foundations.Analytic

/-! ### Charts -/

/-- **Generating coordinates embed.** If every regular function on the affine open `U` is, at the
complex points, a polynomial in the coordinates, the chart map is a topological embedding of the
complex points over `U` into `ℂⁿ`: the analytic topology over an affine open is that of pointwise
convergence of all regular functions, and the coordinates determine them all.
Source: Serre, *Géométrie algébrique et géométrie analytique*, Ann. Inst. Fourier 6 (1956), §2;
SGA 1, Exposé XII, §1; `Point.analyticTopology` (the topology over an affine open is induced by
evaluation of its regular functions). -/
theorem f4_isEmbedding_of_generates {X : Over (Spec ↧ℂ)} (r : f4_RawChart X)
    (hr : r.Generates) : IsEmbedding (r.dom.domRestrict r.toFun) :=
  f4_isEmbedding_of_generates_aux r hr

example (r : f4_RawChart f4_node) (hr : r.Generates) :
    IsEmbedding (r.dom.domRestrict r.toFun) :=
  f4_isEmbedding_of_generates r hr

/-- **The image of a presentation is its zero set.** For a scheme locally of finite type, the
complex points over `U`, read in a presentation, are exactly the common zeros of its equations
(Hilbert's Nullstellensatz: a polynomial vanishing at all points is nilpotent modulo the relations,
and the points of `Spec` of a finitely generated algebra are its `ℂ`-algebra maps to `ℂ`).
Source: Serre, GAGA, §2; Atiyah–Macdonald, *Introduction to Commutative Algebra*, Ch. 7,
Exercise 14 (Hilbert's Nullstellensatz); `affineSpecEquiv`. -/
theorem f4_image_eq_of_isPresentation {X : Over (Spec ↧ℂ)} [LocallyOfFiniteType X.hom]
    (r : f4_RawChart X) (hr : r.IsPresentation) :
    r.toFun '' r.dom = an_zeroLocus univ r.eqns :=
  f4_image_eq_of_isPresentation_aux r hr

example (r : f4_RawChart f4_node) (hr : r.IsPresentation) :
    r.toFun '' r.dom = an_zeroLocus univ r.eqns :=
  f4_image_eq_of_isPresentation r hr

/-- **Affine opens have presentations.** On an affine open of a scheme locally of finite type over
`ℂ` the regular functions form a finitely generated `ℂ`-algebra; generators are coordinates, and
the ideal of polynomials vanishing at the points is finitely generated.
Source: EGA I, §6.2 (locally of finite type: affine opens have finitely generated rings); Hilbert's
basis theorem (Atiyah–Macdonald, Theorem 7.5). -/
theorem f4_exists_presentation (X : Over (Spec ↧ℂ)) [LocallyOfFiniteType X.hom]
    (U : X.left.affineOpens) : ∃ r : f4_RawChart X, r.U = U ∧ r.IsPresentation :=
  f4_exists_presentation_aux X U

example (U : f4_node.left.affineOpens) : ∃ r : f4_RawChart f4_node, r.U = U ∧ r.IsPresentation :=
  f4_exists_presentation f4_node U

/-- **The admissible charts cover.** Every complex point lies in an affine open, whose presentation
is admissible (`f4_isEmbedding_of_generates`, `f4_image_eq_of_isPresentation`,
`f4_exists_presentation`).
Source: SGA 1, Exposé XII, §1; Serre, GAGA, §2. -/
theorem f4_covers (X : Over (Spec ↧ℂ)) [LocallyOfFiniteType X.hom] :
    ∀ z : ComplexPoint X, ∃ r : f4_AdmChart X, z ∈ r.1.dom :=
  f4_covers_aux X

example (z : ComplexPoint (f4_affineSpace 2)) : ∃ r : f4_AdmChart (f4_affineSpace 2), z ∈ r.1.dom :=
  f4_covers _ z

/-- **The algebraic atlas is analytic.** A coordinate of one chart is, near a point of the overlap,
on a principal open `D(g)` of the other chart's affine open, a quotient `c / gᵐ` of regular
functions, hence a quotient of polynomials in the other chart's coordinates with nonvanishing
denominator: holomorphic. Generation is what makes this work (`f4_cuspChart_not_generates`).
Source: Serre, GAGA, §2 (the analytic structure does not depend on the affine embedding);
`Point.exists_evaluate_basicOpen_eq_div` (regular functions on a principal open as quotients). -/
theorem f4_atlas_isAnalytic (X : Over (Spec ↧ℂ))
    (h : ∀ z : ComplexPoint X, ∃ r : f4_AdmChart X, z ∈ r.1.dom) :
    (f4_atlas X h).IsAnalytic :=
  f4_atlas_isAnalytic_aux X h

example : (f4_atlas f4_node (f4_covers _)).IsAnalytic := f4_atlas_isAnalytic _ _

/-- **Separated schemes have Hausdorff analytifications.** The diagonal of a separated scheme is a
closed immersion, so its complex points form a closed subset of `(X ×_ℂ X)(ℂ)`, which is
`X(ℂ) × X(ℂ)` (`f4_pullbackPair_isEmbedding`); a space with closed diagonal is Hausdorff.
Source: SGA 1, Exposé XII, Proposition 3.1 (`f` separated implies `f^an` separated);
`ComplexPoint.isClosedEmbedding_map_of_closedImmersion`. -/
theorem f4_t2Space (X : Over (Spec ↧ℂ)) [LocallyOfFiniteType X.hom] [IsSeparated X.hom] :
    T2Space (ComplexPoint X) :=
  f4_t2Space_aux X

example : T2Space (ComplexPoint f4_node) := f4_t2Space _

/-- **Quasi-compact schemes have second-countable analytifications.** Finitely many affine opens
cover, the complex points over each are an open subspace embedded in some `ℂⁿ`
(`f4_isEmbedding_of_generates`), and a finite union of open second-countable subspaces is second
countable.
Source: SGA 1, Exposé XII, §1; Bourbaki, *Topologie générale*, Ch. IX, §2.8. -/
theorem f4_secondCountable (X : Over (Spec ↧ℂ)) [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] : SecondCountableTopology (ComplexPoint X) :=
  f4_secondCountable_aux X

example : SecondCountableTopology (ComplexPoint (f4_projectiveSpace 2)) := f4_secondCountable _

/-- The analytification of a separated scheme of finite type over `ℂ`: the complex points with the
analytic topology and the atlas of admissible algebraic charts, as a reduced complex analytic
space. Every field comes from a theorem above.
Source: Serre, GAGA, §2; SGA 1, Exposé XII, §1; Grauert–Remmert, *Coherent Analytic Sheaves*,
§1.1.5. -/
abbrev f4_analytification (X : Over (Spec ↧ℂ)) [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [IsSeparated X.hom] : an_ReducedSpace (ComplexPoint X) :=
  f4_an X (f4_covers X) (f4_t2Space X) (f4_secondCountable X)
    (f4_atlas_isAnalytic X (f4_covers X))

example : (f4_analytification f4_node).atlas = f4_atlas f4_node (f4_covers _) := rfl

/-- **The cusp chart is not generating.** The chart `z ↦ (z², z³)` of `𝔸¹` is an embedding onto the
cusp `{w₁³ = w₂²}`, but `x` is not a polynomial in `x²` and `x³` (a polynomial in them has no
linear term), so it is not admissible: with it the atlas would not be analytic, since `x = w₂/w₁`
is not the restriction of a holomorphic function near the cusp point.
Source: Hartshorne, *Algebraic Geometry*, Ch. I, Exercise 3.2 (the cusp and its normalization). -/
theorem f4_cuspChart_not_generates :
    IsEmbedding (f4_cuspChart.dom.domRestrict f4_cuspChart.toFun) ∧
      f4_cuspChart.toFun '' f4_cuspChart.dom = an_zeroLocus univ f4_cuspChart.eqns ∧
      ¬ f4_cuspChart.Generates :=
  f4_cuspChart_not_generates_aux

example : ¬ f4_cuspChart.IsAdmissible := fun h ↦ f4_cuspChart_not_generates.2.2 h.1

/-- **Separatedness is needed.** The affine line with a doubled origin is of finite type over `ℂ`
and not separated, and its two origins have no disjoint neighbourhoods in the analytic topology.
Source: Hartshorne, *Algebraic Geometry*, Ch. II, Example 4.0.1 (the line with a doubled origin);
SGA 1, Exposé XII, Proposition 3.1. -/
theorem f4_exists_not_t2Space :
    ∃ X : Over (Spec ↧ℂ), LocallyOfFiniteType X.hom ∧ QuasiCompact X.hom ∧
      ¬ IsSeparated X.hom ∧ ¬ T2Space (ComplexPoint X) :=
  f4_exists_not_t2Space_aux

example : ∃ X : Over (Spec ↧ℂ), ¬ T2Space (ComplexPoint X) :=
  let ⟨X, _, _, _, h⟩ := f4_exists_not_t2Space
  ⟨X, h⟩

/-! ### Functions and maps -/

/-- **Regular functions are holomorphic.** On the complex points over a Zariski open `U`, a regular
function on `U` is a section of the structure sheaf: in each chart, near each point, it is a
quotient of polynomials in the coordinates with nonvanishing denominator.
Source: Serre, GAGA, §2 (the structure sheaf of `X^an` contains the regular functions);
`Point.exists_evaluate_basicOpen_eq_div`. -/
theorem f4_isHolFun_evaluate (X : Over (Spec ↧ℂ)) [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] [IsSeparated X.hom] (U : X.left.Opens) (s : Γ(X.left, U)) :
    (f4_analytification X).IsHolFun
      (fun z : (Point.overOpen U : Set (ComplexPoint X)) ↦
        Point.evaluate U s (z : ComplexPoint X)) :=
  f4_isHolFun_evaluate_aux X _ _ _ _ U s

example (s : Γ(f4_node.left, ⊤)) :
    (f4_analytification f4_node).IsHolFun
      (fun z : (Point.overOpen ⊤ : Set (ComplexPoint f4_node)) ↦
        Point.evaluate ⊤ s (z : ComplexPoint f4_node)) :=
  f4_isHolFun_evaluate _ ⊤ s

/-- **Morphisms are holomorphic.** The map of complex points of a morphism of separated schemes
of finite type is holomorphic: it is continuous (`Point.continuous_map`), and composed with a chart
of the target it is given by the pulled-back regular coordinates, holomorphic by
`f4_isHolFun_evaluate` (then `an_isHom_iff_chart`).
Source: Serre, GAGA, §2 (a morphism `f` gives a holomorphic `f^an`); SGA 1, Exposé XII, §1. -/
theorem f4_map_isHom {X Y : Over (Spec ↧ℂ)} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [IsSeparated X.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (f : X ⟶ Y) :
    an_IsHom (f4_analytification X) (f4_analytification Y) (Point.map f) :=
  f4_map_isHom_aux _ _ _ _ _ _ _ _ f

example : an_IsHom (f4_analytification f4_node) (f4_analytification f4_point)
    (Point.map (f4_toPoint f4_node)) :=
  f4_map_isHom _

/-- Compatibility with composition holds by definition. -/
example {X Y Z : Over (Spec ↧ℂ)} (f : X ⟶ Y) (g : Y ⟶ Z) :
    Point.map (f ≫ g) = Point.map g ∘ Point.map f :=
  funext (Point.map_comp_apply f g)

/-! ### Fibre products -/

/-- **Points of a fibre product.** The complex points of `X ×_Y Z` are the pairs of complex points
of `X` and `Z` with the same image in `Y`: a complex point is a morphism from the point, and
these are classified by the universal property.
Source: EGA I, §3.4 (points of a fibre product with values in a scheme); SGA 1, Exposé XII, §1. -/
theorem f4_pullbackPair_range {X Y Z : Over (Spec ↧ℂ)} (f : X ⟶ Y) (g : Z ⟶ Y) :
    range (f4_pullbackPair f g) = {p | Point.map f p.1 = Point.map g p.2} :=
  f4_pullbackPair_range_aux f g

example : range (f4_pullbackPair (f4_toPoint f4_node) (f4_toPoint (f4_affineSpace 1))) =
    {p | Point.map (f4_toPoint f4_node) p.1 = Point.map (f4_toPoint (f4_affineSpace 1)) p.2} :=
  f4_pullbackPair_range _ _

/-- **The topology of a fibre product.** The map to pairs is a topological embedding into the
product: over affine opens `U ×_W V` the regular functions are sums of products `a ⊗ b`, so the
analytic topology is that of the product.
Source: SGA 1, Exposé XII, §1 (`(X ×_Y Z)^an = X^an ×_{Y^an} Z^an`); Serre, GAGA, §2. -/
theorem f4_pullbackPair_isEmbedding {X Y Z : Over (Spec ↧ℂ)} [LocallyOfFiniteType X.hom]
    [LocallyOfFiniteType Y.hom] [LocallyOfFiniteType Z.hom] (f : X ⟶ Y) (g : Z ⟶ Y) :
    IsEmbedding (f4_pullbackPair f g) :=
  f4_pullbackPair_isEmbedding_aux f g

example : IsEmbedding (f4_pullbackPair (f4_toPoint f4_node) (f4_toPoint (f4_affineSpace 1))) :=
  f4_pullbackPair_isEmbedding _ _

/-! ### Closed subschemes -/

/-- **Zariski closed sets are closed analytic.** The complex points lying over a closed subset of
`X` form a closed analytic subset: on an affine open it is the zero set of finitely many regular
functions (the ring is Noetherian), holomorphic by `f4_isHolFun_evaluate`.
Source: Serre, GAGA, §2 (algebraic subsets are analytic); SGA 1, Exposé XII, §1. -/
theorem f4_isClosedAnalytic_preimage (X : Over (Spec ↧ℂ)) [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] [IsSeparated X.hom] (Z : Set X.left) (hZ : IsClosed Z) :
    an_IsClosedAnalytic (f4_analytification X) (Point.underlying ⁻¹' Z) :=
  f4_isClosedAnalytic_preimage_aux X _ _ _ _ Z hZ

example (Z : Set f4_node.left) (hZ : IsClosed Z) :
    an_IsClosedAnalytic (f4_analytification f4_node) (Point.underlying ⁻¹' Z) :=
  f4_isClosedAnalytic_preimage _ Z hZ

/-- **Closed immersions land onto closed analytic subsets.** The image of the complex points of a
closed immersion is the set of points over its closed image
(`ComplexPoint.range_map_of_closedImmersion`), closed analytic by
`f4_isClosedAnalytic_preimage`. The map is a closed embedding
(`ComplexPoint.isClosedEmbedding_map_of_closedImmersion`).
Source: Serre, GAGA, §2; SGA 1, Exposé XII, §1 (closed immersions go to closed embeddings onto
closed analytic subspaces). -/
theorem f4_isClosedAnalytic_range {Z X : Over (Spec ↧ℂ)} [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] [IsSeparated X.hom] (i : Z ⟶ X) [IsClosedImmersion i.left] :
    an_IsClosedAnalytic (f4_analytification X) (range (Point.map i)) :=
  f4_isClosedAnalytic_range_aux _ _ _ _ i

example : an_IsClosedAnalytic (f4_analytification f4_node) (range (Point.map (𝟙 f4_node))) :=
  f4_isClosedAnalytic_range (𝟙 f4_node)

/-- **The reduced closed subspace structure.** For a closed immersion `i : Z → X`, a function on an
open set of `Z(ℂ)` is holomorphic exactly when near each point it is the restriction, along `i`, of
a holomorphic function on an open set of `X(ℂ)`. So `Z^an` is the closed analytic subset
`i(Z(ℂ))` with its reduced structure.
Source: Serre, GAGA, §2; Grauert–Remmert, *Coherent Analytic Sheaves*, §1.1.6 and §4.1 (the
reduced closed subspace, whose functions are locally restrictions of ambient ones). -/
theorem f4_closedImmersion_isHolFun_iff {Z X : Over (Spec ↧ℂ)} [LocallyOfFiniteType Z.hom]
    [QuasiCompact Z.hom] [IsSeparated Z.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [IsSeparated X.hom] (i : Z ⟶ X) [IsClosedImmersion i.left] {W : Set (ComplexPoint Z)}
    (hW : IsOpen W) (g : W → ℂ) :
    (f4_analytification Z).IsHolFun g ↔
      ∀ w : W, ∃ V : Set (ComplexPoint X), IsOpen V ∧ Point.map i w ∈ V ∧
        ∃ G : V → ℂ, (f4_analytification X).IsHolFun G ∧
          ∀ w' : W, ∀ h : Point.map i w' ∈ V, g w' = G ⟨Point.map i w', h⟩ :=
  f4_closedImmersion_isHolFun_iff_aux _ _ _ _ _ _ _ _ i hW g

example (g : ↥(univ : Set (ComplexPoint f4_node)) → ℂ) :
    (f4_analytification f4_node).IsHolFun g ↔
      ∀ w : ↥(univ : Set (ComplexPoint f4_node)), ∃ V : Set (ComplexPoint f4_node), IsOpen V ∧
        Point.map (𝟙 f4_node) w ∈ V ∧ ∃ G : V → ℂ, (f4_analytification f4_node).IsHolFun G ∧
          ∀ w' : ↥(univ : Set (ComplexPoint f4_node)), ∀ h : Point.map (𝟙 f4_node) w' ∈ V,
            g w' = G ⟨Point.map (𝟙 f4_node) w', h⟩ :=
  f4_closedImmersion_isHolFun_iff (𝟙 f4_node) isOpen_univ g

/-! ### Properness -/

/-- **Projective space over a base.** The complex points of `ℙᵈ_Y = ℙᵈ_ℤ ×_ℤ Y` are homeomorphic
to `ℙᵈ(ℂ) × Y(ℂ)`, compatibly with the projection to `Y(ℂ)`: over a standard chart `D₊(xᵢ)` and an
affine open of `Y` the ring is `Γ(W)[x/xᵢ]`, whose points are pairs with the product topology.
Source: Hartshorne, *Algebraic Geometry*, Ch. II, §7 (`ℙⁿ_Y = ℙⁿ_ℤ ×_ℤ Y`); SGA 1, Exposé XII,
§1 (analytification commutes with fibre products). -/
theorem f4_projOver_homeomorph (Y : Over (Spec ↧ℂ)) (d : ℕ) :
    ∃ e : ComplexPoint (f4_projOver Y d) ≃ₜ ComplexPoint (f4_projectiveSpace d) × ComplexPoint Y,
      ∀ z, (e z).2 = Point.map (f4_projToBase Y d) z :=
  f4_projOver_homeomorph_aux Y d

example : ∃ e : ComplexPoint (f4_projOver f4_node 1) ≃ₜ
      ComplexPoint (f4_projectiveSpace 1) × ComplexPoint f4_node,
      ∀ z, (e z).2 = Point.map (f4_projToBase f4_node 1) z :=
  f4_projOver_homeomorph _ _

/-- **The projection from projective space is proper.** By `f4_projOver_homeomorph` it is the
projection `ℙᵈ(ℂ) × Y(ℂ) → Y(ℂ)`, and `ℙᵈ(ℂ)` is compact
(`ComplexProjectiveSpace.instCompactSpaceProjectiveSpaceComplexPoint`).
Source: Serre, GAGA, §2 (`ℙⁿ(ℂ)` is compact); `isProperMap_snd_of_compactSpace`. -/
theorem f4_isProperMap_projToBase (Y : Over (Spec ↧ℂ)) (d : ℕ) :
    IsProperMap (Point.map (f4_projToBase Y d)) :=
  f4_isProperMap_projToBase_aux Y d

example : IsProperMap (Point.map (f4_projToBase f4_node 2)) := f4_isProperMap_projToBase _ _

/-- **Projective morphisms give proper maps.** A projective morphism factors as a closed immersion
into `ℙᵈ_Y` followed by the projection; the first gives a closed embedding
(`ComplexPoint.isClosedEmbedding_map_of_closedImmersion`), the second a proper map
(`f4_isProperMap_projToBase`). This is the case the relative Hilbert schemes need.
Source: Serre, GAGA, §2; SGA 1, Exposé XII, Proposition 3.2 (`f` proper implies `f^an` proper),
projective case. -/
theorem f4_isProperMap_of_isProjective {X Y : Over (Spec ↧ℂ)} (f : X ⟶ Y)
    [IsProjective f.left] : IsProperMap (Point.map f) :=
  f4_isProperMap_of_isProjective_aux f

example (d : ℕ) : IsProperMap (Point.map (f4_toPoint (f4_projectiveSpace d))) :=
  f4_isProperMap_of_isProjective _

/-- **Chow's lemma.** For a proper morphism `f : X → Y` of separated schemes of finite type over
`ℂ`, there is a surjective morphism `π : X' → X` with `X'` of finite type and `π ≫ f` projective
(a closed immersion into some `ℙᵈ_Y` over `Y`).
Source: EGA II, Théorème 5.6.1 (Chow's lemma); Hartshorne, *Algebraic Geometry*, Ch. II,
Exercise 4.10 (in the form used here: `X'` projective over the Noetherian base, `π` an isomorphism
over a dense open, hence surjective). -/
theorem f4_chow {X Y : Over (Spec ↧ℂ)} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [IsSeparated X.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (f : X ⟶ Y) [IsProper f.left] :
    ∃ (X' : Over (Spec ↧ℂ)) (π : X' ⟶ X), LocallyOfFiniteType X'.hom ∧
      IsProjective (π ≫ f).left ∧ Surjective π.left :=
  f4_chow_aux f

example : ∃ (X' : Over (Spec ↧ℂ)) (π : X' ⟶ f4_projectiveSpace 1), LocallyOfFiniteType X'.hom ∧
    IsProjective (π ≫ f4_toPoint (f4_projectiveSpace 1)).left ∧ Surjective π.left :=
  f4_chow _

/-- **Surjective morphisms are surjective on complex points.** If `π : X' → X` is surjective and
`X'` is locally of finite type over `ℂ`, the fibre over the point under a complex point of `X` is a
nonempty scheme of finite type over `ℂ`, which has a complex point (Nullstellensatz).
Source: EGA IV, Corollaire 10.4.7 (closed points of schemes of finite type over a field have
finite residue fields); Atiyah–Macdonald, Ch. 7, Exercise 14. -/
theorem f4_map_surjective {X' X : Over (Spec ↧ℂ)} [LocallyOfFiniteType X'.hom]
    (π : X' ⟶ X) [Surjective π.left] : Function.Surjective (Point.map π) :=
  f4_map_surjective_aux π

example : Function.Surjective (Point.map (f4_toPoint f4_node)) :=
  f4_map_surjective _

/-- **Proper morphisms give proper maps.** With `π` from Chow's lemma (`f4_chow`), `Point.map f ∘
Point.map π` is the map of the projective `π ≫ f`, proper by `f4_isProperMap_of_isProjective`;
`Point.map π` is continuous and surjective (`f4_map_surjective`), so `Point.map f` is proper
(`isProperMap_of_comp_of_surj`).
Source: SGA 1, Exposé XII, Proposition 3.2 (`f` proper implies `f^an` proper, via Chow's lemma);
Serre, GAGA, §2. -/
theorem f4_isProperMap_of_isProper {X Y : Over (Spec ↧ℂ)} [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    [IsSeparated Y.hom] (f : X ⟶ Y) [IsProper f.left] : IsProperMap (Point.map f) :=
  f4_isProperMap_of_isProper_aux f

example : IsProperMap (Point.map (f4_toPoint (f4_projectiveSpace 1))) :=
  f4_isProperMap_of_isProper _

/-- **Proper morphisms give proper holomorphic maps**, the form in which Remmert's theorem
(`an_remmert`) applies: `f4_isProperMap_of_isProper` and `f4_map_isHom`.
Source: SGA 1, Exposé XII, Proposition 3.2; Serre, GAGA, §2. -/
theorem f4_isProperHom {X Y : Over (Spec ↧ℂ)} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [IsSeparated X.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (f : X ⟶ Y) [IsProper f.left] :
    an_IsProperHom (f4_analytification X) (f4_analytification Y) (Point.map f) :=
  f4_isProperHom_aux _ _ _ _ _ _ _ _ f

example (d : ℕ) : an_IsProperHom (f4_analytification (f4_projectiveSpace d))
    (f4_analytification f4_point) (Point.map (f4_toPoint (f4_projectiveSpace d))) :=
  f4_isProperHom _

/-! ### Comparison with the manifold structure of smooth schemes -/

/-- **Holomorphic functions on smooth schemes.** For `X` smooth of relative dimension `d`, a
function on an open set of `X(ℂ)` is a section of the structure sheaf of the analytification
exactly when it is `ContMDiffOn … ω` for the upstream étale-coordinate charts on `ComplexPoint X`
(`ComplexPoint.localChart`, the charted space of `ComplexPoint.holomorphicFunctionSheaf`, B2
and the abelian-variety files). The étale coordinates are regular functions, a local analytic
isomorphism onto open subsets of `ℂᵈ`, and they are holomorphic in the algebraic charts and
conversely.
Source: SGA 1, Exposé XII, Proposition 3.1 (`f` smooth iff `f^an` smooth); Serre, GAGA, §2
(nonsingular varieties give complex manifolds). -/
theorem f4_isHolFun_iff_contMDiffOn (X : Over (Spec ↧ℂ)) (d : ℕ)
    [SmoothOfRelativeDimension d X.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [IsSeparated X.hom] (g : ComplexPoint X → ℂ) {U : Set (ComplexPoint X)} (hU : IsOpen U) :
    (f4_analytification X).IsHolFun (fun x : U ↦ g x) ↔
      ContMDiffOn 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, ℂ) ω g U :=
  f4_isHolFun_iff_contMDiffOn_aux X d _ _ _ _ g hU

example (X : Over (Spec ↧ℂ)) (d : ℕ) [SmoothOfRelativeDimension d X.hom]
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] :
    (f4_analytification X).IsHolFun (fun _ : (univ : Set (ComplexPoint X)) ↦ (1 : ℂ)) :=
  (f4_isHolFun_iff_contMDiffOn X d (fun _ ↦ 1) isOpen_univ).2 contMDiffOn_const

/-- **Holomorphic maps of smooth schemes.** A map between the complex points of smooth schemes is
holomorphic for the analytifications exactly when it is `ContMDiff … ω` for the upstream charted
spaces.
Source: SGA 1, Exposé XII, Proposition 3.1; Serre, GAGA, §2. -/
theorem f4_isHom_iff_contMDiff {X Y : Over (Spec ↧ℂ)} {d e : ℕ}
    [SmoothOfRelativeDimension d X.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [IsSeparated X.hom] [SmoothOfRelativeDimension e Y.hom] [LocallyOfFiniteType Y.hom]
    [QuasiCompact Y.hom] [IsSeparated Y.hom] (F : ComplexPoint X → ComplexPoint Y) :
    an_IsHom (f4_analytification X) (f4_analytification Y) F ↔
      ContMDiff 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, Fin e → ℂ) ω F :=
  f4_isHom_iff_contMDiff_aux _ _ _ _ _ _ _ _ F

example (X : Over (Spec ↧ℂ)) (d : ℕ) [SmoothOfRelativeDimension d X.hom]
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] :
    an_IsHom (f4_analytification X) (f4_analytification X) id :=
  (f4_isHom_iff_contMDiff (d := d) (e := d) id).2 contMDiff_id

/-! ### Instances -/

/-- **`𝔸ⁿ` is `ℂⁿ`.** The coordinate bijection `affineSpaceEquiv` of the complex points of `𝔸ⁿ`
with `ℂⁿ` is holomorphic in both directions.
Source: Serre, GAGA, §2 (`(𝔸ⁿ)^an = ℂⁿ`); `ComplexPoint.affineSpaceHomeomorph`. -/
theorem f4_affineSpace_isHom (n : ℕ) :
    an_IsHom (f4_analytification (f4_affineSpace n)) (an_euclidSpace n)
        (affineSpaceEquiv (Fin n)) ∧
      an_IsHom (an_euclidSpace n) (f4_analytification (f4_affineSpace n))
        (affineSpaceEquiv (Fin n)).symm :=
  f4_affineSpace_isHom_aux n _ _ _ _

example : an_IsHom (an_euclidSpace 2) (f4_analytification (f4_affineSpace 2))
    (affineSpaceEquiv (Fin 2)).symm :=
  (f4_affineSpace_isHom 2).2

/-- **The node.** The coordinates `(x, y)` identify the complex points of `Spec ℂ[x, y]/(xy)` with
the local model `an_node = {z₀ z₁ = 0} ⊆ ℂ²`, holomorphically in both directions: the
analytification of the node is the singular space `an_nodeSpace`.
Source: Serre, GAGA, §2; Hartshorne, *Algebraic Geometry*, Ch. I, Exercise 5.6. -/
theorem f4_node_isHom :
    an_IsHom (f4_analytification f4_node) an_nodeSpace f4_nodeEquiv ∧
      an_IsHom an_nodeSpace (f4_analytification f4_node) f4_nodeEquiv.symm :=
  f4_node_isHom_aux _ _ _ _

example : an_IsHom (f4_analytification f4_node) an_nodeSpace f4_nodeCoord := f4_node_isHom.1

end HodgeLean.Foundations.Analytic
