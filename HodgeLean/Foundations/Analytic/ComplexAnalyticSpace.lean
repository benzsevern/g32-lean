import HodgeLean.Foundations.Analytic.ComplexAnalyticSpaceProofs

/-!
# Reduced complex analytic spaces and Remmert's proper mapping theorem (FROZEN SPEC)

Tracks F2 and F3 of the full-formalization program, prefixed `an_`.

**F2 (reduced complex analytic spaces).** The definitions are in `ComplexAnalyticSpaceDefs`: local
models `an_zeroLocus U f` with the reduced ideal `an_reducedIdeal` and the model sheaf
`an_structureSheaf` of local restrictions of holomorphic functions; charts onto local models and
analytic atlases; the reduced complex analytic space `an_ReducedSpace X` (Hausdorff,
second-countable, with an analytic atlas) and its structure sheaf of commutative rings
`an_ReducedSpace.structureSheaf`, glued from the charts, with the evaluation `evalStalk` on
stalks; holomorphic maps (pulling holomorphic functions back to holomorphic functions), proper
holomorphic maps, closed analytic subsets (locally the common zeros of finitely many sections),
and the local dimension (`an_dimAt`, Krull) and geometric dimension (`an_geomDim`, manifold
points). The statements here:

* the local model: restriction to `Z` has kernel the reduced ideal, which is radical, and lands in
  the model sheaf (`an_restrict_ker`, `an_reducedIdeal_isRadical`, `an_restrict_isLocRestr`);
* the structure sheaf: its sections are continuous, on a chart domain they are the sections of the
  model sheaf (`an_isHolFun_continuous`, `an_chart_restrict`), its stalks are local rings whose
  maximal ideal is the germs vanishing at the point (`an_structureSheaf_isLocal`), and holomorphic
  maps are the maps holomorphic in the charts (`an_isHom_iff_chart`);
* complex manifolds: `an_manifoldSpace E M` is a reduced complex analytic space (its atlas is
  analytic: `an_manifoldAtlas_isAnalytic`, in the definitions file), and its holomorphic functions,
  holomorphic maps and closed analytic subsets agree with `ContMDiffOn … ω`, `ContMDiff … ω` and
  the repository's `IsClosedAnalytic` (`an_manifold_isHolFun_iff`, `an_manifold_isHom_iff`,
  `an_manifold_isClosedAnalytic_iff`), with dimension `dim_ℂ E` (`an_manifold_dim`);
* a closed analytic subset is a closed analytic subspace with the universal property of the
  reduced structure (`an_closedSubspace`);
* dimension: the Krull dimension does not depend on the chart (`an_dimAt_eq_chart`), is the Krull
  dimension of the stalk of the structure sheaf (`an_dim_eq_stalk`), and equals the geometric
  dimension (`an_dimAt_eq_geomDim`); `ℂⁿ` has dimension `n` and the node dimension `1` at its
  singular point (`an_dim_euclid`, `an_dim_node`).

**F3 (Remmert's proper mapping theorem), stated with its intermediate steps.** The route is the
classical one by induction on dimension (Remmert 1957; Narasimhan, *Introduction to the Theory of
Analytic Spaces*, LNM 25, Ch. VII; Chirka, *Complex Analytic Sets*, §§3–4):

* locality and finiteness: closed analyticity is local on the target, reduced spaces are locally
  compact, local dimension is bounded on compacta (`an_isClosedAnalytic_of_locally`,
  `an_locallyCompactSpace`, `an_dimAt_bounded`);
* the finite case: the proper projection of a closed analytic set with finite fibres, by
  Weierstrass theory and canonical defining functions, and the finite mapping theorem
  (`an_finite_projection`, `an_finite_mapping`);
* the rank and dimension stratification: the Cartan–Remmert fibre-dimension loci and the
  constant rank theorem (`an_cartan_remmert`, `an_constant_rank`);
* Remmert–Stein extension of a pure-dimensional analytic set across a smaller-dimensional one
  (`an_remmert_stein`);
* induction on dimension, locally over the target (`an_remmert_local_zero`,
  `an_remmert_local_succ`);
* the theorem (`an_remmert`), the hyperbola showing properness is needed
  (`an_remmert_not_proper`), and the manifold case in exactly the shape of `f1_remmert`
  (`an_remmert_manifold`).

Not claimed: coherence of the structure sheaf (Oka–Cartan), Grauert's direct image theorem,
nonreduced spaces, normalization, or any analytic statement about an atlas that is not analytic.
HC no distance; AV milestone no distance.
-/

noncomputable section

open Set Filter Topology TopologicalSpace
open scoped ContDiff Manifold

namespace HodgeLean.Foundations.Analytic

open HodgeLean.Foundations

universe u v w

/-! ### F2: local models -/

/-- **The quotient `𝒪_U / I_Z` embeds in the functions on `Z`.** The kernel of restriction to `Z`
is the reduced ideal of all holomorphic functions vanishing on `Z`.
Source: Grauert–Remmert, *Coherent Analytic Sheaves*, §4.1 (the reduction
`(A, 𝒪_D/𝒥(A))` of a model space). -/
theorem an_restrict_ker {n : ℕ} (U Z : Set (Fin n → ℂ)) (h : Z ⊆ U) :
    RingHom.ker (an_restrict U Z h) = an_reducedIdeal U Z :=
  an_restrict_ker_aux U Z h

example : RingHom.ker (an_restrict univ an_node (subset_univ _)) =
    an_reducedIdeal univ an_node :=
  an_restrict_ker _ _ _

/-- **The reduced ideal is radical.** A holomorphic function some power of which vanishes on `Z`
vanishes on `Z`.
Source: Grauert–Remmert, *Coherent Analytic Sheaves*, §4.1 (`𝒥(A)` is the full ideal of `A`,
hence reduced). -/
theorem an_reducedIdeal_isRadical {n : ℕ} (U Z : Set (Fin n → ℂ)) :
    (an_reducedIdeal U Z).IsRadical :=
  an_reducedIdeal_isRadical_aux U Z

example : (an_reducedIdeal univ an_node).IsRadical := an_reducedIdeal_isRadical _ _

/-- **Restrictions are sections of the model sheaf.** The restriction to `Z` of a function
holomorphic on an open `U ⊇ Z` is locally a restriction of a holomorphic function.
Source: Grauert–Remmert, *Coherent Analytic Sheaves*, §4.1. -/
theorem an_restrict_isLocRestr {n : ℕ} (U Z : Set (Fin n → ℂ)) (hU : IsOpen U)
    (h : Z ⊆ U) (g : an_holRing U) :
    an_IsLocRestr Z (S := univ) (fun x ↦ an_restrict U Z h g x.1) :=
  an_restrict_isLocRestr_aux U Z hU h g

example (g : an_holRing (univ : Set (Fin 2 → ℂ))) :
    an_IsLocRestr an_node (S := univ) (fun x ↦ an_restrict univ an_node (subset_univ _) g x.1) :=
  an_restrict_isLocRestr _ _ isOpen_univ _ g

/-! ### F2: the structure sheaf -/

/-- **Sections of the structure sheaf are continuous.** A holomorphic function on `U ⊆ X` is
continuous: near each point it is a holomorphic function composed with a chart.
Source: Grauert–Remmert, *Coherent Analytic Sheaves*, §4.1 (the structure sheaf of a reduced space
is a subsheaf of the sheaf of continuous functions). -/
theorem an_isHolFun_continuous {X : Type u} [TopologicalSpace X] (S : an_ReducedSpace X)
    {U : Set X} {g : U → ℂ} (hg : S.IsHolFun g) : Continuous g :=
  an_isHolFun_continuous_aux S hg

example (U : Set an_node) (g : U → ℂ) (hg : an_nodeSpace.IsHolFun g) : Continuous g :=
  an_isHolFun_continuous an_nodeSpace hg

/-- **On a chart domain the structure sheaf is the model sheaf.** A function on `U ⊆ dom` is a
section of the structure sheaf exactly when, read on the image of `U` in the local model, it is
locally a restriction of holomorphic functions (`an_IsLocRestr`, the predicate of
`an_structureSheaf`). The other charts impose nothing more, because the transitions are
holomorphic.
Source: Grauert–Remmert, *Coherent Analytic Sheaves*, §1.1.5 (a chart is an isomorphism of ringed
spaces onto a model space) and §4.1 (the structure sheaf of a reduced model space). -/
theorem an_chart_restrict {X : Type u} [TopologicalSpace X] (S : an_ReducedSpace X)
    (i : S.atlas.ι) {U : Set X} (hU : U ⊆ (S.atlas.chart i).dom) (g : U → ℂ) :
    S.IsHolFun g ↔ ∃ h : (S.atlas.chart i).modelImage U → ℂ,
      an_IsLocRestr (an_zeroLocus (S.atlas.chart i).U (S.atlas.chart i).eqns) h ∧
        ∀ x : U, g x = h ((S.atlas.chart i).toModelImage hU x) :=
  an_chart_restrict_aux S i hU g

example (g : ↥(univ : Set an_node) → ℂ) :
    an_nodeSpace.IsHolFun g ↔ ∃ h : (an_nodeSpace.atlas.chart ⟨⟩).modelImage univ → ℂ,
      an_IsLocRestr (an_zeroLocus (an_nodeSpace.atlas.chart ⟨⟩).U
        (an_nodeSpace.atlas.chart ⟨⟩).eqns) h ∧
        ∀ x : ↥(univ : Set an_node), g x = h ((an_nodeSpace.atlas.chart ⟨⟩).toModelImage
          (fun _ _ ↦ mem_univ _) x) :=
  an_chart_restrict an_nodeSpace ⟨⟩ (fun _ _ ↦ mem_univ _) g

/-- **The stalks are local rings.** The stalk `𝒪_{X,x}` of the structure sheaf is a local ring,
and its non-units, the maximal ideal, are the germs vanishing at `x`: a germ not vanishing at `x`
is invertible near `x`.
Source: Grauert–Remmert, *Coherent Analytic Sheaves*, §1.1.5 (complex spaces are locally
ringed: `𝒪_{X,x}` is a local `ℂ`-algebra with maximal ideal the germs vanishing at `x`). -/
theorem an_structureSheaf_isLocal {X : Type u} [TopologicalSpace X] (S : an_ReducedSpace X)
    (x : X) :
    IsLocalRing (S.structureSheaf.presheaf.stalk (x : TopCat.of X)) ∧
      ∀ s, s ∈ nonunits (S.structureSheaf.presheaf.stalk (x : TopCat.of X)) ↔
        S.evalStalk x s = 0 :=
  an_structureSheaf_isLocal_aux S x

/-- The maximal ideal of a stalk is the kernel of evaluation at the point. -/
example {X : Type u} [TopologicalSpace X] (S : an_ReducedSpace X) (x : X) :
    @IsLocalRing.maximalIdeal _ _ (an_structureSheaf_isLocal S x).1 =
      RingHom.ker (S.evalStalk x) := by
  ext s
  rw [@IsLocalRing.mem_maximalIdeal _ _ (an_structureSheaf_isLocal S x).1, RingHom.mem_ker]
  exact (an_structureSheaf_isLocal S x).2 s

/-- **Holomorphic maps in charts.** A map of reduced complex analytic spaces pulls holomorphic
functions back to holomorphic functions exactly when it is continuous and every chart map of the
target, composed with it, is holomorphic in the charts of the source.
Source: Grauert–Remmert, *Coherent Analytic Sheaves*, §1.1.5 and §4.1 (holomorphic maps of
reduced spaces are determined by, and can be read off, the chart maps). -/
theorem an_isHom_iff_chart {X : Type u} [TopologicalSpace X] {Y : Type v}
    [TopologicalSpace Y] (S : an_ReducedSpace X) (T : an_ReducedSpace Y) (f : X → Y) :
    an_IsHom S T f ↔ Continuous f ∧
      ∀ j, S.atlas.IsHolOn ((T.atlas.chart j).toFun ∘ f) (f ⁻¹' (T.atlas.chart j).dom) :=
  an_isHom_iff_chart_aux S T f

example : Continuous an_proj0 ∧ ∀ j, (an_euclidSpace 2).atlas.IsHolOn
    (((an_euclidSpace 1).atlas.chart j).toFun ∘ an_proj0)
    (an_proj0 ⁻¹' ((an_euclidSpace 1).atlas.chart j).dom) :=
  (an_isHom_iff_chart _ _ an_proj0).1 an_proj0_isHom

/-! ### F2: manifolds -/

/-- **Holomorphic functions on a manifold.** On an open set of an analytic manifold, the sections
of the structure sheaf of `an_manifoldSpace E M` are the `ContMDiffOn … ω` functions.
Source: Grauert–Remmert, *Coherent Analytic Sheaves*, §1.1.5; `contDiffOn_omega_iff_analyticOn`
(`C^ω` maps of complex spaces are the analytic ones). -/
theorem an_manifold_isHolFun_iff {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [FiniteDimensional ℂ E] {M : Type*} [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ω M] (g : M → ℂ)
    {U : Set M} (hU : IsOpen U) :
    (an_manifoldSpace E M).IsHolFun (fun x : U ↦ g x) ↔ ContMDiffOn 𝓘(ℂ, E) 𝓘(ℂ, ℂ) ω g U :=
  an_manifold_isHolFun_iff_aux g hU

example (g : ℂ → ℂ) :
    (an_manifoldSpace ℂ ℂ).IsHolFun (fun x : (univ : Set ℂ) ↦ g x) ↔
      ContMDiffOn 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω g univ :=
  an_manifold_isHolFun_iff g isOpen_univ

/-- **Holomorphic maps of manifolds.** A map of analytic manifolds is holomorphic for the manifold
spaces exactly when it is `ContMDiff … ω`.
Source: Grauert–Remmert, *Coherent Analytic Sheaves*, §1.1.5. -/
theorem an_manifold_isHom_iff {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [FiniteDimensional ℂ E] {M : Type*} [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ω M] {E' : Type*}
    [NormedAddCommGroup E'] [NormedSpace ℂ E'] [FiniteDimensional ℂ E'] {M' : Type*}
    [TopologicalSpace M'] [T2Space M'] [SecondCountableTopology M'] [ChartedSpace E' M']
    [IsManifold 𝓘(ℂ, E') ω M'] (f : M → M') :
    an_IsHom (an_manifoldSpace E M) (an_manifoldSpace E' M') f ↔
      ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E') ω f :=
  an_manifold_isHom_iff_aux f

example : an_IsHom (an_manifoldSpace ℂ ℂ) (an_manifoldSpace ℂ ℂ) (id : ℂ → ℂ) :=
  (an_manifold_isHom_iff id).2 contMDiff_id

/-- **Closed analytic subsets of manifolds.** For the manifold space, `an_IsClosedAnalytic` is the
repository's `IsClosedAnalytic` (local equations in the preferred charts).
Source: Grauert–Remmert, *Coherent Analytic Sheaves*, §1.1.6; Schnell, *Complex Manifolds*
(lecture notes), Definition 3.2; analytic chart transitions make the local equations chart
independent. -/
theorem an_manifold_isClosedAnalytic_iff {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [FiniteDimensional ℂ E] {M : Type*} [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ω M] (Z : Set M) :
    an_IsClosedAnalytic (an_manifoldSpace E M) Z ↔ IsClosedAnalytic E Z :=
  an_manifold_isClosedAnalytic_iff_aux Z

example : an_IsClosedAnalytic (an_manifoldSpace ℂ ℂ) {(0 : ℂ)} :=
  (an_manifold_isClosedAnalytic_iff _).2 (isClosedAnalytic_singleton 0)

/-- **The dimension of a manifold.** Every point of a manifold charted on `E` has local dimension
`dim_ℂ E`.
Source: Grauert–Remmert, *Coherent Analytic Sheaves*, §5.1; `adim6_parameter_dimension`
(`ringKrullDim (AnalyticGerm n) = n`). -/
theorem an_manifold_dim {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [FiniteDimensional ℂ E] {M : Type*} [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ω M] (x : M) :
    an_dim (an_manifoldSpace E M) x = ((Module.finrank ℂ E : ℕ∞) : WithBot ℕ∞) :=
  an_manifold_dim_aux x

example : an_dim (an_manifoldSpace ℂ ℂ) (0 : ℂ) =
    ((Module.finrank ℂ ℂ : ℕ∞) : WithBot ℕ∞) :=
  an_manifold_dim 0

/-! ### F2: closed analytic subspaces -/

/-- **Closed analytic subspaces.** A closed analytic subset `Z` of a reduced complex analytic space
is itself one, the inclusion is holomorphic, and a map from a reduced complex analytic space into
`Z` is holomorphic as soon as its composite with the inclusion is: the universal property of the
reduced closed subspace.
Source: Grauert–Remmert, *Coherent Analytic Sheaves*, §1.1.6 and §4.1 (the reduced closed
subspace `(Z, 𝒪_X/𝒥(Z))`, through which every holomorphic map of a reduced space landing in `Z`
factors). -/
theorem an_closedSubspace {X : Type u} [TopologicalSpace X] (S : an_ReducedSpace X)
    {Z : Set X} (hZ : an_IsClosedAnalytic S Z) :
    ∃ SZ : an_ReducedSpace Z, an_IsHom SZ S Subtype.val ∧
      ∀ (W : Type w) [TopologicalSpace W] (C : an_ReducedSpace W) (h : W → Z),
        an_IsHom C S (Subtype.val ∘ h) → an_IsHom C SZ h :=
  an_closedSubspace_aux S hZ

example (hZ : an_IsClosedAnalytic (an_euclidSpace 2) an_node) :
    ∃ SZ : an_ReducedSpace an_node, an_IsHom SZ (an_euclidSpace 2) Subtype.val ∧
      ∀ (W : Type) [TopologicalSpace W] (C : an_ReducedSpace W) (h : W → an_node),
        an_IsHom C (an_euclidSpace 2) (Subtype.val ∘ h) → an_IsHom C SZ h :=
  an_closedSubspace _ hZ

/-! ### F2: dimension -/

/-- **The Krull dimension does not depend on the chart.** Any chart at `x` computes
`an_dimAt S Z x`: transition maps are biholomorphic between local models, so they identify the
reduced local rings.
Source: Grauert–Remmert, *Coherent Analytic Sheaves*, §5.1 (the dimension of a germ is an
invariant of the analytic algebra `𝒪_{X,x}`); de Jong–Pfister, *Local Analytic Geometry*,
§3.4. -/
theorem an_dimAt_eq_chart {X : Type u} [TopologicalSpace X] (S : an_ReducedSpace X)
    (Z : Set X) (i : S.atlas.ι) {x : X} (hx : x ∈ (S.atlas.chart i).dom) :
    an_dimAt S Z x = adim2_dimension (S.atlas.chart i).n
      (adim2_germ (S.atlas.chart i).n ((S.atlas.chart i).toFun '' (Z ∩ (S.atlas.chart i).dom))
        ((S.atlas.chart i).toFun x)) :=
  an_dimAt_eq_chart_aux S Z i hx

example (Z : Set (Fin 2 → ℂ)) (x : Fin 2 → ℂ) :
    an_dimAt (an_euclidSpace 2) Z x = adim2_dimension 2 (adim2_germ 2 (id '' (Z ∩ univ)) x) :=
  an_dimAt_eq_chart (an_euclidSpace 2) Z PUnit.unit (mem_univ x)

/-- **The dimension is the Krull dimension of the stalk.** The local dimension of the space at
`x` is the Krull dimension of the local ring `𝒪_{X,x}`: in a chart, the stalk is the reduced
analytic algebra `𝒪_{ℂⁿ, c x} / I` of the germ of the model.
Source: Grauert–Remmert, *Coherent Analytic Sheaves*, §5.1 (`dim_x X` is the Krull dimension of
`𝒪_{X,x}`) and §4.1 (the stalk of a reduced model space is `𝒪_{ℂⁿ, x}` modulo the full ideal of
the germ). -/
theorem an_dim_eq_stalk {X : Type u} [TopologicalSpace X] (S : an_ReducedSpace X) (x : X) :
    an_dim S x = ringKrullDim (S.structureSheaf.presheaf.stalk (x : TopCat.of X)) :=
  an_dim_eq_stalk_aux S x

example (x : an_node) :
    an_dim an_nodeSpace x =
      ringKrullDim (an_nodeSpace.structureSheaf.presheaf.stalk (x : TopCat.of an_node)) :=
  an_dim_eq_stalk _ x

/-- **Krull dimension equals geometric dimension.** For a closed analytic subset, the Krull
dimension of the germ at `x` is the largest dimension of the manifold points of `Z` arbitrarily
near `x` (and `⊥` off `Z`).
Source: Grauert–Remmert, *Coherent Analytic Sheaves*, §5.1–5.3 (algebraic and analytic dimension
agree; the regular locus is dense); Chirka, *Complex Analytic Sets*, §2.4 and §3.4. -/
theorem an_dimAt_eq_geomDim {X : Type u} [TopologicalSpace X] (S : an_ReducedSpace X)
    {Z : Set X} (hZ : an_IsClosedAnalytic S Z) (x : X) :
    an_dimAt S Z x = an_geomDim S Z x :=
  an_dimAt_eq_geomDim_aux S hZ x

example (x : Fin 2 → ℂ) : an_dim (an_euclidSpace 2) x = an_geomDim (an_euclidSpace 2) univ x :=
  an_dimAt_eq_geomDim _ (an_isClosedAnalytic_univ _) x

/-- **`ℂⁿ` has dimension `n`.**
Source: Gunning–Rossi, *Analytic Functions of Several Complex Variables*, Ch. II, §B;
`adim6_parameter_dimension` (`ringKrullDim (AnalyticGerm n) = n`). -/
theorem an_dim_euclid (n : ℕ) (x : Fin n → ℂ) :
    an_dim (an_euclidSpace n) x = ((n : ℕ∞) : WithBot ℕ∞) :=
  an_dim_euclid_aux n x

example : an_dim (an_euclidSpace 3) 0 = ((3 : ℕ∞) : WithBot ℕ∞) := an_dim_euclid 3 0

/-- **The node is one-dimensional at its singular point.** The germ of `{z₀ z₁ = 0}` at the origin
has reduced local ring `ℂ{z₀, z₁}/(z₀ z₁)`, of Krull dimension `1`.
Source: de Jong–Pfister, *Local Analytic Geometry*, §3.4 (dimension of `𝒪/(f)` for a nonzero
non-unit `f` is one less); Chirka, *Complex Analytic Sets*, §2.3. -/
theorem an_dim_node :
    an_dim an_nodeSpace ⟨0, mem_univ _, by funext i; simp [an_nodeEqn]⟩ = 1 :=
  an_dim_node_aux

example : an_dim an_nodeSpace ⟨0, mem_univ _, by funext i; simp [an_nodeEqn]⟩ ≠ 2 := by
  rw [an_dim_node]; decide

/-! ### F3: locality and finiteness -/

/-- **Closed analyticity is local.** A closed set that is near each of its points the trace of a
closed analytic subset is closed analytic.
Source: Grauert–Remmert, *Coherent Analytic Sheaves*, §1.1.6 (analyticity is a local
condition). -/
theorem an_isClosedAnalytic_of_locally {Y : Type v} [TopologicalSpace Y]
    (T : an_ReducedSpace Y) {Z : Set Y} (hZ : IsClosed Z)
    (h : ∀ y ∈ Z, an_IsLocallyAnalyticAt T Z y) :
    an_IsClosedAnalytic T Z :=
  an_isClosedAnalytic_of_locally_aux T hZ h

example : an_IsClosedAnalytic (an_euclidSpace 1) (∅ : Set (Fin 1 → ℂ)) :=
  an_isClosedAnalytic_of_locally _ isClosed_empty fun _ h ↦ h.elim

/-- **Reduced complex analytic spaces are locally compact.** A local model is relatively closed in
an open subset of `ℂⁿ`.
Source: Grauert–Remmert, *Coherent Analytic Sheaves*, §1.1.5 (complex spaces are locally
compact). -/
theorem an_locallyCompactSpace {X : Type u} [TopologicalSpace X] (S : an_ReducedSpace X) :
    LocallyCompactSpace X :=
  an_locallyCompactSpace_aux S

example : LocallyCompactSpace an_node := an_locallyCompactSpace an_nodeSpace

/-- **Local dimension is bounded on compacta.** Finitely many charts cover a compact set, and the
dimension at a point is at most the ambient dimension of any chart there.
Source: Grauert–Remmert, *Coherent Analytic Sheaves*, §5.1 (`dim_x X ≤ emb dim`); Bourbaki,
*Topologie générale*, Ch. I, §9.1 (finite subcovers). -/
theorem an_dimAt_bounded {X : Type u} [TopologicalSpace X] (S : an_ReducedSpace X)
    (Z : Set X) {K : Set X} (hK : IsCompact K) :
    ∃ d : ℕ, ∀ x ∈ K, an_dimAt S Z x ≤ ((d : ℕ∞) : WithBot ℕ∞) :=
  an_dimAt_bounded_aux S Z hK

example : ∃ d : ℕ, ∀ x ∈ ({0} : Set (Fin 2 → ℂ)),
    an_dimAt (an_euclidSpace 2) univ x ≤ ((d : ℕ∞) : WithBot ℕ∞) :=
  an_dimAt_bounded _ univ isCompact_singleton

/-! ### F3: the finite case -/

/-- **Proper finite projections.** If the projection of a closed analytic set `T ⊆ ℂᵐ × ℂᵏ` to
`ℂᵐ` is proper with finite fibres, its image is closed analytic: near a point of the image the
elementary symmetric functions of the fibre coordinates (canonical defining functions, from
Weierstrass preparation) give the equations.
Source: Gunning–Rossi, *Analytic Functions of Several Complex Variables*, Ch. III, §B (proper
projections); Chirka, *Complex Analytic Sets*, §3.7 (images under proper finite projections);
Narasimhan, *Introduction to the Theory of Analytic Spaces*, LNM 25, Ch. VII, Theorem 1. -/
theorem an_finite_projection (m k : ℕ) (T : Set ((Fin m → ℂ) × (Fin k → ℂ)))
    (hT : IsClosedAnalytic ((Fin m → ℂ) × (Fin k → ℂ)) T)
    (hproper : IsProperMap (fun a : T ↦ (a : (Fin m → ℂ) × (Fin k → ℂ)).1))
    (hfin : ∀ y, {a | a ∈ T ∧ a.1 = y}.Finite) :
    IsClosedAnalytic (Fin m → ℂ) (Prod.fst '' T) :=
  an_finite_projection_aux m k T hT hproper hfin

example (hproper : IsProperMap (fun a : (univ : Set ((Fin 1 → ℂ) × (Fin 0 → ℂ))) ↦
      (a : (Fin 1 → ℂ) × (Fin 0 → ℂ)).1))
    (hfin : ∀ y, {a : (Fin 1 → ℂ) × (Fin 0 → ℂ) | a ∈ univ ∧ a.1 = y}.Finite) :
    IsClosedAnalytic (Fin 1 → ℂ) (Prod.fst '' (univ : Set ((Fin 1 → ℂ) × (Fin 0 → ℂ)))) :=
  an_finite_projection 1 0 univ isClosedAnalytic_univ hproper hfin

/-- **The finite mapping theorem.** The image of a closed analytic subset under a proper
holomorphic map with finite fibres on it is closed analytic.
Source: Grauert–Remmert, *Coherent Analytic Sheaves*, Ch. 2 (finite holomorphic maps; the finite
mapping theorem); Narasimhan, LNM 25, Ch. VII, Theorem 1. -/
theorem an_finite_mapping {X : Type u} [TopologicalSpace X] {Y : Type v}
    [TopologicalSpace Y] (S : an_ReducedSpace X) (T : an_ReducedSpace Y) (f : X → Y)
    (hf : an_IsProperHom S T f) {Z : Set X} (hZ : an_IsClosedAnalytic S Z)
    (hfin : ∀ y, (Z ∩ f ⁻¹' {y}).Finite) :
    an_IsClosedAnalytic T (f '' Z) :=
  an_finite_mapping_aux S T f hf hZ hfin

/-- The closed embedding of the node has finite (at most one-point) fibres. -/
example (hfin : ∀ y, ((univ : Set an_node) ∩ Subtype.val ⁻¹' {y}).Finite) :
    an_IsClosedAnalytic (an_euclidSpace 2) (Subtype.val '' (univ : Set an_node)) :=
  an_finite_mapping an_nodeSpace (an_euclidSpace 2) _
    (an_modelSpace_val_isProperHom an_nodeEqn an_nodeEqn_analytic)
    (an_isClosedAnalytic_univ _) hfin

/-! ### F3: rank and fibre dimension -/

/-- **Cartan–Remmert.** For a holomorphic map and a closed analytic subset `Z`, the points of `Z`
where the fibre of `f` through them has dimension at least `k` form a closed analytic subset: the
fibre dimension is upper semicontinuous in the analytic Zariski topology.
Source: Fischer, *Complex Analytic Geometry*, LNM 538 (1976), §3.6 (Cartan–Remmert theorem);
Grauert–Remmert, *Coherent Analytic Sheaves*, Ch. 5 (dimension theory). -/
theorem an_cartan_remmert {X : Type u} [TopologicalSpace X] {Y : Type v}
    [TopologicalSpace Y] (S : an_ReducedSpace X) (T : an_ReducedSpace Y) (f : X → Y)
    (hf : an_IsHom S T f) {Z : Set X} (hZ : an_IsClosedAnalytic S Z) (k : ℕ) :
    an_IsClosedAnalytic S
      {x | x ∈ Z ∧ ((k : ℕ∞) : WithBot ℕ∞) ≤ an_dimAt S (Z ∩ f ⁻¹' {f x}) x} :=
  an_cartan_remmert_aux S T f hf hZ k

example (hZ : an_IsClosedAnalytic (an_euclidSpace 2) an_node) :
    an_IsClosedAnalytic (an_euclidSpace 2)
      {x | x ∈ an_node ∧ ((1 : ℕ∞) : WithBot ℕ∞) ≤
        an_dimAt (an_euclidSpace 2) (an_node ∩ an_proj0 ⁻¹' {an_proj0 x}) x} :=
  an_cartan_remmert _ (an_euclidSpace 1) an_proj0 an_proj0_isHom hZ 1

/-- **The constant rank theorem.** A holomorphic map of constant rank `r` on an open `U` maps a
small neighbourhood of each point onto a closed analytic piece of an open `V` (an `r`-dimensional
submanifold), whose germ has dimension `r`.
Source: Gunning–Rossi, *Analytic Functions of Several Complex Variables*, Ch. I, §B, Theorem 5
(rank theorem); Grauert–Remmert, *Coherent Analytic Sheaves*, §5.1. -/
theorem an_constant_rank (n m r : ℕ) (U : Set (Fin n → ℂ)) (hU : IsOpen U)
    (g : (Fin n → ℂ) → (Fin m → ℂ)) (hg : AnalyticOnNhd ℂ g U)
    (hr : ∀ z ∈ U, Module.finrank ℂ
      (LinearMap.range (fderiv ℂ g z : (Fin n → ℂ) →ₗ[ℂ] (Fin m → ℂ))) = r)
    {x : Fin n → ℂ} (hx : x ∈ U) :
    ∃ (W : Set (Fin n → ℂ)) (V : Set (Fin m → ℂ)), IsOpen W ∧ x ∈ W ∧ W ⊆ U ∧ IsOpen V ∧
      g '' W ⊆ V ∧
      (∃ (k : ℕ) (F : (Fin m → ℂ) → (Fin k → ℂ)), AnalyticOnNhd ℂ F V ∧
        ∀ y ∈ V, (y ∈ g '' W ↔ F y = 0)) ∧
      adim2_dimension m (adim2_germ m (g '' W) (g x)) = ((r : ℕ∞) : WithBot ℕ∞) :=
  an_constant_rank_aux n m r U hU g hg hr hx

example (hr : ∀ z ∈ (univ : Set (Fin 2 → ℂ)), Module.finrank ℂ
      (LinearMap.range (fderiv ℂ an_proj0 z : (Fin 2 → ℂ) →ₗ[ℂ] (Fin 1 → ℂ))) = 1)
    (hg : AnalyticOnNhd ℂ an_proj0 univ) :
    ∃ (W : Set (Fin 2 → ℂ)) (V : Set (Fin 1 → ℂ)), IsOpen W ∧ 0 ∈ W ∧ W ⊆ univ ∧ IsOpen V ∧
      an_proj0 '' W ⊆ V ∧
      (∃ (k : ℕ) (F : (Fin 1 → ℂ) → (Fin k → ℂ)), AnalyticOnNhd ℂ F V ∧
        ∀ y ∈ V, (y ∈ an_proj0 '' W ↔ F y = 0)) ∧
      adim2_dimension 1 (adim2_germ 1 (an_proj0 '' W) (an_proj0 0)) = ((1 : ℕ∞) : WithBot ℕ∞) :=
  an_constant_rank 2 1 1 univ isOpen_univ an_proj0 hg hr (mem_univ 0)

/-! ### F3: Remmert–Stein -/

/-- **Remmert–Stein.** Let `T ⊆ ℂⁿ` be closed analytic of dimension `< p` at each of its points,
and `B ⊆ ℂⁿ \ T` closed analytic in `ℂⁿ \ T` and of pure dimension `p`. Then the closure of `B` is
closed analytic in `ℂⁿ`.
Source: Remmert–Stein, *Math. Ann.* 126 (1953), 263–306, Satz 13; Chirka, *Complex Analytic
Sets*, §4.4 (Remmert–Stein theorem); Gunning–Rossi, Ch. V. -/
theorem an_remmert_stein (n p : ℕ) (T B : Set (Fin n → ℂ))
    (hT : IsClosedAnalytic (Fin n → ℂ) T) (hBT : Disjoint B T)
    (hB : ∀ z ∉ T, ∃ V : Set (Fin n → ℂ), IsOpen V ∧ z ∈ V ∧ Disjoint V T ∧
      ∃ (k : ℕ) (F : (Fin n → ℂ) → (Fin k → ℂ)), AnalyticOnNhd ℂ F V ∧
        ∀ y ∈ V, (y ∈ B ↔ F y = 0))
    (hpure : ∀ z ∈ B, adim2_dimension n (adim2_germ n B z) = ((p : ℕ∞) : WithBot ℕ∞))
    (hdimT : ∀ z ∈ T, adim2_dimension n (adim2_germ n T z) < ((p : ℕ∞) : WithBot ℕ∞)) :
    IsClosedAnalytic (Fin n → ℂ) (closure B) :=
  an_remmert_stein_aux n p T B hT hBT hB hpure hdimT

/-- With `T = ∅` the extension statement reduces to: a closed analytic set equals its closure. -/
example (B : Set (Fin 1 → ℂ))
    (hB : ∀ z ∉ (∅ : Set (Fin 1 → ℂ)), ∃ V : Set (Fin 1 → ℂ), IsOpen V ∧ z ∈ V ∧
      Disjoint V ∅ ∧ ∃ (k : ℕ) (F : (Fin 1 → ℂ) → (Fin k → ℂ)), AnalyticOnNhd ℂ F V ∧
        ∀ y ∈ V, (y ∈ B ↔ F y = 0))
    (hpure : ∀ z ∈ B, adim2_dimension 1 (adim2_germ 1 B z) = ((0 : ℕ∞) : WithBot ℕ∞)) :
    IsClosedAnalytic (Fin 1 → ℂ) (closure B) :=
  an_remmert_stein 1 0 ∅ B isClosedAnalytic_empty (disjoint_empty B) hB hpure (fun _ h ↦ h.elim)

/-! ### F3: induction on dimension -/

/-- **Induction on dimension: the base.** Over an open `V` above which `Z` is zero-dimensional,
the image of `Z` under a proper holomorphic map is locally analytic: fibres are compact and
discrete, so the image is locally finite.
Source: Narasimhan, LNM 25, Ch. VII (proof of the proper mapping theorem); Grauert–Remmert,
*Coherent Analytic Sheaves*, §5.1 (zero-dimensional germs are points). -/
theorem an_remmert_local_zero {X : Type u} [TopologicalSpace X] {Y : Type v}
    [TopologicalSpace Y] (S : an_ReducedSpace X) (T : an_ReducedSpace Y) (f : X → Y)
    (hf : an_IsProperHom S T f) {Z : Set X} (hZ : an_IsClosedAnalytic S Z) {V : Set Y}
    (hV : IsOpen V) (hdim : ∀ x ∈ Z ∩ f ⁻¹' V, an_dimAt S Z x ≤ 0) :
    ∀ y ∈ V, an_IsLocallyAnalyticAt T (f '' Z) y :=
  an_remmert_local_zero_aux S T f hf hZ hV hdim

example (hdim : ∀ x ∈ (∅ : Set (Fin 1 → ℂ)) ∩ id ⁻¹' univ,
      an_dimAt (an_euclidSpace 1) ∅ x ≤ 0) :
    ∀ y ∈ (univ : Set (Fin 1 → ℂ)), an_IsLocallyAnalyticAt (an_euclidSpace 1) (id '' ∅) y :=
  an_remmert_local_zero _ _ id (an_isProperHom_id _) (an_isClosedAnalytic_empty _)
    isOpen_univ hdim

/-- **Induction on dimension: the step.** If images of closed analytic subsets of dimension `≤ d`
over open sets of the target are locally analytic there, so are images of those of dimension
`≤ d + 1`. The step removes, by the Cartan–Remmert loci (`an_cartan_remmert`), the singular locus
and the locus where the rank of `f` drops, a closed analytic subset of dimension `≤ d` whose image
is analytic by hypothesis; off it the image is, by the constant rank theorem
(`an_constant_rank`) and properness, a pure-dimensional analytic set, and Remmert–Stein
(`an_remmert_stein`) extends it across the smaller part, with the finite mapping theorem
(`an_finite_mapping`) where the rank equals the dimension.
Source: Remmert, *Math. Ann.* 133 (1957), 328–370, §§13–15; Narasimhan, LNM 25, Ch. VII;
Chirka, *Complex Analytic Sets*, §§3–4. -/
theorem an_remmert_local_succ {X : Type u} [TopologicalSpace X] {Y : Type v}
    [TopologicalSpace Y] (S : an_ReducedSpace X) (T : an_ReducedSpace Y) (f : X → Y)
    (hf : an_IsProperHom S T f) (d : ℕ)
    (ih : ∀ Z' : Set X, an_IsClosedAnalytic S Z' → ∀ V : Set Y, IsOpen V →
      (∀ x ∈ Z' ∩ f ⁻¹' V, an_dimAt S Z' x ≤ ((d : ℕ∞) : WithBot ℕ∞)) →
      ∀ y ∈ V, an_IsLocallyAnalyticAt T (f '' Z') y)
    {Z : Set X} (hZ : an_IsClosedAnalytic S Z) {V : Set Y} (hV : IsOpen V)
    (hdim : ∀ x ∈ Z ∩ f ⁻¹' V, an_dimAt S Z x ≤ (((d + 1 : ℕ) : ℕ∞) : WithBot ℕ∞)) :
    ∀ y ∈ V, an_IsLocallyAnalyticAt T (f '' Z) y :=
  an_remmert_local_succ_aux S T f hf d ih hZ hV hdim

example (ih : ∀ Z' : Set (Fin 1 → ℂ), an_IsClosedAnalytic (an_euclidSpace 1) Z' →
      ∀ V : Set (Fin 1 → ℂ), IsOpen V →
      (∀ x ∈ Z' ∩ id ⁻¹' V, an_dimAt (an_euclidSpace 1) Z' x ≤ ((0 : ℕ∞) : WithBot ℕ∞)) →
      ∀ y ∈ V, an_IsLocallyAnalyticAt (an_euclidSpace 1) (id '' Z') y)
    (hdim : ∀ x ∈ (univ : Set (Fin 1 → ℂ)) ∩ id ⁻¹' univ,
      an_dimAt (an_euclidSpace 1) univ x ≤ (((0 + 1 : ℕ) : ℕ∞) : WithBot ℕ∞)) :
    ∀ y ∈ (univ : Set (Fin 1 → ℂ)), an_IsLocallyAnalyticAt (an_euclidSpace 1) (id '' univ) y :=
  an_remmert_local_succ _ _ id (an_isProperHom_id _) 0 ih (an_isClosedAnalytic_univ _)
    isOpen_univ hdim

/-! ### F3: the proper mapping theorem -/

/-- **Remmert's proper mapping theorem.** The image of a closed analytic subset under a proper
holomorphic map of reduced complex analytic spaces is closed analytic. It follows from the
locality statements, the bound on compacta and the induction on dimension above: the image is
closed because a proper map is closed.
Source: Remmert, *Math. Ann.* 133 (1957), 328–370, Satz 23; Grauert–Remmert, *Coherent Analytic
Sheaves*, §10.6 (proper mapping theorem). -/
theorem an_remmert {X : Type u} [TopologicalSpace X] {Y : Type v}
    [TopologicalSpace Y] (S : an_ReducedSpace X) (T : an_ReducedSpace Y) (f : X → Y)
    (hf : an_IsProperHom S T f) {Z : Set X} (hZ : an_IsClosedAnalytic S Z) :
    an_IsClosedAnalytic T (f '' Z) :=
  an_remmert_aux S T f hf hZ

/-- The closed embedding of the node: its image in `ℂ²` is closed analytic. -/
example : an_IsClosedAnalytic (an_euclidSpace 2) (Subtype.val '' (univ : Set an_node)) :=
  an_remmert an_nodeSpace (an_euclidSpace 2) _
    (an_modelSpace_val_isProperHom an_nodeEqn an_nodeEqn_analytic) (an_isClosedAnalytic_univ _)

/-- **Properness is needed.** The hyperbola `{z₀ z₁ = 1}` is closed analytic in `ℂ²` and the
first projection is holomorphic, but not proper, and the image `{z ≠ 0}` is not closed analytic.
Source: Grauert–Remmert, *Coherent Analytic Sheaves*, §10.6 (the properness hypothesis). -/
theorem an_remmert_not_proper :
    an_IsClosedAnalytic (an_euclidSpace 2) an_hyperbola ∧
      an_IsHom (an_euclidSpace 2) (an_euclidSpace 1) an_proj0 ∧ ¬ IsProperMap an_proj0 ∧
      ¬ an_IsClosedAnalytic (an_euclidSpace 1) (an_proj0 '' an_hyperbola) :=
  an_remmert_not_proper_aux

example : ¬ an_IsProperHom (an_euclidSpace 2) (an_euclidSpace 1) an_proj0 :=
  fun h ↦ an_remmert_not_proper.2.2.1 h.1

/-- **The manifold case.** Remmert's theorem for a proper holomorphic map of analytic manifolds,
in exactly the shape of `f1_remmert` (`HodgeLean.Foundations.Program.CycleSpreading`), whose
open obligation `f1_remmert_aux` it provides, once that file imports this one. It follows from
`an_remmert` for `an_manifoldSpace` through `an_manifold_isHom_iff` and
`an_manifold_isClosedAnalytic_iff`. No second countability is assumed here: the statement is local
on `M`, and over a relatively compact chart domain of `M` the proper map `π` sees a compact part
of `P`, covered by finitely many chart domains, whose union is a second-countable open
submanifold.
Source: Remmert, *Math. Ann.* 133 (1957), 328–370, Satz 23; Grauert–Remmert, *Coherent Analytic
Sheaves*, §10.6.1. -/
theorem an_remmert_manifold {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E] {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace E M]
    [IsManifold 𝓘(ℂ, E) ω M] {d : ℕ} {P : Type*} [TopologicalSpace P] [T2Space P]
    [ChartedSpace (Fin d → ℂ) P] [IsManifold 𝓘(ℂ, Fin d → ℂ) ω P] (π : P → M)
    (hπ : IsProperMap π) (hhol : ContMDiff 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, E) ω π) {Z : Set P}
    (hZ : IsClosedAnalytic (Fin d → ℂ) Z) : IsClosedAnalytic E (π '' Z) :=
  an_remmert_manifold_aux π hπ hhol hZ

example : IsClosedAnalytic (Fin 1 → ℂ) ((id : (Fin 1 → ℂ) → Fin 1 → ℂ) '' univ) :=
  an_remmert_manifold id isProperMap_id contMDiff_id isClosedAnalytic_univ

end HodgeLean.Foundations.Analytic
