import HodgeLean.Adapters.NormalConeB3Defs
import HodgeLean.Adapters.CycleClassDivisorLocalDefs
import HodgeLean.Foundations.Analytic.Analytification
import HodgeConjecture.Definitions.AlgebraicTopology.LocalHomology.NormalProjectionCoclass

/-! # Analytic specialization: objects

Stage A3-B4 objects. A scheme `Z` with a map `q : Z ⟶ Spec ℂ` has the space of complex points
`a3b4_an q`, with the upstream analytic topology, and a morphism over `Spec ℂ` gives a continuous
map `a3b4_anMap`. These are the spaces of F4's analytification `f4_analytification`; the
holomorphic structure is used only through F4's holomorphic functions `an_ReducedSpace.IsHolFun`.

Maps of pairs: `a3b4_supportPairMap f S S' h` is a continuous map viewed as a map of pairs
`(T, T ∖ S) ⟶ (T', T' ∖ S')`, given `h : f⁻¹ S' ⊆ S`; `a3b4_neighborhoodPairMap W S` is the
inclusion `(W, W ∖ S) ⟶ (T, T ∖ S)`. Relative singular cohomology and its pullbacks are the B1
layer `RelativeCohomology`, `relativeCohomologyMap` and `cohomologyWithSupportMap`.

Complex orientation: `a3b4_IsHolChart` says that a chart `e` of the complex points into
`ℂʳ × ℂᶜ` has holomorphic coordinates in F4's sense. For a support flattened by such a chart, the
upstream `chartNormalProjectionCoclass` is the pullback along the normal coordinate of the class in
`H^{2c}(ℂᶜ, ℂᶜ ∖ {0}; ℚ)` that evaluates to `1` on the complex orientation class.

Cycle classes: `a3b4_cycleSupport q γ` is the set of complex points lying on the support of an
algebraic cycle `γ`, `a3b4_multiplicity q γ x` is the sum of the coefficients of the components of
`γ` that contain a neighbourhood of `x` in that support, and `a3b4_IsCycleClass q γ c β` says that
`β ∈ H^{2c}(Z(ℂ), Z(ℂ) ∖ |γ|; ℚ)` restricts, near every point of `|γ|` at which some holomorphic
chart flattens `|γ|` with normal dimension `c`, to the multiplicity times the normalized normal
coclass of that chart. This is a property of a class; no definition here asserts that such a class
exists or is unique, which are statements of the frozen spec. No definition here chooses a witness
from an open theorem.
-/

noncomputable section
namespace HodgeLean.Adapters
open CategoryTheory Limits AlgebraicGeometry AlgebraicTopology.Singular
open HodgeLean.Foundations.Analytic

universe u

/-! ## Complex points and maps of pairs -/

/-- The complex points of a scheme over `ℂ`, with the analytic topology.
Source: Serre, *Géométrie algébrique et géométrie analytique*, Ann. Inst. Fourier 6 (1956), §2;
upstream `AlgebraicGeometry.ComplexPoint` and `Point.analyticTopology`. -/
abbrev a3b4_an {Z : Scheme.{0}} (q : Z ⟶ Spec (CommRingCat.of ℂ)) : TopCat.{0} :=
  TopCat.of (ComplexPoint (Over.mk q))

example : TopCat.{0} := a3b4_an (𝟙 (Spec (CommRingCat.of ℂ)))

/-- The continuous map of complex points of a morphism over `ℂ`.
Source: Serre, GAGA, §2; upstream `Point.continuousMap`; F4 `f4_map_isHom`. -/
def a3b4_anMap {Z Z' : Scheme.{0}} {q : Z ⟶ Spec (CommRingCat.of ℂ)}
    {q' : Z' ⟶ Spec (CommRingCat.of ℂ)} (g : Z ⟶ Z') (h : g ≫ q' = q) :
    a3b4_an q ⟶ a3b4_an q' :=
  TopCat.ofHom (Point.continuousMap (Over.homMk g h : Over.mk q ⟶ Over.mk q'))

example {Z : Scheme.{0}} (q : Z ⟶ Spec (CommRingCat.of ℂ)) (z : a3b4_an q) :
    a3b4_anMap (𝟙 Z) (Category.id_comp q) z =
      Point.map (Over.homMk (𝟙 Z) (Category.id_comp _) : Over.mk q ⟶ Over.mk q) z := rfl

/-- A continuous map as a map of pairs `(T, T ∖ S) ⟶ (T', T' ∖ S')`, given that the preimage of
`S'` lies in `S`.
Source: Hatcher, *Algebraic Topology*, §2.1 (maps of pairs); upstream `TopPair.ofHom`. -/
def a3b4_supportPairMap {T T' : TopCat.{0}} (f : T ⟶ T') (S : Set T) (S' : Set T')
    (h : ∀ x, f x ∈ S' → x ∈ S) :
    TopPair.ofSubset (X := T) Sᶜ ⟶ TopPair.ofSubset (X := T') S'ᶜ :=
  TopPair.ofHom f (TopCat.ofHom ⟨fun x => ⟨f x.1, fun hx => x.2 (h _ hx)⟩, by fun_prop⟩)
    (by ext; rfl)

example (T : TopCat.{0}) (S : Set T) :
    TopPair.ofSubset (X := T) Sᶜ ⟶ TopPair.ofSubset (X := T) Sᶜ :=
  a3b4_supportPairMap (𝟙 T) S S fun _ h => h

/-- The inclusion of pairs `(W, W ∖ S) ⟶ (M, M ∖ S)` for a subset `W`.
Source: Hatcher, *Algebraic Topology*, §2.1 (excision); upstream
`neighborhoodSupportComplementPair`. -/
def a3b4_neighborhoodPairMap {M : Type} [TopologicalSpace M] (W S : Set M) :
    neighborhoodSupportComplementPair W S ⟶ TopPair.ofSubset (X := TopCat.of M) Sᶜ :=
  TopPair.ofHom (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩)
    (TopCat.ofHom ⟨fun w => ⟨w.1.1, w.2⟩, by fun_prop⟩) (by ext; rfl)

example {M : Type} [TopologicalSpace M] (S : Set M) :
    neighborhoodSupportComplementPair Set.univ S ⟶ TopPair.ofSubset (X := TopCat.of M) Sᶜ :=
  a3b4_neighborhoodPairMap Set.univ S

/-! ## Holomorphic charts and normalized cycle classes -/

/-- A scheme quasi-compact over `ℂ` is a compact space.
Source: Mathlib, `AlgebraicGeometry.quasiCompact_iff_compactSpace`. -/
theorem a3b4_compactSpace {Z : Scheme.{0}} (q : Z ⟶ Spec (CommRingCat.of ℂ)) [QuasiCompact q] :
    CompactSpace Z :=
  (quasiCompact_iff_compactSpace q).1 inferInstance

/-- A chart of the complex points into `ℂʳ × ℂᶜ` is holomorphic if all of its coordinates are
holomorphic functions on its source, for F4's analytification. A holomorphic homeomorphism of a
reduced space onto an open subset of `ℂʳ⁺ᶜ` is a biholomorphism of complex manifolds, so its normal
coordinates carry the complex orientation.
Source: F4 `f4_analytification` and `an_ReducedSpace.IsHolFun`; Grauert–Remmert, *Coherent
Analytic Sheaves*, §1.1.5. -/
def a3b4_IsHolChart {Z : Scheme.{0}} (q : Z ⟶ Spec (CommRingCat.of ℂ)) [LocallyOfFiniteType q]
    [QuasiCompact q] [IsSeparated q] {r c : ℕ}
    (e : OpenPartialHomeomorph (ComplexPoint (Over.mk q)) ((Fin r → ℂ) × (Fin c → ℂ))) : Prop :=
  haveI : LocallyOfFiniteType (Over.mk q).hom := ‹LocallyOfFiniteType q›
  haveI : QuasiCompact (Over.mk q).hom := ‹QuasiCompact q›
  haveI : IsSeparated (Over.mk q).hom := ‹IsSeparated q›
  (∀ j, (f4_analytification (Over.mk q)).IsHolFun (fun y : e.source ↦ (e y).1 j)) ∧
    ∀ j, (f4_analytification (Over.mk q)).IsHolFun (fun y : e.source ↦ (e y).2 j)

example {Z : Scheme.{0}} (q : Z ⟶ Spec (CommRingCat.of ℂ)) [LocallyOfFiniteType q]
    [QuasiCompact q] [IsSeparated q] {r c : ℕ}
    (e : OpenPartialHomeomorph (ComplexPoint (Over.mk q)) ((Fin r → ℂ) × (Fin c → ℂ))) :
    Prop := a3b4_IsHolChart q e

/-- The complex points lying on the support of an algebraic cycle: those whose scheme point lies
in the closure of a point where the cycle is nonzero.
Source: Fulton, *Intersection Theory*, second edition, §§1.5 and 19.1 (the support `|α|`). -/
def a3b4_cycleSupport {Z : Scheme.{0}} (q : Z ⟶ Spec (CommRingCat.of ℂ))
    (γ : AlgebraicCycle Z ℚ) : Set (ComplexPoint (Over.mk q)) :=
  Point.underlying ⁻¹' ⋃ ξ ∈ γ.support, closure {ξ}

example {Z : Scheme.{0}} (q : Z ⟶ Spec (CommRingCat.of ℂ)) :
    a3b4_cycleSupport q (0 : AlgebraicCycle Z ℚ) = ∅ := by
  ext x
  simp [a3b4_cycleSupport]

/-- The multiplicity of a cycle at a complex point: the sum of the coefficients of the points of
its support whose closure contains a neighbourhood of `x` in the support of the cycle. At a point
where the support is locally a manifold exactly one component of maximal dimension passes, and
components of smaller dimension contain no such neighbourhood. The sum runs over the finite
support of the cycle on a quasi-compact scheme.
Source: Fulton, *Intersection Theory*, second edition, §§1.5 and 19.1 (the coefficient of `[V]`
in `α`); `a3b2_support_finite`. -/
def a3b4_multiplicity {Z : Scheme.{0}} (q : Z ⟶ Spec (CommRingCat.of ℂ)) [QuasiCompact q]
    (γ : AlgebraicCycle Z ℚ) (x : ComplexPoint (Over.mk q)) : ℚ := by
  classical
  haveI := a3b4_compactSpace q
  exact ∑ ξ ∈ (a3b2_support_finite γ).toFinset,
    if ∃ U : Set (ComplexPoint (Over.mk q)), IsOpen U ∧ x ∈ U ∧
        U ∩ a3b4_cycleSupport q γ ⊆ Point.underlying ⁻¹' closure {ξ} then γ ξ else 0

example {Z : Scheme.{0}} (q : Z ⟶ Spec (CommRingCat.of ℂ)) [QuasiCompact q]
    (x : ComplexPoint (Over.mk q)) : a3b4_multiplicity q (0 : AlgebraicCycle Z ℚ) x = 0 := by
  classical
  simp [a3b4_multiplicity, Finset.sum_eq_zero]

/-- `β ∈ H^{2c}(Z(ℂ), Z(ℂ) ∖ |γ|; ℚ)` is a normalized cycle class of `γ` in codimension `c`: for
every holomorphic chart `e` into `ℂʳ × ℂᶜ` in which `|γ|` is the zero set of the normal
coordinate, and every point `x` of `|γ|` in its source, `β` restricts on some open neighbourhood
`W ⊆ e.source` of `x` to the multiplicity of `γ` at `x` times the normal coclass of `e`, which
evaluates to `1` on the complex orientation class. Points where no such chart exists (singular
points of the support, and components of another codimension) impose no condition.
Source: Fulton, *Intersection Theory*, second edition, §19.1 (the cycle class `cl(V)` and its
local orientation); Borel–Haefliger, *La classe d'homologie fondamentale d'un espace analytique*,
Bull. Soc. Math. France 89 (1961); upstream `chartNormalProjectionCoclass`. -/
def a3b4_IsCycleClass {Z : Scheme.{0}} (q : Z ⟶ Spec (CommRingCat.of ℂ)) [LocallyOfFiniteType q]
    [QuasiCompact q] [IsSeparated q] (γ : AlgebraicCycle Z ℚ) (c : ℕ)
    (β : RelativeCohomology ℚ (TopPair.ofSubset (X := a3b4_an q) (a3b4_cycleSupport q γ)ᶜ)
      (2 * c)) : Prop :=
  ∀ (r : ℕ) (e : OpenPartialHomeomorph (ComplexPoint (Over.mk q)) ((Fin r → ℂ) × (Fin c → ℂ)))
    (hS : ∀ y ∈ e.source, y ∈ a3b4_cycleSupport q γ ↔ (e y).2 = 0) (x : ComplexPoint (Over.mk q)),
    x ∈ e.source → x ∈ a3b4_cycleSupport q γ → a3b4_IsHolChart q e →
    ∃ (W : Set (ComplexPoint (Over.mk q))) (hW : W ⊆ e.source), IsOpen W ∧ x ∈ W ∧
      relativeCohomologyMap ℚ (2 * c) (a3b4_neighborhoodPairMap W (a3b4_cycleSupport q γ)) β =
        a3b4_multiplicity q γ x •
          chartNormalProjectionCoclass (Fin r → ℂ) c e (a3b4_cycleSupport q γ) hS W hW

/-- The zero cycle has the zero class in every codimension: its support is empty, so no chart
condition applies.
Source: Fulton, *Intersection Theory*, second edition, §19.1. -/
example {Z : Scheme.{0}} (q : Z ⟶ Spec (CommRingCat.of ℂ)) [LocallyOfFiniteType q]
    [QuasiCompact q] [IsSeparated q] (c : ℕ) :
    a3b4_IsCycleClass q (0 : AlgebraicCycle Z ℚ) c 0 := by
  intro r e hS x _ hx
  simp [a3b4_cycleSupport] at hx

/-! ## Fibres of a family over complex points -/

/-- The rational points of the parameter line are closed immersions.
Source: Mathlib, `AlgebraicGeometry.IsClosedImmersion.spec_of_surjective`. -/
instance a3b4_point_isClosedImmersion (k : Type u) [Field k] (c : k) :
    IsClosedImmersion (a3b2_point k c) :=
  IsClosedImmersion.spec_of_surjective _ fun x => ⟨Polynomial.C x, by simp⟩

/-- The map of fibres over `t = c` induced by a map of families over the parameter line; at
`c = 0` it is `a3b2_zeroFibreMap`.
Source: Fulton, *Intersection Theory*, second edition, §5.2. -/
def a3b4_fibreMap {k : Type u} [Field k] {X : Scheme.{u}}
    {p : X ⟶ Spec (CommRingCat.of k)} {I : X.IdealSheafData} {D : A3b2Deformation k X p I}
    {K : X.IdealSheafData}
    (DV : A3b2Deformation k K.subscheme (K.subschemeι ≫ p) (I.comap K.subschemeι))
    (f : DV.M ⟶ D.M) (hL : f ≫ D.toLine = DV.toLine) (c : k) :
    pullback DV.toLine (a3b2_point k c) ⟶ pullback D.toLine (a3b2_point k c) :=
  pullback.map DV.toLine (a3b2_point k c) D.toLine (a3b2_point k c) f (𝟙 _) (𝟙 _)
    (by rw [hL, Category.comp_id]) (by rw [Category.id_comp, Category.comp_id])

example {k : Type u} [Field k] {X : Scheme.{u}} {p : X ⟶ Spec (CommRingCat.of k)}
    {I : X.IdealSheafData} {D : A3b2Deformation k X p I} {K : X.IdealSheafData}
    (DV : A3b2Deformation k K.subscheme (K.subschemeι ≫ p) (I.comap K.subschemeι))
    (f : DV.M ⟶ D.M) (hL : f ≫ D.toLine = DV.toLine) :
    a3b4_fibreMap DV f hL 0 = a3b2_zeroFibreMap DV f hL := rfl

/-- A fibre of a Noetherian family over a rational point of the line is Noetherian: it is a
closed subscheme.
Source: Mathlib, `LocallyOfFiniteType.isLocallyNoetherian` and `quasiCompact_iff_compactSpace`;
Hartshorne, *Algebraic Geometry*, II, Exercise 3.13. -/
theorem a3b4_fibre_isNoetherian {k : Type u} [Field k] {X : Scheme.{u}}
    {p : X ⟶ Spec (CommRingCat.of k)} {I : X.IdealSheafData} (D : A3b2Deformation k X p I)
    (c : k) (h : IsNoetherian D.M) :
    IsNoetherian (pullback D.toLine (a3b2_point k c) : Scheme.{u}) :=
  haveI : IsLocallyNoetherian (pullback D.toLine (a3b2_point k c) : Scheme.{u}) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.fst D.toLine (a3b2_point k c))
  haveI : CompactSpace (pullback D.toLine (a3b2_point k c) : Scheme.{u}) :=
    (quasiCompact_iff_compactSpace (pullback.fst D.toLine (a3b2_point k c))).1 inferInstance
  { toIsLocallyNoetherian := inferInstance, toCompactSpace := inferInstance }

/-- The projection of a family to the ambient scheme is affine: over an affine open its preimage
is identified with the spectrum of the extended Rees algebra by the chart.
Source: Fulton, *Intersection Theory*, second edition, §5.1, pp. 87–88; Mathlib,
`AlgebraicGeometry.IsAffineHom`. -/
instance a3b4_toX_isAffineHom {k : Type u} [Field k] {X : Scheme.{u}}
    {p : X ⟶ Spec (CommRingCat.of k)} {I : X.IdealSheafData} (D : A3b2Deformation k X p I) :
    IsAffineHom D.toX := by
  constructor
  intro U hU
  have : IsAffine (D.toX ⁻¹ᵁ U).toScheme :=
    IsAffine.of_isIso (D.chart ⟨U, hU⟩).hom
  exact this

/-! ## The diagonal -/

/-- The projection of the normal bundle of the diagonal to `Y` given by an identification with the
tangent bundle lies over `Spec k` compatibly with the projection to `Y ×ₖ Y`.
Source: `pullback.diagonal_fst`; the shape of `a3b3_tangentBundle_normalBundle`. -/
theorem a3b4_tangentProj_comp {k : Type u} [Field k] {Y : Scheme.{u}}
    (p : Y ⟶ Spec (CommRingCat.of k)) {H₁ : (a3b3_tangentDiagramMap p).Coequifibered}
    {H₂ : (a3b3_normalDiagramMap (pullback p p : Scheme.{u}) (a3b3_diagonalIdeal p)).Coequifibered}
    (eT : a3b3_tangentBundle p H₁ ≅
      a3b3_normalBundle (pullback p p : Scheme.{u}) (a3b3_diagonalIdeal p) H₂)
    (heT : eT.hom ≫ a3b3_normalBundleProj (pullback p p : Scheme.{u}) (a3b3_diagonalIdeal p) H₂ =
      a3b3_tangentBundleProj p H₁ ≫ pullback.diagonal p) :
    (eT.inv ≫ a3b3_tangentBundleProj p H₁) ≫ p =
      a3b3_normalBundleProj (pullback p p : Scheme.{u}) (a3b3_diagonalIdeal p) H₂ ≫
        pullback.fst p p ≫ p := by
  have h : a3b3_normalBundleProj (pullback p p : Scheme.{u}) (a3b3_diagonalIdeal p) H₂ =
      eT.inv ≫ a3b3_tangentBundleProj p H₁ ≫ pullback.diagonal p := by
    rw [← heT, Iso.inv_hom_id_assoc]
  rw [h]
  simp

end HodgeLean.Adapters
