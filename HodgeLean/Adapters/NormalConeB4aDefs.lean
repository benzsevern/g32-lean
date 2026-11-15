import HodgeLean.Adapters.NormalConeB4Defs

/-! # Analytic foundations: objects

Stage A3-B4a objects, used by the foundation statements of `NormalConeB4a.lean` and by the
specialization statements of stage A3-B4b (`NormalConeB4.lean`).

The line coordinate: `a3b4a_lineCoord` is the value of the coordinate `t` of the parameter line
`Spec ℂ[t]` at a complex point, the evaluation of the global section `t`. It is continuous
(`a3b4a_continuous_lineCoord`), it is `s` at the complex point of `t = s`
(`a3b4a_lineCoord_point`), and every complex point of the fibre of a scheme over the line at
`t = s` has coordinate `s` (`a3b4a_lineCoord_fibre`). So the fibre inclusions at `0` and `1` of
any family land in the level sets `t = 0` and `t = 1`.

Fibres of a closed subscheme: for a closed immersion `i : K ⟶ Z` over the line,
`a3b4a_fibreMap i h hK hi s` is the induced map of fibres over `t = s`; for the families of stage
A3-B2 it is `a3b4_fibreMap`. A fibre of a Noetherian scheme over a rational point of the line is
Noetherian (`a3b4a_fibre_isNoetherian`).

Maps of complex points compose (`a3b4a_anMap_comp`, `a3b4a_anMap_id`).

Maps of local pairs: `a3b4a_restrictPairMap F W S W' S'` is a continuous map `F` viewed as a map
`(W, W ∖ S) ⟶ (W', W' ∖ S')`, the pairs on which the upstream normal coclasses live.

No definition here chooses a witness from an open theorem.
-/

noncomputable section
namespace HodgeLean.Adapters
open CategoryTheory Limits AlgebraicGeometry AlgebraicTopology.Singular

/-- The maps of complex points compose.
Source: upstream `Point.map_comp_apply`. -/
theorem a3b4a_anMap_comp {Z Z' Z'' : Scheme.{0}} {q : Z ⟶ Spec (CommRingCat.of ℂ)}
    {q' : Z' ⟶ Spec (CommRingCat.of ℂ)} {q'' : Z'' ⟶ Spec (CommRingCat.of ℂ)}
    (g : Z ⟶ Z') (g' : Z' ⟶ Z'') (h : g ≫ q' = q) (h' : g' ≫ q'' = q')
    (h'' : (g ≫ g') ≫ q'' = q) (z : a3b4_an q) :
    a3b4_anMap g' h' (a3b4_anMap g h z) = a3b4_anMap (g ≫ g') h'' z := by
  simp only [a3b4_anMap, TopCat.hom_ofHom]
  change Point.map _ (Point.map _ z) = Point.map _ z
  rw [← Point.map_comp_apply]
  rfl

/-- The map of complex points of the identity is the identity.
Source: upstream `Point.map_id`. -/
theorem a3b4a_anMap_id {Z : Scheme.{0}} {q : Z ⟶ Spec (CommRingCat.of ℂ)} (h : 𝟙 Z ≫ q = q)
    (z : a3b4_an q) : a3b4_anMap (𝟙 Z) h z = z := by
  simp only [a3b4_anMap, TopCat.hom_ofHom]
  change Point.map _ z = z
  have : (Over.homMk (𝟙 Z) h : Over.mk q ⟶ Over.mk q) = 𝟙 _ := by ext; simp
  rw [this]
  rfl

/-! ## The line coordinate -/

/-- The coordinate `t` of the parameter line at a complex point: the evaluation of the global
section `t` of `Spec ℂ[t]`.
Source: Serre, *Géométrie algébrique et géométrie analytique*, Ann. Inst. Fourier 6 (1956), §2
(regular functions on the complex points); upstream `Point.evaluate`. -/
def a3b4a_lineCoord (z : a3b4_an (a3b2_lineToBase ℂ)) : ℂ :=
  Point.evaluate (X := Over.mk (a3b2_lineToBase ℂ)) ⊤
    ((Scheme.ΓSpecIso (CommRingCat.of (Polynomial ℂ))).inv.hom Polynomial.X) z

example (z : a3b4_an (a3b2_lineToBase ℂ)) : ℂ := a3b4a_lineCoord z

/-- The line coordinate is continuous for the analytic topology.
Source: upstream `ComplexPoint.continuous_evaluate_top`. -/
theorem a3b4a_continuous_lineCoord : Continuous a3b4a_lineCoord :=
  ComplexPoint.continuous_evaluate_top (X := Over.mk (a3b2_lineToBase ℂ)) _

/-- The rational point `t = s` of the line is a section of the structure map.
Source: Mathlib, `Polynomial.eval_C`. -/
theorem a3b4a_point_lineToBase (s : ℂ) :
    a3b2_point ℂ s ≫ a3b2_lineToBase ℂ = 𝟙 (Spec (CommRingCat.of ℂ)) := by
  rw [a3b2_point, a3b2_lineToBase, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  convert Spec.map_id (CommRingCat.of ℂ)
  ext a
  simp

/-- The line coordinate of the complex point `t = s` is `s`.
Source: upstream `ComplexPoint.evaluate_top_eq_appTop`; Mathlib,
`AlgebraicGeometry.Scheme.ΓSpecIso_inv_naturality`. -/
theorem a3b4a_lineCoord_point (s : ℂ) (z : a3b4_an (𝟙 (Spec (CommRingCat.of ℂ)))) :
    a3b4a_lineCoord (a3b4_anMap (q' := a3b2_lineToBase ℂ) (a3b2_point ℂ s)
      (a3b4a_point_lineToBase s) z) = s := by
  unfold a3b4a_lineCoord a3b4_anMap
  change Point.evaluate _ _ (Point.map _ z) = s
  rw [ComplexPoint.evaluate_top_eq_appTop]
  have hz : z.left = 𝟙 _ := by
    have := Over.w z
    simpa using this
  change (Scheme.ΓSpecIso _).hom ((z.left ≫ a3b2_point ℂ s).appTop _) = s
  rw [hz, Category.id_comp, a3b2_point]
  have := congrArg (fun φ => (CommRingCat.Hom.hom φ) Polynomial.X)
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (Polynomial.evalRingHom s)))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at this
  rw [← this]
  simp

/-- The second projection of a fibre over `t = s` lies over `ℂ` compatibly with the first.
Source: Mathlib, `CategoryTheory.Limits.pullback.condition`. -/
theorem a3b4a_fibre_snd {Z : Scheme.{0}} {q : Z ⟶ Spec (CommRingCat.of ℂ)}
    (h : Z ⟶ a3b2_line ℂ) (hq : h ≫ a3b2_lineToBase ℂ = q) (s : ℂ) :
    pullback.snd h (a3b2_point ℂ s) ≫ 𝟙 _ = pullback.fst h (a3b2_point ℂ s) ≫ q := by
  rw [← hq, pullback.condition_assoc, a3b4a_point_lineToBase]

/-- Compatibility with the fibre inclusions: every complex point of the fibre of a scheme over the
line at `t = s` has line coordinate `s`.
Source: upstream `Point.map_comp_apply`; `a3b4a_lineCoord_point`. -/
theorem a3b4a_lineCoord_fibre {Z : Scheme.{0}} {q : Z ⟶ Spec (CommRingCat.of ℂ)}
    (h : Z ⟶ a3b2_line ℂ) (hq : h ≫ a3b2_lineToBase ℂ = q) (s : ℂ)
    (w : a3b4_an (pullback.fst h (a3b2_point ℂ s) ≫ q)) :
    a3b4a_lineCoord (a3b4_anMap (q' := a3b2_lineToBase ℂ) h hq
      (a3b4_anMap (q' := q) (pullback.fst h (a3b2_point ℂ s)) rfl w)) = s := by
  have e1 : a3b4_anMap (q' := a3b2_lineToBase ℂ) h hq
      (a3b4_anMap (q' := q) (pullback.fst h (a3b2_point ℂ s)) rfl w) =
      a3b4_anMap (q' := a3b2_lineToBase ℂ) (a3b2_point ℂ s) (a3b4a_point_lineToBase s)
        (a3b4_anMap (q' := 𝟙 _) (pullback.snd h (a3b2_point ℂ s)) (a3b4a_fibre_snd h hq s) w) := by
    simp only [a3b4_anMap, TopCat.hom_ofHom]
    change Point.map _ (Point.map _ w) = Point.map _ (Point.map _ w)
    rw [← Point.map_comp_apply, ← Point.map_comp_apply]
    congr 1
    ext
    simp [pullback.condition]
  rw [e1, a3b4a_lineCoord_point]

/-! ## Fibres of closed subschemes -/

/-- A fibre of a Noetherian scheme over a rational point of the line is Noetherian: it is a
closed subscheme.
Source: Mathlib, `LocallyOfFiniteType.isLocallyNoetherian` and `quasiCompact_iff_compactSpace`;
Hartshorne, *Algebraic Geometry*, II, Exercise 3.13. -/
theorem a3b4a_fibre_isNoetherian {Z : Scheme.{0}} [IsNoetherian Z] (h : Z ⟶ a3b2_line ℂ)
    (s : ℂ) : IsNoetherian (pullback h (a3b2_point ℂ s) : Scheme.{0}) :=
  haveI : IsLocallyNoetherian (pullback h (a3b2_point ℂ s) : Scheme.{0}) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.fst h (a3b2_point ℂ s))
  haveI : CompactSpace (pullback h (a3b2_point ℂ s) : Scheme.{0}) :=
    (quasiCompact_iff_compactSpace (pullback.fst h (a3b2_point ℂ s))).1 inferInstance
  { toIsLocallyNoetherian := inferInstance, toCompactSpace := inferInstance }

/-- The map of fibres over `t = s` induced by a morphism `i : K ⟶ Z` over the line.
Source: Fulton, *Intersection Theory*, second edition, §§1.7 and 10.1 (the fibre `K_s = K ×_𝔸¹ s`
of a family over a curve). -/
def a3b4a_fibreMap {K Z : Scheme.{0}} (i : K ⟶ Z) (h : Z ⟶ a3b2_line ℂ)
    (hK : K ⟶ a3b2_line ℂ) (hi : i ≫ h = hK) (s : ℂ) :
    pullback hK (a3b2_point ℂ s) ⟶ pullback h (a3b2_point ℂ s) :=
  pullback.map hK (a3b2_point ℂ s) h (a3b2_point ℂ s) i (𝟙 _) (𝟙 _)
    (by rw [hi, Category.comp_id]) (by rw [Category.id_comp, Category.comp_id])

/-- For the families of stage A3-B2 the fibre map is `a3b4_fibreMap`.
Source: definitions. -/
example {X : Scheme.{0}} {p : X ⟶ Spec (CommRingCat.of ℂ)}
    {I : X.IdealSheafData} {D : A3b2Deformation ℂ X p I} {K : X.IdealSheafData}
    (DV : A3b2Deformation ℂ K.subscheme (K.subschemeι ≫ p) (I.comap K.subschemeι))
    (f : DV.M ⟶ D.M) (hL : f ≫ D.toLine = DV.toLine) (s : ℂ) :
    a3b4a_fibreMap f D.toLine DV.toLine hL s = a3b4_fibreMap DV f hL s := rfl

/-! ## Maps of local pairs -/

/-- A continuous map as a map of local pairs `(W, W ∖ S) ⟶ (W', W' ∖ S')`, given that it maps
`W` into `W'` and that, on `W`, the preimage of `S'` lies in `S`.
Source: Hatcher, *Algebraic Topology*, §2.1 (maps of pairs); upstream `TopPair.ofSubsetHom` and
`neighborhoodSupportComplementPair`. -/
def a3b4a_restrictPairMap {M M' : Type} [TopologicalSpace M] [TopologicalSpace M'] (F : C(M, M'))
    (W S : Set M) (W' S' : Set M') (hW : ∀ y ∈ W, F y ∈ W') (hS : ∀ y ∈ W, F y ∈ S' → y ∈ S) :
    neighborhoodSupportComplementPair W S ⟶ neighborhoodSupportComplementPair W' S' :=
  TopPair.ofSubsetHom (TopCat.ofHom ⟨fun w => ⟨F w.1, hW _ w.2⟩, by fun_prop⟩)
    fun a ha h => ha (hS _ a.2 h)

example {M : Type} [TopologicalSpace M] (W S : Set M) :
    neighborhoodSupportComplementPair W S ⟶ neighborhoodSupportComplementPair W S :=
  a3b4a_restrictPairMap (ContinuousMap.id M) W S W S (fun _ h => h) fun _ _ h => h

end HodgeLean.Adapters
