import HodgeLean.Foundations.QuotientDuality.ProperCycleChartOrientationComparison
import HodgeConjecture.Definitions.AlgebraicTopology.LocalHomology.NormalProjectionCoclass

/-! # Actual local homology coordinates for original partial complex charts -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicTopology AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- The original partial chart gives the actual isomorphism between its source and target neighborhood point-complement pairs.
Source: Hatcher, Algebraic Topology, section 2.2, point excision in chart neighborhoods.
HC no distance; AV milestone no distance. -/
def properCycle_chart_point_pair_iso
    (d : ℕ) {M : TopCat.{0}} (e : OpenPartialHomeomorph M (Fin d → ℂ)) (x : M) (hx : x ∈ e.source) :
    neighborhoodPointComplementPair e.source x ≅ neighborhoodPointComplementPair e.target (e x) :=
  TopPair.isoOfSubset (X := TopCat.of e.source) (Y := TopCat.of e.target) e.toHomeomorphSourceTarget (by
    intro z
    change (e z.1 ≠ e x) ↔ z.1 ≠ x
    apply not_congr
    constructor
    · intro h
      exact e.injOn z.2 hx h
    · intro h
      exact congrArg e h)

/-- The original inverse chart point map factors through the actual source-neighborhood point map and the inverse chart pair isomorphism.
Source: Hatcher, Algebraic Topology, section 2.2, natural point excision in complex chart neighborhoods.
HC no distance; AV milestone no distance. -/
lemma properCycle_chart_inverse_point_pair_factorization
    (d : ℕ) {M : TopCat.{0}} (e : OpenPartialHomeomorph M (Fin d → ℂ)) (x : M) (hx : x ∈ e.source) :
    chartTargetInverseAtSourcePairMap d e x =
      (properCycle_chart_point_pair_iso d e x hx).inv ≫ neighborhoodPointComplementPairMap e.source x := by
  ext z : 2 <;> rfl

/-- Actual source and target point excision give the original partial chart coordinate isomorphism on ambient local homology in every degree.
Source: Hatcher, Algebraic Topology, section 2.2, excision in source and target chart neighborhoods.
HC no distance; AV milestone no distance. -/
def properCycle_chart_local_homology_coordinates
    (d : ℕ) {M : TopCat.{0}} [T1Space M]
    (e : OpenPartialHomeomorph M (Fin d → ℂ)) (x : M) (hx : x ∈ e.source) (n : ℕ) :
    orientationGroup M n x ≅ orientationGroup (TopCat.of (Fin d → ℂ)) n (e x) :=
  (neighborhoodPointComplementRelativeHomologyIso e.source x e.open_source hx n).symm ≪≫
    (HomologicalComplex.homologyFunctor (ModuleCat.{0} ℚ) (ComplexShape.down ℕ) n).mapIso
      ((relativeChainFunctor ℚ).mapIso (properCycle_chart_point_pair_iso d e x hx)) ≪≫
    neighborhoodPointComplementRelativeHomologyIso e.target (e x) e.open_target (e.map_source hx) n

/-- Original partial chart coordinates send the actual inverse chart point map to the literal target-neighborhood point inclusion on homology.
Source: Hatcher, Algebraic Topology, section 2.2, naturality of point excision.
HC no distance; AV milestone no distance. -/
lemma properCycle_chart_local_coordinates_inverse
    (d : ℕ) {M : TopCat.{0}} [T1Space M]
    (e : OpenPartialHomeomorph M (Fin d → ℂ)) (x : M) (hx : x ∈ e.source) (n : ℕ) :
    HomologicalComplex.homologyMap ((relativeChainFunctor ℚ).map
        (chartTargetInverseAtSourcePairMap d e x)) n ≫
      (properCycle_chart_local_homology_coordinates d e x hx n).hom =
        HomologicalComplex.homologyMap ((relativeChainFunctor ℚ).map
          (neighborhoodPointComplementPairMap e.target (e x))) n := by
  let eS := neighborhoodPointComplementRelativeHomologyIso e.source x e.open_source hx n
  let eT := neighborhoodPointComplementRelativeHomologyIso e.target (e x) e.open_target (e.map_source hx) n
  let eP := (HomologicalComplex.homologyFunctor (ModuleCat.{0} ℚ) (ComplexShape.down ℕ) n).mapIso
    ((relativeChainFunctor ℚ).mapIso (properCycle_chart_point_pair_iso d e x hx))
  rw [properCycle_chart_inverse_point_pair_factorization d e x hx,
    Functor.map_comp, HomologicalComplex.homologyMap_comp]
  change (eP.inv ≫ eS.hom) ≫ (eS.inv ≫ eP.hom ≫ eT.hom) = eT.hom
  simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id_assoc]

/-- Actual partial-chart local homology coordinates send the original compressed chart class to the original translated standard complex class with its full normalization.
Source: Hatcher, Algebraic Topology, section 3.3; radialTargetPointPairMap_normalization, original radial chart normalization.
HC no distance; AV milestone no distance. -/
lemma properCycle_partial_chart_local_class_normalization
    (d : ℕ) {M : TopCat.{0}} [T1Space M]
    (e : OpenPartialHomeomorph M (Fin d → ℂ)) (x : M) (hx : x ∈ e.source) :
    (properCycle_chart_local_homology_coordinates d e x hx (2 * d)).hom.hom
        (localClassOfChart d e x hx) =
      relativeHomologyMap ℚ (2 * d) (translationPointComplementPairMap (Fin d → ℂ) (e x))
        (standardComplexLocalClass ℚ d) := by
  let Q := radialTargetPointPairMap d e.target (e x) (chartRadius d e x hx)
    (chartRadius_pos d e x hx) (ball_chartRadius_subset d e x hx) 0 (e x)
    (OpenPartialHomeomorph.univBall_apply_zero _ _)
  have hQ : Q ≫ chartTargetInverseAtSourcePairMap d e x = chartModelEmbeddingPair d e x hx :=
    radialTargetPointPairMap_chartTargetInverseAtSource d e x hx
  change (properCycle_chart_local_homology_coordinates d e x hx (2 * d)).hom.hom
    (relativeHomologyMap ℚ (2 * d) (chartModelEmbeddingPair d e x hx) (standardComplexLocalClass ℚ d)) = _
  rw [← hQ, relativeHomologyMap_comp, LinearMap.comp_apply]
  have h := ConcreteCategory.congr_hom (properCycle_chart_local_coordinates_inverse d e x hx (2 * d))
    (relativeHomologyMap ℚ (2 * d) Q (standardComplexLocalClass ℚ d))
  exact h.trans (radialTargetPointPairMap_normalization d e.target (e x) (chartRadius d e x hx)
    (chartRadius_pos d e x hx) (ball_chartRadius_subset d e x hx) 0 (e x)
    (OpenPartialHomeomorph.univBall_apply_zero _ _))

/-- The original restricted chart on any source subset gives its literal map from the neighborhood point-complement pair to the full complex point pair.
Source: Hatcher, Algebraic Topology, section 2.2, point maps in smaller chart neighborhoods.
HC no distance; AV milestone no distance. -/
def properCycle_restricted_chart_point_pair_map
    (d : ℕ) {M : TopCat.{0}} (e : OpenPartialHomeomorph M (Fin d → ℂ)) (x : M) (hx : x ∈ e.source)
    (W : Set M) (hW : W ⊆ e.source) :
    neighborhoodPointComplementPair W x ⟶ pointComplementPair (e x) :=
  TopPair.ofSubsetHom
    (TopCat.ofHom ⟨fun w => e w.1, (e.continuousOn.mono hW).domRestrict⟩)
    (fun w hw h => hw (e.injOn (hW w.2) hx h))

/-- The actual restricted chart point map agrees on homology with original ambient point inclusion followed by the constructed chart coordinates.
Source: Hatcher, Algebraic Topology, section 2.2, naturality of neighborhood point excision.
HC no distance; AV milestone no distance. -/
lemma properCycle_restricted_chart_local_coordinates
    (d : ℕ) {M : TopCat.{0}} [T1Space M]
    (e : OpenPartialHomeomorph M (Fin d → ℂ)) (x : M) (hx : x ∈ e.source)
    (W : Set M) (hW : W ⊆ e.source) (n : ℕ) :
    HomologicalComplex.homologyMap ((relativeChainFunctor ℚ).map
        (neighborhoodPointComplementPairMap W x)) n ≫
      (properCycle_chart_local_homology_coordinates d e x hx n).hom =
        HomologicalComplex.homologyMap ((relativeChainFunctor ℚ).map
          (properCycle_restricted_chart_point_pair_map d e x hx W hW)) n := by
  let I : neighborhoodPointComplementPair W x ⟶ neighborhoodPointComplementPair e.source x :=
    neighborhoodSupportInclusionPairMap hW {x}
  let eS := neighborhoodPointComplementRelativeHomologyIso e.source x e.open_source hx n
  let eT := neighborhoodPointComplementRelativeHomologyIso e.target (e x) e.open_target (e.map_source hx) n
  let eP := (HomologicalComplex.homologyFunctor (ModuleCat.{0} ℚ) (ComplexShape.down ℕ) n).mapIso
    ((relativeChainFunctor ℚ).mapIso (properCycle_chart_point_pair_iso d e x hx))
  let J := HomologicalComplex.homologyMap ((relativeChainFunctor ℚ).map I) n
  have hi : I ≫ neighborhoodPointComplementPairMap e.source x = neighborhoodPointComplementPairMap W x := by
    ext z : 2 <;> rfl
  have hf : I ≫ (properCycle_chart_point_pair_iso d e x hx).hom ≫
      neighborhoodPointComplementPairMap e.target (e x) =
        properCycle_restricted_chart_point_pair_map d e x hx W hW := by
    ext z : 2 <;> rfl
  rw [← hi, ← hf]
  simp only [Functor.map_comp, HomologicalComplex.homologyMap_comp]
  change (J ≫ eS.hom) ≫ (eS.inv ≫ eP.hom ≫ eT.hom) = J ≫ eP.hom ≫ eT.hom
  simp only [Category.assoc, Iso.hom_inv_id_assoc]

/-- Restricting the original compressed chart orientation to any actual smaller open neighborhood and applying its literal chart point map retains the exact translated standard normalization.
Source: Hatcher, Algebraic Topology, section 3.3, normalized local orientations and point excision.
HC no distance; AV milestone no distance. -/
lemma properCycle_restricted_chart_local_class_normalization
    (d : ℕ) {M : TopCat.{0}} [T1Space M]
    (e : OpenPartialHomeomorph M (Fin d → ℂ)) (x : M) (hx : x ∈ e.source)
    (W : Set M) (hW : W ⊆ e.source) (hWo : IsOpen W) (hxW : x ∈ W) :
    relativeHomologyMap ℚ (2 * d) (properCycle_restricted_chart_point_pair_map d e x hx W hW)
        ((neighborhoodPointComplementRelativeHomologyIso W x hWo hxW (2 * d)).inv.hom
          (localClassOfChart d e x hx)) =
      relativeHomologyMap ℚ (2 * d) (translationPointComplementPairMap (Fin d → ℂ) (e x))
        (standardComplexLocalClass ℚ d) := by
  let eW := neighborhoodPointComplementRelativeHomologyIso W x hWo hxW (2 * d)
  let c := localClassOfChart d e x hx
  have h := ConcreteCategory.congr_hom
    (properCycle_restricted_chart_local_coordinates d (M := M) e x hx W hW (2 * d)) (eW.inv.hom c)
  change (properCycle_chart_local_homology_coordinates d e x hx (2 * d)).hom.hom
      (eW.hom.hom (eW.inv.hom c)) =
    relativeHomologyMap ℚ (2 * d) (properCycle_restricted_chart_point_pair_map d e x hx W hW)
      (eW.inv.hom c) at h
  rw [eW.inv_hom_id_apply] at h
  exact h.symm.trans (properCycle_partial_chart_local_class_normalization d (M := M) e x hx)

end HodgeLean.Foundations.QuotientDuality
