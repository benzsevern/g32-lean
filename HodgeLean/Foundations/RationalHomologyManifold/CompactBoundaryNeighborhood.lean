import HodgeLean.Foundations.RationalHomologyManifold.RelativeBoundaryNeighborhood
import HodgeLean.Foundations.RationalHomologyManifold.RelativeSubdivisionBoundaryDetection
import HodgeLean.Foundations.RationalHomologyManifold.OrientationDimensionBound

/-! Actual ambient primitives near compact supports from intrinsic homology bounds.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicTopology.Singular HodgeLean.Foundations.QuotientDuality
namespace HodgeLean.Foundations.RationalHomologyManifold

/-- Above the orientation dimension, each actual relative cycle along a compact set is an ambient boundary on a neighborhood.
Source: Bredon, Sheaf Theory, second edition, V.16 and VI.12; intrinsic support bounds and relative-chain primitives.
HC no distance; AV milestone no distance.
-/
theorem compact_relative_cycle_ambient_boundary_above_orientation (X : TopCat.{0}) [T2Space X]
    (t : FiniteTriangulation X) (n : ℕ) (o : LocalRationalOrientation X n)
    (K : Set X) (hK : IsCompact K) (i : ℕ) (hi : n < i)
    (z : (SingularChainComplex ℚ X).X i)
    (hz : (((relativeChainFunctor ℚ).obj (TopPair.ofSubset (X := X) Kᶜ)).sc i).g.hom
      (((relativeChainProjection ℚ (TopPair.ofSubset (X := X) Kᶜ)).f i).hom z) = 0) :
    ∃ (b : (SingularChainComplex ℚ X).X (i + 1)) (V : TopologicalSpace.Opens X), K ⊆ V ∧
      (relativeChainProjection ℚ (TopPair.ofSubset (X := X) (V : Set X)ᶜ)).f i z =
        (relativeChainProjection ℚ (TopPair.ofSubset (X := X) (V : Set X)ᶜ)).f i
          ((SingularChainComplex ℚ X).d (i + 1) i b) := by
  letI := relativeHomology_above_orientation X t n o K hK i hi
  apply relativeCycleClass_zero_ambient_boundary_near_set X i K z hz
  exact @Subsingleton.elim (RelativeHomology ℚ (TopPair.ofSubset (X := X) Kᶜ) i)
    (relativeHomology_above_orientation X t n o K hK i hi) _ _

#print axioms compact_relative_cycle_ambient_boundary_above_orientation
/-- In the orientation degree, pointwise vanishing detects an actual ambient primitive near a compact support.
Source: Bredon, Sheaf Theory, second edition, V.9, V.16 and VI.12; compact point detection and relative boundaries.
HC no distance; AV milestone no distance.
-/
theorem compact_pointwise_zero_cycle_ambient_boundary (X : TopCat.{0}) [T2Space X]
    (t : FiniteTriangulation X) (n : ℕ) (o : LocalRationalOrientation X n)
    (K : Set X) (hK : IsCompact K) (z : (SingularChainComplex ℚ X).X n)
    (hz : (((relativeChainFunctor ℚ).obj (TopPair.ofSubset (X := X) Kᶜ)).sc n).g.hom
      (((relativeChainProjection ℚ (TopPair.ofSubset (X := X) Kᶜ)).f n).hom z) = 0)
    (hpoint : ∀ (x : X) (hx : x ∈ K), relativeHomologyMap ℚ n
      (supportInclusionPairMap X (Set.singleton_subset_iff.mpr hx))
      ((((relativeChainFunctor ℚ).obj (TopPair.ofSubset (X := X) Kᶜ)).sc n).moduleCatHomologyClass
        ⟨((relativeChainProjection ℚ (TopPair.ofSubset (X := X) Kᶜ)).f n).hom z, hz⟩) = 0) :
    ∃ (b : (SingularChainComplex ℚ X).X (n + 1)) (V : TopologicalSpace.Opens X), K ⊆ V ∧
      (relativeChainProjection ℚ (TopPair.ofSubset (X := X) (V : Set X)ᶜ)).f n z =
        (relativeChainProjection ℚ (TopPair.ofSubset (X := X) (V : Set X)ᶜ)).f n
          ((SingularChainComplex ℚ X).d (n + 1) n b) := by
  apply relativeCycleClass_zero_ambient_boundary_near_set X n K z hz
  apply finiteTriangulation_compact_detection X t n o K hK
  exact hpoint

#print axioms compact_pointwise_zero_cycle_ambient_boundary
/-- Pointwise subdivided boundary witnesses yield one actual ambient primitive near a compact support.
Source: Bredon, Sheaf Theory, second edition, V.9, V.16 and VI.12; compact point detection and subdivision invariance.
HC no distance; AV milestone no distance.
-/
theorem compact_subdivided_point_boundaries_ambient_primitive (X : TopCat.{0}) [T2Space X]
    (t : FiniteTriangulation X) (n : ℕ) (o : LocalRationalOrientation X n)
    (K : Set X) (hK : IsCompact K) (z : (SingularChainComplex ℚ X).X n)
    (hz : (((relativeChainFunctor ℚ).obj (TopPair.ofSubset (X := X) Kᶜ)).sc n).g.hom
      (((relativeChainProjection ℚ (TopPair.ofSubset (X := X) Kᶜ)).f n).hom z) = 0)
    (hpoint : ∀ (x : X), x ∈ K → ∃ (r : ℕ)
      (b : ((relativeChainFunctor ℚ).obj (pointComplementPair x)).X (n + 1)),
      ((relativeChainFunctor ℚ).obj (pointComplementPair x)).d (n + 1) n b =
        (relativeChainProjection ℚ (pointComplementPair x)).f n
          ((rationalSubdivisionIterate X r).f n z)) :
    ∃ (b : (SingularChainComplex ℚ X).X (n + 1)) (V : TopologicalSpace.Opens X), K ⊆ V ∧
      (relativeChainProjection ℚ (TopPair.ofSubset (X := X) (V : Set X)ᶜ)).f n z =
        (relativeChainProjection ℚ (TopPair.ofSubset (X := X) (V : Set X)ᶜ)).f n
          ((SingularChainComplex ℚ X).d (n + 1) n b) := by
  apply compact_pointwise_zero_cycle_ambient_boundary X t n o K hK z hz
  intro x hx
  obtain ⟨r, b, hb⟩ := hpoint x hx
  let P := TopPair.ofSubset (X := X) Kᶜ
  let Q := pointComplementPair x
  let C := (relativeChainFunctor ℚ).obj P
  let D := (relativeChainFunctor ℚ).obj Q
  let a := supportInclusionPairMap X (Set.singleton_subset_iff.mpr hx)
  let φ := (relativeChainFunctor ℚ).map a
  let F := (HomologicalComplex.shortComplexFunctor (ModuleCat ℚ) (ComplexShape.down ℕ) n).map φ
  let ξ : LinearMap.ker (C.sc n).g.hom :=
    ⟨((relativeChainProjection ℚ P).f n).hom z, hz⟩
  have hp := TopPair.Homotopy.relativeChainProjection_naturality (R := ℚ) a
  change relativeChainProjection ℚ P ≫ φ =
    (((AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{0} ℚ)).obj
      (ModuleCat.of ℚ ℚ)).map (𝟙 X)) ≫ relativeChainProjection ℚ Q at hp
  simp only [CategoryTheory.Functor.map_id, Category.id_comp] at hp
  have hv := ConcreteCategory.congr_hom (congrArg (fun f => f.f n) hp) z
  change φ.f n ((relativeChainProjection ℚ P).f n z) =
    (relativeChainProjection ℚ Q).f n z at hv
  have hzQ : (D.sc n).g.hom (((relativeChainProjection ℚ Q).f n).hom z) = 0 := by
    have hc := (ShortComplex.moduleCatCycleMap F ξ).property
    change (D.sc n).g.hom (φ.f n ((relativeChainProjection ℚ P).f n z)) = 0 at hc
    rw [hv] at hc
    exact hc
  have hzero := relativeCycleClass_zero_of_subdivided_boundary Q r n z hzQ b hb
  change (ShortComplex.homologyMap F).hom ((C.sc n).moduleCatHomologyClass ξ) = 0
  rw [ShortComplex.moduleCatHomologyClass_naturality]
  calc
    _ = (D.sc n).moduleCatHomologyClass
        ⟨((relativeChainProjection ℚ Q).f n).hom z, hzQ⟩ := by
      apply congrArg (D.sc n).moduleCatHomologyClass
      exact Subtype.ext hv
    _ = 0 := hzero

#print axioms compact_subdivided_point_boundaries_ambient_primitive
end HodgeLean.Foundations.RationalHomologyManifold
