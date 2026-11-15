import HodgeLean.Foundations.RationalHomologyManifold.AmbientSubdivisionBoundary
import HodgeLean.Foundations.RationalHomologyManifold.CompactSubdivisionEquality

/-! Actual relative-cycle representatives of subdivision sheaf cycles along compact supports.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicTopology.Singular
namespace HodgeLean.Foundations.RationalHomologyManifold

/-- A positive-degree ambient sheaf cycle has an actual relative-cycle representative along a compact set after one finite subdivision.
Source: Bredon, Sheaf Theory, second edition, VI.12; compact finite-stage detection of supported cycles.
HC no distance; AV milestone no distance.
-/
theorem compact_ambient_sheaf_cycle_relative_representative (X : TopCat.{0}) (n m : ℕ)
    (U : Opens X) (K : Set X) (hK : IsCompact K) (hKU : K ⊆ U)
    (z : (SingularChainComplex ℚ X).X (n + 1))
    (hs : (((subdivisionLimitSheafComplex X).d (n + 1) n).hom.app (Opposite.op U))
      ((subdivisionAmbientSectionMap X (n + 1) U m).hom z) = 0) :
    ∃ R : ℕ, (((relativeChainFunctor ℚ).obj (TopPair.ofSubset (X := X) Kᶜ)).sc (n + 1)).g.hom
      (((relativeChainProjection ℚ (TopPair.ofSubset (X := X) Kᶜ)).f (n + 1)).hom
        ((rationalSubdivisionIterate X R).f (n + 1) z)) = 0 := by
  have hb := ConcreteCategory.congr_hom (subdivisionAmbientSectionMap_boundary X n m U) z
  change (((subdivisionLimitSheafComplex X).d (n + 1) n).hom.app (Opposite.op U))
      ((subdivisionAmbientSectionMap X (n + 1) U m).hom z) =
    (subdivisionAmbientSectionMap X n U m).hom ((SingularChainComplex ℚ X).d (n + 1) n z) at hb
  have hEq : (subdivisionAmbientSectionMap X n U m).hom
      ((SingularChainComplex ℚ X).d (n + 1) n z) =
    (subdivisionAmbientSectionMap X n U m).hom 0 := by rw [← hb, hs, map_zero]
  obtain ⟨N, hNU, R, hKN, he⟩ := subdivisionAmbientSection_eq_near_compact X n m U
    ((SingularChainComplex ℚ X).d (n + 1) n z) 0 hEq K hK hKU
  let zR := (rationalSubdivisionIterate X R).f (n + 1) z
  let P := TopPair.ofSubset (X := X) (N : Set X)ᶜ
  let Q := TopPair.ofSubset (X := X) Kᶜ
  have hd := ConcreteCategory.congr_hom ((rationalSubdivisionIterate X R).comm (n + 1) n) z
  change (SingularChainComplex ℚ X).d (n + 1) n zR =
    (rationalSubdivisionIterate X R).f n ((SingularChainComplex ℚ X).d (n + 1) n z) at hd
  have hP : (relativeChainProjection ℚ P).f n
      ((SingularChainComplex ℚ X).d (n + 1) n zR) = 0 := by
    rw [hd, he, map_zero, map_zero]
  let f := supportInclusionPairMap X hKN
  let φ := (relativeChainFunctor ℚ).map f
  have hp := TopPair.Homotopy.relativeChainProjection_naturality (R := ℚ) f
  change relativeChainProjection ℚ P ≫ φ =
    (((AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{0} ℚ)).obj
      (ModuleCat.of ℚ ℚ)).map (𝟙 X)) ≫ relativeChainProjection ℚ Q at hp
  simp only [CategoryTheory.Functor.map_id, Category.id_comp] at hp
  have hq := ConcreteCategory.congr_hom (congrArg (fun f => f.f n) hp)
    ((SingularChainComplex ℚ X).d (n + 1) n zR)
  change φ.f n ((relativeChainProjection ℚ P).f n
      ((SingularChainComplex ℚ X).d (n + 1) n zR)) =
    (relativeChainProjection ℚ Q).f n ((SingularChainComplex ℚ X).d (n + 1) n zR) at hq
  rw [hP, map_zero] at hq
  have hrel := ConcreteCategory.congr_hom
    ((relativeChainProjection ℚ Q).comm (n + 1) n) zR
  change ((relativeChainFunctor ℚ).obj Q).d (n + 1) n
      ((relativeChainProjection ℚ Q).f (n + 1) zR) =
    (relativeChainProjection ℚ Q).f n ((SingularChainComplex ℚ X).d (n + 1) n zR) at hrel
  refine ⟨R, ?_⟩
  change (((relativeChainFunctor ℚ).obj Q).d (n + 1)
    ((ComplexShape.down ℕ).next (n + 1))).hom
      (((relativeChainProjection ℚ Q).f (n + 1)).hom zR) = 0
  rw [ChainComplex.next_nat_succ]
  exact hrel.trans hq.symm

#print axioms compact_ambient_sheaf_cycle_relative_representative
end HodgeLean.Foundations.RationalHomologyManifold
