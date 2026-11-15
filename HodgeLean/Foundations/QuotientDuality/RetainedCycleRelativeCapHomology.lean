import HodgeLean.Foundations.QuotientDuality.RetainedCycleCapWithOrientation
import HodgeLean.Foundations.QuotientDuality.RetainedCycleGradedCap

noncomputable section
open CategoryTheory Limits AlgebraicTopology AlgebraicTopology.Singular
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace HodgeLean.Foundations.QuotientDuality

/-- The actual ambient cap operation as a morphism of relative homology short complexes. -/
def retainedRelativeCapShortComplex (P : TopPair.{0}) (p q : ℕ)
    (φ : Simplicial.Cochain ℚ (TopCat.toSSet.obj P.fst) p)
    (hφ : Simplicial.coboundary ℚ p φ = 0) :
    ((relativeChainFunctor ℚ).obj P).sc (p + q) ⟶ ((relativeChainFunctor ℚ).obj P).sc q :=
  retainedGradedCapShortComplexMap ((relativeChainFunctor ℚ).obj P) p
    (fun j => retainedRelativeAmbientCapHom P p j φ)
    (fun j => retained_relative_ambient_cap_boundary P p j φ hφ) q

/-- The relative short-complex map retains the exact quotient cap operation. -/
theorem retained_relative_cap_short_complex_middle (P : TopPair.{0}) (p q : ℕ)
    (φ : Simplicial.Cochain ℚ (TopCat.toSSet.obj P.fst) p)
    (hφ : Simplicial.coboundary ℚ p φ = 0) :
    (retainedRelativeCapShortComplex P p q φ hφ).τ₂ = retainedRelativeAmbientCapHom P p q φ :=
  retained_graded_cap_short_complex_map_middle _ _ _ _ _

/-- Cap by an ambient cocycle on actual relative singular homology. -/
def retainedRelativeCapHomology (P : TopPair.{0}) (p q : ℕ)
    (φ : Simplicial.Cochain ℚ (TopCat.toSSet.obj P.fst) p)
    (hφ : Simplicial.coboundary ℚ p φ = 0) :
    RelativeHomology ℚ P (p + q) →ₗ[ℚ] RelativeHomology ℚ P q :=
  (ShortComplex.homologyMap (retainedRelativeCapShortComplex P p q φ hφ)).hom

/-- The relative homology cap map is induced by the constructed map on actual cycles. -/
theorem retained_relative_cap_homology_cycles (P : TopPair.{0}) (p q : ℕ)
    (φ : Simplicial.Cochain ℚ (TopCat.toSSet.obj P.fst) p)
    (hφ : Simplicial.coboundary ℚ p φ = 0) :
    ((relativeChainFunctor ℚ).obj P).homologyπ (p + q) ≫
      ModuleCat.ofHom (retainedRelativeCapHomology P p q φ hφ) =
    ShortComplex.cyclesMap (retainedRelativeCapShortComplex P p q φ hφ) ≫
      ((relativeChainFunctor ℚ).obj P).homologyπ q :=
  ShortComplex.homologyπ_naturality (retainedRelativeCapShortComplex P p q φ hφ)

/-- Projection of absolute cap equals cap of the actual relative homology projection. -/
theorem retained_relative_cap_homology_projection (P : TopPair.{0}) (p q : ℕ)
    (φ : Simplicial.Cochain ℚ (TopCat.toSSet.obj P.fst) p)
    (hφ : Simplicial.coboundary ℚ p φ = 0)
    (c : Homology ℚ P.fst (p + q)) :
    (relativeHomologyProjection ℚ P q).hom (Simplicial.capHomologyMap ℚ p q φ hφ c) =
      retainedRelativeCapHomology P p q φ hφ
        ((relativeHomologyProjection ℚ P (p + q)).hom c) := by
  let π := relativeChainProjection ℚ P
  let πN := (HomologicalComplex.shortComplexFunctor (ModuleCat ℚ) (ComplexShape.down ℕ)
    (p + q)).map π
  let πQ := (HomologicalComplex.shortComplexFunctor (ModuleCat ℚ) (ComplexShape.down ℕ) q).map π
  let A := Simplicial.capShortComplexHom ℚ p q φ hφ
  let R := retainedRelativeCapShortComplex P p q φ hφ
  have hm : (πN ≫ R).τ₂ = (A ≫ πQ).τ₂ := by
    change π.f (p + q) ≫ R.τ₂ = A.τ₂ ≫ π.f q
    rw [retained_relative_cap_short_complex_middle, Simplicial.capShortComplexHom_τ₂]
    exact retained_relative_projection_ambient_cap P p q φ
  have hh := retained_homology_map_eq_of_middle (πN ≫ R) (A ≫ πQ) hm
  rw [ShortComplex.homologyMap_comp, ShortComplex.homologyMap_comp] at hh
  exact (ConcreteCategory.congr_hom hh c).symm

/-- The specified orientation cap map has the actual relative projection formula on represented classes. -/
theorem retained_orientation_cap_relative_projection (P : TopPair.{0}) (p q : ℕ)
    (φ : Simplicial.Cocycle ℚ (TopCat.toSSet.obj P.fst) p)
    (c : Homology ℚ P.fst (p + q)) :
    (relativeHomologyProjection ℚ P q).hom
      (retainedCapWithOrientation P.fst p q c
        (HodgeLean.Foundations.Singular.cohomologyClass P.fst p φ)) =
    retainedRelativeCapHomology P p q φ.1 φ.2
      ((relativeHomologyProjection ℚ P (p + q)).hom c) := by
  exact (congrArg (relativeHomologyProjection ℚ P q).hom
    (retained_cap_with_orientation_on_class P.fst p q c φ)).trans
      (retained_relative_cap_homology_projection P p q φ.1 φ.2 c)

/-- Actual relative cap on homology commutes with restricting its support. -/
theorem retained_relative_cap_homology_support_inclusion
    (X : TopCat.{0}) (p q : ℕ) (φ : Simplicial.Cochain ℚ (TopCat.toSSet.obj X) p)
    (hφ : Simplicial.coboundary ℚ p φ = 0) {S T : Set X} (h : S ⊆ T)
    (c : RelativeHomology ℚ (TopPair.ofSubset Tᶜ) (p + q)) :
    relativeHomologyMap ℚ q (supportInclusionPairMap X h)
      (retainedRelativeCapHomology (TopPair.ofSubset Tᶜ) p q φ hφ c) =
    retainedRelativeCapHomology (TopPair.ofSubset Sᶜ) p q φ hφ
      (relativeHomologyMap ℚ (p + q) (supportInclusionPairMap X h) c) := by
  let f := (relativeChainFunctor ℚ).map (supportInclusionPairMap X h)
  let fN := (HomologicalComplex.shortComplexFunctor (ModuleCat ℚ) (ComplexShape.down ℕ)
    (p + q)).map f
  let fQ := (HomologicalComplex.shortComplexFunctor (ModuleCat ℚ) (ComplexShape.down ℕ) q).map f
  let A := retainedRelativeCapShortComplex (TopPair.ofSubset Tᶜ) p q φ hφ
  let R := retainedRelativeCapShortComplex (TopPair.ofSubset Sᶜ) p q φ hφ
  have hm : (A ≫ fQ).τ₂ = (fN ≫ R).τ₂ := by
    change A.τ₂ ≫ f.f q = f.f (p + q) ≫ R.τ₂
    rw [retained_relative_cap_short_complex_middle, retained_relative_cap_short_complex_middle]
    exact (retained_relative_ambient_cap_support_inclusion X p q φ h).symm
  have hh := retained_homology_map_eq_of_middle (A ≫ fQ) (fN ≫ R) hm
  rw [ShortComplex.homologyMap_comp, ShortComplex.homologyMap_comp] at hh
  exact ConcreteCategory.congr_hom hh c

end HodgeLean.Foundations.QuotientDuality
