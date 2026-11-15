import HodgeLean.RealDefs.Port.AlgebraicTopology.LocalHomology.EuclideanNeighborhoodOrientation

noncomputable section
namespace HodgeLean.Foundations.Program
open CategoryTheory CategoryTheory.Limits AlgebraicTopology.Singular Convexity
open scoped Simplicial
variable (R : Type) [CommRing R]

set_option backward.isDefEq.respectTransparency false in
lemma b6m_standardOrientationBallFace_projection (n : ℕ) (i : Fin (n + 2)) :
    standardAmbientFaceChain R n i ≫
      (relativeChainProjection R (standardOrientationBallPair (n + 1))).f n = 0 := by
  let σ := ((standardOrientationBallPair (n + 1)).snd.toSSetObjEquiv (.op ⦋n⦌)).symm
    (standardOrientationBallFaceMap n i)
  have hσ :
      (TopCat.toSSet.map (standardOrientationBallPair (n + 1)).map).app _ σ =
        (TopCat.toSSet.obj (puncturedPair ℝ (n + 1)).fst).δ i
          (standardSingularSimplex (n + 1)) := by
    apply ((standardOrientationBallPair (n + 1)).fst.toSSetObjEquiv _).injective
    ext t
    rfl
  exact iota_subspace_relativeChainProjection R (standardOrientationBallPair (n + 1)) σ

set_option backward.isDefEq.respectTransparency false in
def b6m_standardOrientationBallChain (d : ℕ) :
    ModuleCat.of R R ⟶ ((relativeChainFunctor R).obj (standardOrientationBallPair d)).X d :=
  standardAmbientSimplexChain R d ≫
    (relativeChainProjection R (standardOrientationBallPair d)).f d

set_option backward.isDefEq.respectTransparency false in
lemma b6m_standardOrientationBallChain_boundary (d : ℕ) :
    b6m_standardOrientationBallChain R d ≫
      ((relativeChainFunctor R).obj (standardOrientationBallPair d)).d
        d ((ComplexShape.down ℕ).next d) = 0 := by
  cases d with
  | zero => simp
  | succ n =>
    rw [ChainComplex.next_nat_succ, b6m_standardOrientationBallChain, Category.assoc,
      (relativeChainProjection R (standardOrientationBallPair (n + 1))).comm,
      ← Category.assoc]
    change (standardAmbientSimplexChain R (n + 1) ≫
      ((chainPairFunctor R).obj (puncturedPair ℝ (n + 1))).right.d (n + 1) n) ≫ _ = 0
    rw [standardAmbientSimplexChain_boundary, Preadditive.sum_comp]
    apply Finset.sum_eq_zero
    intro i _
    rw [Preadditive.zsmul_comp, b6m_standardOrientationBallFace_projection R]
    simp

set_option backward.isDefEq.respectTransparency false in
def b6m_standardOrientationBallCycle (d : ℕ) :
    ModuleCat.of R R ⟶
      ((relativeChainFunctor R).obj (standardOrientationBallPair d)).cycles d :=
  ((relativeChainFunctor R).obj (standardOrientationBallPair d)).liftCycles
    (b6m_standardOrientationBallChain R d) ((ComplexShape.down ℕ).next d) rfl
    (b6m_standardOrientationBallChain_boundary R d)

set_option backward.isDefEq.respectTransparency false in
def b6m_standardOrientationBallClass (d : ℕ) :
    RelativeHomology R (standardOrientationBallPair d) d :=
  ((b6m_standardOrientationBallCycle R d ≫
    ((relativeChainFunctor R).obj (standardOrientationBallPair d)).homologyπ d).hom) 1

set_option backward.isDefEq.respectTransparency false in
lemma b6m_standardOrientationBallCycle_restrict_zero (d : ℕ) :
    b6m_standardOrientationBallCycle R d ≫ HomologicalComplex.cyclesMap
      ((relativeChainFunctor R).map
        (standardOrientationBallPointMap d 0 (zero_mem_standardOrientationBall d))) d =
      standardLocalCycle R d := by
  apply (cancel_mono ((standardLocalRelativeChainComplex R d).iCycles d)).mp
  rw [Category.assoc, HomologicalComplex.cyclesMap_i, ← Category.assoc,
    b6m_standardOrientationBallCycle, HomologicalComplex.liftCycles_i,
    standardLocalCycle_inclusion, b6m_standardOrientationBallChain, Category.assoc]
  have h := congrArg (fun f => f.f d)
    (relativeChainProjection_supportInclusion R (TopCat.of (Fin d → ℝ))
      (Set.singleton_subset_iff.mpr (zero_mem_standardOrientationBall d)))
  exact congrArg (fun f => standardAmbientSimplexChain R d ≫ f) h

set_option backward.isDefEq.respectTransparency false in
theorem b6m_standardOrientationBallClass_restrict_zero (d : ℕ) :
    relativeHomologyMap R d
      (standardOrientationBallPointMap d 0 (zero_mem_standardOrientationBall d))
      (b6m_standardOrientationBallClass R d) = standardLocalClass R d := by
  have hmor : b6m_standardOrientationBallCycle R d ≫
      ((relativeChainFunctor R).obj (standardOrientationBallPair d)).homologyπ d ≫
      HomologicalComplex.homologyMap ((relativeChainFunctor R).map
        (standardOrientationBallPointMap d 0 (zero_mem_standardOrientationBall d))) d =
      standardLocalCycle R d ≫ (standardLocalRelativeChainComplex R d).homologyπ d := by
    rw [HomologicalComplex.homologyπ_naturality, ← Category.assoc,
      b6m_standardOrientationBallCycle_restrict_zero R]
  exact ConcreteCategory.congr_hom hmor 1

set_option backward.isDefEq.respectTransparency false in
theorem b6m_standardOrientationBallClass_restrict (d : ℕ) (y : Fin d → ℝ)
    (hy : y ∈ standardOrientationBall d) :
    relativeHomologyMap R d (standardOrientationBallPointMap d y hy)
      (b6m_standardOrientationBallClass R d) =
      relativeHomologyMap R d (translationPointComplementPairMap (Fin d → ℝ) y)
        (standardLocalClass R d) := by
  have h := (convexSupportTranslationPairHomotopy (Fin d → ℝ)
    (standardOrientationBall d) (zero_mem_standardOrientationBall d)
    (convex_ball _ _) y hy).relativeHomologyMap_apply_eq (R := R) d
      (b6m_standardOrientationBallClass R d)
  change relativeHomologyMap R d (standardOrientationBallPointMap d y hy)
    (b6m_standardOrientationBallClass R d) = relativeHomologyMap R d
      (standardOrientationBallPointMap d 0 (zero_mem_standardOrientationBall d) ≫
        translationPointComplementPairMap (Fin d → ℝ) y)
      (b6m_standardOrientationBallClass R d) at h
  simpa only [relativeHomologyMap_comp, LinearMap.comp_apply,
    b6m_standardOrientationBallClass_restrict_zero R] using h

end HodgeLean.Foundations.Program
