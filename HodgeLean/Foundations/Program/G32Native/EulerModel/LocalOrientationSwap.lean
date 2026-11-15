import HodgeLean.Foundations.Program.G32Native.EulerModel.LocalOrientationHomology
import HodgeConjecture.Lemmas.AlgebraicTopology.Singular.RelativeHomotopyInvariance

/-! # The actual adjacent coordinate exchange on local homology -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicTopology.Singular
open scoped Simplicial
namespace HodgeLean.Foundations.Program.G32Native.EulerModel

/-- The actual continuous map exchanging the two indicated real coordinates. -/
def orientationAdjacentSwapMap (d i : ℕ) (hi : i + 1 < d) :
    (puncturedPair ℝ d).fst ⟶ (puncturedPair ℝ d).fst :=
  TopCat.ofHom ⟨fun z j => z (Equiv.swap (⟨i, by omega⟩ : Fin d) ⟨i + 1, hi⟩ j), by fun_prop⟩

/-- The same coordinate exchange retains the actual punctured subspace. -/
def orientationAdjacentSwapPairMap (d i : ℕ) (hi : i + 1 < d) :
    puncturedPair ℝ d ⟶ puncturedPair ℝ d :=
  TopPair.ofHom (orientationAdjacentSwapMap d i hi)
    (TopCat.ofHom ⟨fun z => ⟨(orientationAdjacentSwapMap d i hi) z.1, by
      intro h
      apply z.2
      funext j
      have hj := congrFun h (Equiv.swap (⟨i, by omega⟩ : Fin d) ⟨i + 1, hi⟩ j)
      change z.1 (Equiv.swap (⟨i, by omega⟩ : Fin d) ⟨i + 1, hi⟩
        (Equiv.swap (⟨i, by omega⟩ : Fin d) ⟨i + 1, hi⟩ j)) = 0 at hj
      simpa only [Equiv.swap_apply_self, Pi.zero_apply] using hj⟩, by
      apply Continuous.subtype_mk
      exact (orientationAdjacentSwapMap d i hi).hom.continuous.comp continuous_subtype_val⟩)
    (by ext; rfl)

/-- The exchanged distinguished face is exactly the image of the specified standard singular simplex. -/
theorem orientationAdjacentSwap_simplex (d i : ℕ) (hi : i + 1 < d) :
    (TopCat.toSSet.obj (puncturedPair ℝ d).fst).δ (⟨i, by omega⟩ : Fin (d + 2))
      (foldedOrientationSingularSimplex d i hi) =
      (TopCat.toSSet.map (orientationAdjacentSwapMap d i hi)).app _ (standardSingularSimplex d) := by
  apply ((puncturedPair ℝ d).fst.toSSetObjEquiv _).injective
  apply ContinuousMap.ext
  intro t
  exact (foldedOrientationSimplex_face_left d i hi t).trans
    (standardAffineSimplex_adjacent_swap d i hi t)

#print axioms orientationAdjacentSwap_simplex

/-- The actual relative chain map sends the standard chain to the specified exchanged face chain. -/
theorem orientationAdjacentSwap_relativeChain (d i : ℕ) (hi : i + 1 < d) :
    standardLocalChain ℚ d ≫
        ((relativeChainFunctor ℚ).map (orientationAdjacentSwapPairMap d i hi)).f d =
      foldedOrientationAmbientFace d i hi ⟨i, by omega⟩ ≫ (standardLocalProjection ℚ d).f d := by
  have hn := congrArg (fun q => q.f d)
    (TopPair.Homotopy.relativeChainProjection_naturality (R := ℚ)
      (orientationAdjacentSwapPairMap d i hi))
  change (standardLocalProjection ℚ d).f d ≫
      ((relativeChainFunctor ℚ).map (orientationAdjacentSwapPairMap d i hi)).f d =
    (SSet.chainComplexMap (TopCat.toSSet.map (orientationAdjacentSwapMap d i hi))
      (ModuleCat.of ℚ ℚ)).f d ≫ (standardLocalProjection ℚ d).f d at hn
  have ha : standardAmbientSimplexChain ℚ d ≫
      (SSet.chainComplexMap (TopCat.toSSet.map (orientationAdjacentSwapMap d i hi))
        (ModuleCat.of ℚ ℚ)).f d = foldedOrientationAmbientFace d i hi ⟨i, by omega⟩ := by
    unfold standardAmbientSimplexChain
    rw [SSet.ι_chainComplexMap_f, ← orientationAdjacentSwap_simplex]
    rfl
  rw [standardLocalChain, Category.assoc, hn, ← Category.assoc, ha]

#print axioms orientationAdjacentSwap_relativeChain

/-- The coordinate exchange carries the standard cycle to the actual exchanged-face cycle. -/
theorem orientationAdjacentSwap_cycles (d i : ℕ) (hi : i + 1 < d) :
    standardLocalCycle ℚ d ≫ HomologicalComplex.cyclesMap
        ((relativeChainFunctor ℚ).map (orientationAdjacentSwapPairMap d i hi)) d =
      swappedOrientationCycle d i hi := by
  apply (cancel_mono ((standardLocalRelativeChainComplex ℚ d).iCycles d)).mp
  rw [Category.assoc, HomologicalComplex.cyclesMap_i, ← Category.assoc,
    standardLocalCycle_inclusion, orientationAdjacentSwap_relativeChain,
    swappedOrientationCycle_inclusion]

#print axioms orientationAdjacentSwap_cycles

/-- Every adjacent real coordinate exchange reverses the specified standard local homology class. -/
theorem orientationAdjacentSwap_standardLocalClass (d i : ℕ) (hi : i + 1 < d) :
    relativeHomologyMap ℚ d (orientationAdjacentSwapPairMap d i hi) (standardLocalClass ℚ d) =
      -standardLocalClass ℚ d := by
  have hmap : (standardLocalCycle ℚ d ≫ (standardLocalRelativeChainComplex ℚ d).homologyπ d) ≫
      HomologicalComplex.homologyMap
        ((relativeChainFunctor ℚ).map (orientationAdjacentSwapPairMap d i hi)) d =
      -(standardLocalCycle ℚ d ≫ (standardLocalRelativeChainComplex ℚ d).homologyπ d) := by
    rw [Category.assoc, HomologicalComplex.homologyπ_naturality, ← Category.assoc,
      orientationAdjacentSwap_cycles, swappedOrientationCycle_homology]
  change (((standardLocalCycle ℚ d ≫ (standardLocalRelativeChainComplex ℚ d).homologyπ d) ≫
    HomologicalComplex.homologyMap
      ((relativeChainFunctor ℚ).map (orientationAdjacentSwapPairMap d i hi)) d).hom) 1 = _
  rw [hmap]
  rfl

#print axioms orientationAdjacentSwap_standardLocalClass
end HodgeLean.Foundations.Program.G32Native.EulerModel
