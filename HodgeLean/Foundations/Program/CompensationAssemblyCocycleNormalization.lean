import HodgeLean.Foundations.Program.CompensationAssemblyChainCocycle
import HodgeLean.Foundations.Program.CompensationAssemblyLoopNormalization
import Mathlib.AlgebraicTopology.SimplicialSet.Homology.Nondegenerate

noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 10000
set_option maxRecDepth 2048
open CategoryTheory Limits AlgebraicTopology AlgebraicTopology.Singular AlgebraicTopology.Simplicial
open HodgeLean.Foundations HodgeLean.Adapters
open scoped Simplicial
namespace HodgeLean.Foundations.Program

theorem cq_chainCocycleMap_pairing {X Y : TopCat.{0}}
    (a : SingularChainComplex ℚ X ⟶ SingularChainComplex ℚ Y) (n : ℕ)
    (c : Cocycle ℚ (TopCat.toSSet.obj Y) n) (z : Homology ℚ X n) :
    cohomologyEquivDualHomology ℚ X n
        (Singular.cohomologyClass X n (cq_chainCocycleMap a n c)) z =
      cohomologyEquivDualHomology ℚ Y n (Singular.cohomologyClass Y n c)
        (HomologicalComplex.homologyMap a n z) := by
  obtain ⟨v, rfl⟩ := ((SingularChainComplex ℚ X).sc n).moduleCatHomologyClass_surjective z
  rw [cohomologyEquivDualHomology_cohomologyClass]
  change _ = cohomologyEquivDualHomology ℚ Y n (Singular.cohomologyClass Y n c)
    ((ShortComplex.homologyMap ((HomologicalComplex.shortComplexFunctor (ModuleCat ℚ)
      (ComplexShape.down ℕ) n).map a)).hom _)
  rw [ShortComplex.moduleCatHomologyClass_naturality,
    cohomologyEquivDualHomology_cohomologyClass]
  rfl

def cq_normalizedChainProjection (X : TopCat.{0}) :
    SingularChainComplex ℚ X ⟶ SingularChainComplex ℚ X :=
  (TopCat.toSSet.obj X).toNormalizedChainComplex (ModuleCat.of ℚ ℚ) ≫
    (TopCat.toSSet.obj X).fromNormalizedChainComplex (ModuleCat.of ℚ ℚ)

theorem cq_normalizedChainProjection_homology (X : TopCat.{0}) (n : ℕ) :
    HomologicalComplex.homologyMap (cq_normalizedChainProjection X) n = 𝟙 _ := by
  have h := ((TopCat.toSSet.obj X).homotopyEquivNormalizedChainComplex
    (ModuleCat.of ℚ ℚ)).homotopyHomInvId.homologyMap_eq n
  exact h.trans (HomologicalComplex.homologyMap_id _ _)

def cq_normalizedCocycle (X : TopCat.{0}) (n : ℕ)
    (c : Cocycle ℚ (TopCat.toSSet.obj X) n) : Cocycle ℚ (TopCat.toSSet.obj X) n :=
  cq_chainCocycleMap (cq_normalizedChainProjection X) n c

theorem cq_normalizedCocycle_class (X : TopCat.{0}) (n : ℕ)
    (c : Cocycle ℚ (TopCat.toSSet.obj X) n) :
    Singular.cohomologyClass X n (cq_normalizedCocycle X n c) =
      Singular.cohomologyClass X n c := by
  apply (cohomologyEquivDualHomology ℚ X n).injective
  ext z
  have h := cq_chainCocycleMap_pairing (cq_normalizedChainProjection X) n c z
  rw [cq_normalizedChainProjection_homology] at h
  exact h

set_option backward.isDefEq.respectTransparency false in
theorem cq_normalizedCocycle_degenerate (X : TopCat.{0}) (n : ℕ)
    (c : Cocycle ℚ (TopCat.toSSet.obj X) n)
    (x : (TopCat.toSSet.obj X) _⦋n⦌) (hx : x ∈ (TopCat.toSSet.obj X).degenerate n) :
    (cq_normalizedCocycle X n c).1 (chainOfSimplex ℚ x) = 0 := by
  have hz := (TopCat.toSSet.obj X).ιNormalizedChainComplex_eq_zero
    (R := ModuleCat.of ℚ ℚ) x hx
  have hp : (TopCat.toSSet.obj X).ιChainComplex (R := ModuleCat.of ℚ ℚ) x ≫
      (cq_normalizedChainProjection X).f n = 0 := by
    rw [cq_normalizedChainProjection, HomologicalComplex.comp_f, ← Category.assoc,
      SSet.ιChainComplex_toNormalizedChainComplex_f, hz, zero_comp]
  have he := ConcreteCategory.congr_hom hp (1 : ℚ)
  change (cq_normalizedChainProjection X).f n (chainOfSimplex ℚ x) = 0 at he
  change c.1 ((cq_normalizedChainProjection X).f n (chainOfSimplex ℚ x)) = 0
  rw [he]
  exact c.1.map_zero

end HodgeLean.Foundations.Program
