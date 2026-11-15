import HodgeLean.Foundations.Program.CompensationAssemblyRelativePrism

noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 10000
set_option maxRecDepth 2048
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.Program

def cq_circleChainHomotopy (X : TopCat.{0}) :=
  (cq_circleLoopHomotopy X).singularChainComplexFunctorObjMap (ModuleCat.of ℚ ℚ)

def cq_circleHomologyPrism (X : TopCat.{0}) (n : ℕ) :
    Homology ℚ X n ⟶ Homology ℚ (TopCat.of (X × UnitAddCircle)) (n + 1) :=
  cq_selfHomotopy_homologyMap (cq_circleChainHomotopy X) n

def cq_circleCohomologyPrism (X : TopCat.{0}) (n : ℕ) :
    Cohomology ℚ (TopCat.of (X × UnitAddCircle)) (n + 1) →ₗ[ℚ] Cohomology ℚ X n :=
  (cohomologyEquivDualHomology ℚ X n).symm.toLinearMap ∘ₗ
    LinearMap.dualMap (cq_circleHomologyPrism X n).hom ∘ₗ
      (cohomologyEquivDualHomology ℚ (TopCat.of (X × UnitAddCircle)) (n + 1)).toLinearMap

theorem cq_circleHomologyPrism_relative (P : TopPair.{0}) (n : ℕ) :
    HomologicalComplex.homologyMap (relativeChainProjection ℚ P) n ≫
        cq_pairCircleHomologyPrism P n =
      cq_circleHomologyPrism P.fst n ≫
        HomologicalComplex.homologyMap (relativeChainProjection ℚ (cq_pairCircle P)) (n + 1) := by
  exact cq_selfHomotopy_homologyMap_naturality _ _ _ _
    (fun k => TopPair.Homotopy.relativeChainHomotopyComponent_fac
      (cq_pairCircleLoopHomotopy P) k (k + 1)) n

theorem cq_circleCohomologyPrism_pairing (X : TopCat.{0}) (n : ℕ)
    (a : Cohomology ℚ (TopCat.of (X × UnitAddCircle)) (n + 1)) (z : Homology ℚ X n) :
    cohomologyEquivDualHomology ℚ X n (cq_circleCohomologyPrism X n a) z =
      cohomologyEquivDualHomology ℚ (TopCat.of (X × UnitAddCircle)) (n + 1) a
        (cq_circleHomologyPrism X n z) := by
  simp only [cq_circleCohomologyPrism, LinearMap.comp_apply,
    LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply, LinearMap.dualMap_apply]

theorem cq_circleCohomologyPrism_relative (P : TopPair.{0}) (n : ℕ)
    (a : RelativeCohomology ℚ (cq_pairCircle P) (n + 1)) :
    cq_circleCohomologyPrism P.fst n
        (relativeCohomologyToAbsolute ℚ (cq_pairCircle P) (n + 1) a) =
      relativeCohomologyToAbsolute ℚ P n (cq_pairCircleCohomologyPrism P n a) := by
  apply (cohomologyEquivDualHomology ℚ P.fst n).injective
  ext z
  have hleft := cq_circleCohomologyPrism_pairing P.fst n
    (relativeCohomologyToAbsolute ℚ (cq_pairCircle P) (n + 1) a) z
  have hl := cohomologyEquivDualHomology_relativeCohomologyToAbsolute ℚ
    (cq_pairCircle P) (n + 1) a (cq_circleHomologyPrism P.fst n z)
  have hr := cohomologyEquivDualHomology_relativeCohomologyToAbsolute ℚ P n
    (cq_pairCircleCohomologyPrism P n a) z
  have hright := cq_pairCircleCohomologyPrism_pairing P n a
    ((relativeHomologyProjection ℚ P n).hom z)
  apply (hleft.trans hl).trans
  apply Eq.trans _ (hr.trans hright).symm
  have h := ConcreteCategory.congr_hom (cq_circleHomologyPrism_relative P n) z
  exact congrArg (relativeCohomologyEquivDualHomology ℚ (cq_pairCircle P) (n + 1) a) h.symm

end HodgeLean.Foundations.Program
