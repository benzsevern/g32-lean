import Mathlib.AlgebraicTopology.SimplicialSet.Homology.MapHomologicalComplex
import Mathlib.Algebra.Category.Grp.ZModuleEquivalence
import HodgeConjecture.Lemmas.AlgebraicTopology.Singular.Excision.OpenCover
import HodgeLean.Foundations.Program.SchoenTransferC1a5ExactHelpers

/-! Relative integral small-chain transport for an actual open cover.
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits AlgebraicTopology.Singular
open scoped Simplicial
namespace HodgeLean.Foundations.Program

/-- Open-cover small-chain replacement remains a comparison after taking a fixed subcomplex quotient.
Source: Hatcher, Algebraic Topology, §2.1, Theorem 2.20;
HodgeConjecture coverSmallChainApproximation_of_openCover. -/
lemma c1a5_relative_open_cover_excision {I : Type} (X : TopCat.{0}) (U : I → Set X)
    (hU : ∀ i, IsOpen (U i)) (hcover : ⋃ i, U i = Set.univ)
    {A : ChainComplex AddCommGrpCat ℕ}
    (f : A ⟶ CoverSmallIntegralSingularChainComplex X U) [Mono f] :
    QuasiIso (cokernel.map f (f ≫ coverSmallIntegralSingularChainInclusion X U)
      (𝟙 A) (coverSmallIntegralSingularChainInclusion X U) (by simp)) := by
  have hI : QuasiIso (coverSmallIntegralSingularChainInclusion X U) := by
    have h := (coverSmallChainHomotopyEquiv_of_openCover X U hU hcover).quasiIso_hom
    rwa [coverSmallChainHomotopyEquiv_of_openCover_hom] at h
  exact c1a5_cokernel_comparison _ _ _ _ _ inferInstance hI

/-- Small-chain comparison in the literal integral module coefficient model.
Source: Hatcher, Algebraic Topology, §2.1, Theorem 2.20;
Mathlib SSet.chainComplexFunctorObjCompMapIso and the integral open-cover theorem. -/
lemma c1a5_module_open_cover_comparison {I : Type} (X : TopCat.{0}) (U : I → Set X)
    (hU : ∀ i, IsOpen (U i)) (hcover : ⋃ i, U i = Set.univ) :
    QuasiIso (SSet.chainComplexMap (coverSmallSingularSubcomplex X U).ι
      (ModuleCat.of ℤ ℤ)) := by
  let F := forget₂ (ModuleCat ℤ) AddCommGrpCat
  let i := (coverSmallSingularSubcomplex X U).ι
  let e := SSet.chainComplexFunctorObjCompMapIso F (ModuleCat.of ℤ ℤ)
  have hI : QuasiIso (SSet.chainComplexMap i (F.obj (ModuleCat.of ℤ ℤ))) := by
    have h := (coverSmallChainHomotopyEquiv_of_openCover X U hU hcover).quasiIso_hom
    rwa [coverSmallChainHomotopyEquiv_of_openCover_hom] at h
  have hw := e.hom.naturality i
  change (F.mapHomologicalComplex (ComplexShape.down ℕ)).map
    (SSet.chainComplexMap i (ModuleCat.of ℤ ℤ)) ≫ e.hom.app (TopCat.toSSet.obj X) =
      e.hom.app (coverSmallSingularSubcomplex X U : SSet) ≫
        SSet.chainComplexMap i (F.obj (ModuleCat.of ℤ ℤ)) at hw
  have hcomp : QuasiIso
      ((F.mapHomologicalComplex (ComplexShape.down ℕ)).map
        (SSet.chainComplexMap i (ModuleCat.of ℤ ℤ)) ≫ e.hom.app (TopCat.toSSet.obj X)) := by
    rw [hw]
    infer_instance
  have hmap : QuasiIso ((F.mapHomologicalComplex (ComplexShape.down ℕ)).map
      (SSet.chainComplexMap i (ModuleCat.of ℤ ℤ))) :=
    (quasiIso_iff_comp_right _ (e.hom.app (TopCat.toSSet.obj X))).1 hcomp
  exact (HomologicalComplex.quasiIso_map_iff_of_preservesHomology
    (SSet.chainComplexMap i (ModuleCat.of ℤ ℤ)) F).1 hmap

/-- Relative open-cover excision in integral module chains.
Source: Hatcher, Algebraic Topology, §2.1, Theorem 2.20. -/
lemma c1a5_module_relative_open_cover_excision {I : Type} (X : TopCat.{0}) (U : I → Set X)
    (hU : ∀ i, IsOpen (U i)) (hcover : ⋃ i, U i = Set.univ)
    {A : ChainComplex (ModuleCat ℤ) ℕ}
    (f : A ⟶ (coverSmallSingularSubcomplex X U : SSet).chainComplex (ModuleCat.of ℤ ℤ))
    [Mono f] :
    let j := SSet.chainComplexMap (coverSmallSingularSubcomplex X U).ι (ModuleCat.of ℤ ℤ)
    QuasiIso (cokernel.map f (f ≫ j) (𝟙 A) j (by simp)) := by
  dsimp only
  have hj := c1a5_module_open_cover_comparison X U hU hcover
  have : Mono (SSet.chainComplexMap (coverSmallSingularSubcomplex X U).ι
      (ModuleCat.of ℤ ℤ)) := by
    apply HomologicalComplex.mono_of_mono_f
    intro n
    change Mono ((sigmaConst.obj (ModuleCat.of ℤ ℤ)).map
      ((coverSmallSingularSubcomplex X U).ι.app (Opposite.op ⦋n⦌)))
    infer_instance
  exact c1a5_cokernel_comparison _ _ _ _ _ inferInstance hj

end HodgeLean.Foundations.Program
