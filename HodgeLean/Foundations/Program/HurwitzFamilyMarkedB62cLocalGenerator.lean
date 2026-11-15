import HodgeConjecture.Definitions.AlgebraicTopology.LocalHomology.ComplexClass
import HodgeLean.Foundations.Program.HurwitzFamilyMarkedB62cSphereBoundary
import HodgeLean.Foundations.Program.HurwitzFamilyMarkedB62cEuclideanBoundary
import HodgeLean.Foundations.Program.HurwitzFamilyMarkedB62cIntegralSphere

noncomputable section
namespace HodgeLean.Foundations.Program
open CategoryTheory CategoryTheory.Limits AlgebraicTopology.Singular
open scoped _root_.Simplicial
variable (R : Type) [CommRing R]

set_option backward.isDefEq.respectTransparency false in
lemma b6m_standardAffineBoundaryChainMap_standardSphereSimplicialBoundaryChain (n : ℕ) :
    b6m_standardSphereSimplicialBoundaryChain R n ≫
        (b6m_standardAffineBoundaryChainMap R (n + 1)).f n =
      b6m_standardSubspaceBoundaryChain R n := by
  rw [b6m_standardSphereSimplicialBoundaryChain, b6m_standardSubspaceBoundaryChain,
    Preadditive.sum_comp]
  apply Finset.sum_congr rfl
  intro i _
  rw [Preadditive.zsmul_comp]
  congr 1
  change (∂Δ[n + 1] : SSet.{0}).ιChainComplex
      (standardSphereBoundaryFaceSimplex n i) ≫
        (SSet.chainComplexMap (standardAffineBoundarySimplicialMap (n + 1))
          (ModuleCat.of R R)).f n = _
  rw [SSet.ι_chainComplexMap_f, standardAffineBoundarySimplicialMap_face]
  rfl

set_option backward.isDefEq.respectTransparency false in
def b6m_standardAffineBoundaryHomologyMap (n : ℕ) :
    ((∂Δ[n + 2] : SSet.{0}).chainComplex
      (ModuleCat.of R R)).homology (n + 1) ⟶
    ((TopCat.toSSet.obj (puncturedPair ℝ (n + 2)).snd).chainComplex
      (ModuleCat.of R R)).homology (n + 1) :=
  HomologicalComplex.homologyMap
    (b6m_standardAffineBoundaryChainMap R (n + 2)) (n + 1)

theorem b6m_affineBoundaryHomologyMap_isIso (n : ℕ) :
    IsIso (b6m_standardAffineBoundaryHomologyMap R n) := by
  let he := (b6m_affineBoundaryCoefficientHomotopyEquiv R (n + 2)).toHomologyIso (n + 1)
  have hh : he.hom = b6m_standardAffineBoundaryHomologyMap R n := by
    change HomologicalComplex.homologyMap
      (b6m_affineBoundaryCoefficientHomotopyEquiv R (n + 2)).hom (n + 1) = _
    rw [b6m_affineBoundaryCoefficientHomotopyEquiv_hom]
    rfl
  rw [← hh]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
lemma b6m_standardPuncturedBoundaryCycle_inclusion' (n : ℕ) :
    b6m_standardPuncturedBoundaryCycle R n ≫
        ((chainPairFunctor R).obj
          (puncturedPair ℝ (n + 1))).left.iCycles n =
      b6m_standardSubspaceBoundaryChain R n := by
  rw [b6m_standardPuncturedBoundaryCycle, HomologicalComplex.liftCycles_i]

set_option backward.isDefEq.respectTransparency false in
lemma b6m_standardPuncturedBoundaryCycle_direct_inclusion (n : ℕ) :
    b6m_standardPuncturedBoundaryCycle R n ≫
        ((TopCat.toSSet.obj (puncturedPair ℝ (n + 1)).snd).chainComplex
          (ModuleCat.of R R)).iCycles n =
      b6m_standardSubspaceBoundaryChain R n :=
  b6m_standardPuncturedBoundaryCycle_inclusion' R n

set_option backward.isDefEq.respectTransparency false in
lemma b6m_standardSphereSimplicialBoundaryCycle_inclusion' (n : ℕ) :
    b6m_standardSphereSimplicialBoundaryCycle R n ≫
        ((∂Δ[n + 2] : SSet.{0}).chainComplex
          (ModuleCat.of R R)).iCycles (n + 1) =
      b6m_standardSphereSimplicialBoundaryChain R (n + 1) := by
  rw [b6m_standardSphereSimplicialBoundaryCycle,
    HomologicalComplex.liftCycles_i]

set_option backward.isDefEq.respectTransparency false in
lemma b6m_standardSphereSimplicialBoundaryCycle_affine (n : ℕ) :
    b6m_standardSphereSimplicialBoundaryCycle R n ≫
        HomologicalComplex.cyclesMap
          (b6m_standardAffineBoundaryChainMap R (n + 2)) (n + 1) =
      b6m_standardPuncturedBoundaryCycle R (n + 1) := by
  have hcycles :
      HomologicalComplex.cyclesMap
          (b6m_standardAffineBoundaryChainMap R (n + 2)) (n + 1) ≫
        ((TopCat.toSSet.obj (puncturedPair ℝ (n + 2)).snd).chainComplex
          (ModuleCat.of R R)).iCycles (n + 1) =
      ((∂Δ[n + 2] : SSet.{0}).chainComplex
          (ModuleCat.of R R)).iCycles (n + 1) ≫
        (b6m_standardAffineBoundaryChainMap R (n + 2)).f (n + 1) :=
    HomologicalComplex.cyclesMap_i (b6m_standardAffineBoundaryChainMap R (n + 2)) (n + 1)
  apply (cancel_mono
    (((TopCat.toSSet.obj (puncturedPair ℝ (n + 2)).snd).chainComplex
      (ModuleCat.of R R)).iCycles (n + 1))).mp
  rw [Category.assoc, hcycles, b6m_standardPuncturedBoundaryCycle_direct_inclusion R,
    ← Category.assoc, b6m_standardSphereSimplicialBoundaryCycle_inclusion' R]
  exact b6m_standardAffineBoundaryChainMap_standardSphereSimplicialBoundaryChain R (n + 1)

set_option backward.isDefEq.respectTransparency false in
lemma b6m_standardAffineBoundaryHomologyMap_standardSphereSimplicialBoundaryClass (n : ℕ) :
    (b6m_standardAffineBoundaryHomologyMap R n).hom
        (b6m_standardSphereSimplicialBoundaryClass R n) =
      b6m_standardPuncturedBoundaryClass R (n + 1) := by
  have hmor :
      b6m_standardSphereSimplicialBoundaryCycle R n ≫
          ((∂Δ[n + 2] : SSet.{0}).chainComplex
            (ModuleCat.of R R)).homologyπ (n + 1) ≫
          b6m_standardAffineBoundaryHomologyMap R n =
        b6m_standardPuncturedBoundaryCycle R (n + 1) ≫
          ((TopCat.toSSet.obj (puncturedPair ℝ (n + 2)).snd).chainComplex
            (ModuleCat.of R R)).homologyπ (n + 1) := by
    change b6m_standardSphereSimplicialBoundaryCycle R n ≫
        ((∂Δ[n + 2] : SSet.{0}).chainComplex
          (ModuleCat.of R R)).homologyπ (n + 1) ≫
        HomologicalComplex.homologyMap
          (b6m_standardAffineBoundaryChainMap R (n + 2)) (n + 1) = _
    rw [HomologicalComplex.homologyπ_naturality, ← Category.assoc,
      b6m_standardSphereSimplicialBoundaryCycle_affine R]
  exact ConcreteCategory.congr_hom hmor 1

set_option backward.isDefEq.respectTransparency false in
lemma b6m_span_standardPuncturedBoundaryClass_succ_eq_top_of_affine_isIso
    (n : ℕ)  :
    Submodule.span R {b6m_standardPuncturedBoundaryClass R (n + 1)} = ⊤ := by
  letI := b6m_affineBoundaryHomologyMap_isIso R n
  let e := (asIso (b6m_standardAffineBoundaryHomologyMap R n)).toLinearEquiv
  have he : e (b6m_standardSphereSimplicialBoundaryClass R n) =
      b6m_standardPuncturedBoundaryClass R (n + 1) :=
    b6m_standardAffineBoundaryHomologyMap_standardSphereSimplicialBoundaryClass R n
  have hmap :
      (Submodule.span R {b6m_standardSphereSimplicialBoundaryClass R n}).map e.toLinearMap =
        Submodule.span R {b6m_standardPuncturedBoundaryClass R (n + 1)} := by
    rw [Submodule.map_span]
    simp [he]
  have etop : (⊤ : Submodule R _).map e.toLinearMap = ⊤ := by
    rw [Submodule.map_top]
    exact LinearMap.range_eq_top.mpr e.surjective
  rw [← hmap, b6m_span_standardSphereSimplicialBoundaryClass R, etop]

set_option backward.isDefEq.respectTransparency false in
lemma b6m_span_standardLocalClass_add_two_eq_top_of_affine_isIso
    (n : ℕ)  :
    Submodule.span R {standardLocalClass R (n + 2)} = ⊤ := by
  rw [b6m_span_standardLocalClass_succ_eq_top_iff R (n + 1) (by lia)]
  exact b6m_span_standardPuncturedBoundaryClass_succ_eq_top_of_affine_isIso R n

theorem b6m_span_relativeHomology_degree_cast
    {P : TopPair} {i j : ℕ} (h : i = j) (x : RelativeHomology R P i) :
    Submodule.span R {h ▸ x} = ⊤ ↔ Submodule.span R {x} = ⊤ := by
  subst j
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem b6m_span_standardComplexLocalClass_pos (d : ℕ) (hd : 0 < d) :
    Submodule.span R {standardComplexLocalClass R d} = ⊤ := by
  unfold standardComplexLocalClass
  rw [b6m_span_relativeHomology_degree_cast]
  let e := (standardComplexRealRelativeHomologyIso R d).symm.toLinearEquiv
  have hr : Submodule.span R {standardLocalClass R (d * 2)} = ⊤ := by
    have hdim : d * 2 = (d - 1) * 2 + 2 := by omega
    rw [hdim]
    exact b6m_span_standardLocalClass_add_two_eq_top_of_affine_isIso R ((d - 1) * 2)
  have hm := congrArg (Submodule.map e.toLinearMap) hr
  simp only [Submodule.map_span, Set.image_singleton, Submodule.map_top,
    LinearMap.range_eq_top.mpr e.surjective] at hm
  exact hm

def b6m_standardRealLocalHomologyEquiv (n : ℕ) :
    RelativeHomology R (puncturedPair ℝ (n + 2)) (n + 2) ≃ₗ[R] R :=
  (b6m_standardPuncturedRelativeBoundaryIso R (n + 1) (by omega)).toLinearEquiv.trans
    (((b6m_affineBoundaryCoefficientHomotopyEquiv R (n + 2)).toHomologyIso
      (n + 1)).symm.toLinearEquiv.trans
        (b6m_standardSphereSuccSimplicialHomologyTopIsoRing R n).toLinearEquiv)

theorem b6m_standardComplexLocalClass_one_smul_bijective :
    Function.Bijective (fun r : R => r • standardComplexLocalClass R 1) := by
  apply b6m_smul_bijective_of_span_rank_one
    ((standardComplexRealRelativeHomologyIso R 1).toLinearEquiv.trans
      (b6m_standardRealLocalHomologyEquiv R 0))
  exact b6m_span_standardComplexLocalClass_pos R 1 (by decide)

end HodgeLean.Foundations.Program
