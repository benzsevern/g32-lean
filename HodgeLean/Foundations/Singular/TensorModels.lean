import HodgeLean.Foundations.Singular.TensorHomotopy

/-! Acyclicity of the actual tensor complexes on the simplex-product models. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped TensorProduct
namespace HodgeLean.Foundations.Singular

/-- The tensor of two actual complexes concentrated in degree zero vanishes in positive degrees.
Source: Hatcher, Algebraic Topology, §3.2, the total tensor complex. -/
theorem tensorSingle_positive_isZero (A B : ModuleCat ℚ) (n : ℕ) :
    IsZero ((HomologicalComplex.tensorObj
      ((ChainComplex.single₀ (ModuleCat ℚ)).obj A)
      ((ChainComplex.single₀ (ModuleCat ℚ)).obj B)).X (n + 1)) := by
  let K := (ChainComplex.single₀ (ModuleCat ℚ)).obj A
  let L := (ChainComplex.single₀ (ModuleCat ℚ)).obj B
  apply (IsZero.iff_id_eq_zero _).mpr
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q hpq
  change p + q = n + 1 at hpq
  have hs : Subsingleton (K.X p ⊗[ℚ] L.X q) := by
    by_cases hp : p = 0
    · have hq : q ≠ 0 := by omega
      letI := ModuleCat.subsingleton_of_isZero
        (HomologicalComplex.isZero_single_obj_X (ComplexShape.down ℕ) 0 B q hq)
      infer_instance
    · letI := ModuleCat.subsingleton_of_isZero
        (HomologicalComplex.isZero_single_obj_X (ComplexShape.down ℕ) 0 A p hp)
      infer_instance
  letI := hs
  have hsrc : IsZero (K.X p ⊗ L.X q) :=
    ModuleCat.isZero_of_subsingleton (M := ModuleCat.of ℚ (K.X p ⊗[ℚ] L.X q))
  exact hsrc.eq_of_src _ _

/-- Actual rational chains of a contractible space are homotopy equivalent to a complex concentrated in degree zero.
Source: Hatcher, Algebraic Topology, Theorem 2.10 and §2.1, contraction and point chains. -/
def contractibleChainsSingleHomotopyEquiv
    (X : Type) [TopologicalSpace X] [ContractibleSpace X] :
    HomotopyEquiv (rationalChains (TopCat.of X))
      ((ChainComplex.single₀ (ModuleCat ℚ)).obj
        (∐ fun _ : TopCat.of (ULift.{0} Unit) => ModuleCat.of ℚ ℚ)) :=
  (AlgebraicTopology.contractibleSingularChainHomotopyEquiv ℚ X).trans
    ((HomotopyEquiv.ofIso (AlgebraicTopology.singularChainComplexFunctorIsoOfTotallyDisconnectedSpace
      (ModuleCat ℚ) (ModuleCat.of ℚ ℚ) (TopCat.of (ULift.{0} Unit)))).trans
        (ChainComplex.alternatingConstHomotopyEquiv _))

/-- The actual tensor complex of rational chains of contractible spaces is exact in every positive degree.
Source: Hatcher, Algebraic Topology, §3.2, tensor products of contractions. -/
theorem contractibleTensorChains_exactAt
    (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y]
    [ContractibleSpace X] [ContractibleSpace Y] (n : ℕ) :
    (rationalTensorChains (TopCat.of X) (TopCat.of Y)).ExactAt (n + 1) := by
  let e := tensorComplexHomotopyEquiv
    (contractibleChainsSingleHomotopyEquiv X) (contractibleChainsSingleHomotopyEquiv Y)
  rw [exactAt_iff_of_quasiIsoAt e.hom (n + 1)]
  exact HomologicalComplex.ExactAt.of_isZero (tensorSingle_positive_isZero _ _ n)

/-- Positive cycles in the actual tensor chains of two contractible spaces have fillers.
Source: Hatcher, Algebraic Topology, §3.2, tensor products of contractions. -/
theorem contractibleTensor_cycle_filler
    (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y]
    [ContractibleSpace X] [ContractibleSpace Y] (n : ℕ)
    (z : (rationalTensorChains (TopCat.of X) (TopCat.of Y)).X (n + 1))
    (hz : ((rationalTensorChains (TopCat.of X) (TopCat.of Y)).d (n + 1) n).hom z = 0) :
    ∃ w : (rationalTensorChains (TopCat.of X) (TopCat.of Y)).X (n + 2),
      ((rationalTensorChains (TopCat.of X) (TopCat.of Y)).d (n + 2) (n + 1)).hom w = z := by
  have he := contractibleTensorChains_exactAt X Y n
  rw [HomologicalComplex.exactAt_iff' _ (n + 2) (n + 1) n (by simp) (by simp)] at he
  have hr : LinearMap.range
      ((rationalTensorChains (TopCat.of X) (TopCat.of Y)).d (n + 2) (n + 1)).hom =
      LinearMap.ker ((rationalTensorChains (TopCat.of X) (TopCat.of Y)).d (n + 1) n).hom :=
    he.moduleCat_range_eq_ker
  have hzker : z ∈ LinearMap.ker
      ((rationalTensorChains (TopCat.of X) (TopCat.of Y)).d (n + 1) n).hom := hz
  rw [← hr] at hzker
  exact hzker

#print axioms contractibleTensor_cycle_filler
#print axioms contractibleTensorChains_exactAt
#print axioms contractibleChainsSingleHomotopyEquiv
#print axioms tensorSingle_positive_isZero
end HodgeLean.Foundations.Singular
