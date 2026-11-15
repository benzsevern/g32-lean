import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.AlgebraicTopology.SimplicialSet.Homology.Nondegenerate
import Mathlib.AlgebraicTopology.SimplicialSet.TopAdj
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.AlgebraicTopology.ExtraDegeneracy
import Mathlib.AlgebraicTopology.SimplicialSet.Homology.HomotopyInvariance
import Mathlib.Algebra.Homology.QuasiIso

/-! Point comparison for the actual realization unit.
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory
open scoped Simplicial
namespace HodgeLean.Foundations.Program

/-- The realization unit of the point is an isomorphism of simplicial sets.
Source: Mathlib SSet.stdSimplex.isTerminalObj₀ and SimplexCategory.toTopHomeo. -/
lemma c1a5_point_unit_isIso : IsIso (sSetTopAdj.unit.app (Δ[0] : SSet.{0})) := by
  have (n : SimplexCategoryᵒᵖ) : IsIso ((sSetTopAdj.unit.app (Δ[0] : SSet.{0})).app n) := by
    rw [isIso_iff_bijective]
    constructor
    · intro x y h
      apply SSet.stdSimplex.objEquiv.injective
      exact Subsingleton.elim _ _
    · intro y
      obtain ⟨x⟩ := (show Nonempty ((Δ[0] : SSet.{0}).obj n) from inferInstance)
      refine ⟨x, ?_⟩
      apply (TopCat.toSSetObjEquiv _ _).injective
      ext z
      exact Subsingleton.elim _ _
  exact NatIso.isIso_of_isIso_app _

/-- Integral comparison at the point, with the unnormalized chain complex.
Source: Hatcher, Algebraic Topology, §2.1, Theorem 2.27, degree zero. -/
lemma c1a5_point_comparison :
    QuasiIso (SSet.chainComplexMap (sSetTopAdj.unit.app (Δ[0] : SSet.{0}))
      (ModuleCat.of ℤ ℤ)) := by
  have := c1a5_point_unit_isIso
  infer_instance

/-- An extra degeneracy gives a homotopy equivalence on integral chains.
Source: Mathlib ExtraDegeneracy.homotopy; Hatcher, Algebraic Topology, §2.1. -/
def c1a5_extraDegeneracy_chainEquiv
    {X : SimplicialObject.Augmented (Type 0)}
    (ed : SimplicialObject.Augmented.ExtraDegeneracy X) :
    HomotopyEquiv (SSet.chainComplex X.left (ModuleCat.of ℤ ℤ))
      (SSet.chainComplex ((SimplicialObject.const (Type 0)).obj X.right) (ModuleCat.of ℤ ℤ)) where
  hom := SSet.chainComplexMap X.hom _
  inv := SSet.chainComplexMap ed.section_ _
  homotopyHomInvId := by
    let F := (SSet.chainComplexFunctor (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ)
    have H := ed.homotopy.sSetChainComplexMap (ModuleCat.of ℤ ℤ)
    change Homotopy (F.map (X.hom ≫ ed.section_)) (F.map (𝟙 X.left)) at H
    rw [F.map_comp] at H
    have hid : F.map (𝟙 X.left) = 𝟙 _ := F.map_id (X.left : SSet)
    rw [hid] at H
    exact H
  homotopyInvHomId := Homotopy.ofEq (by
    change ((SSet.chainComplexFunctor (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ)).map _ ≫
      ((SSet.chainComplexFunctor (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ)).map _ = _
    rw [← CategoryTheory.Functor.map_comp, ed.section_comp_hom, CategoryTheory.Functor.map_id])

set_option backward.isDefEq.respectTransparency false in
/-- The simplicial projection of a standard simplex preserves integral homology.
Source: Hatcher, Algebraic Topology, §2.1, simplex contraction;
Mathlib SSet.Augmented.StandardSimplex.extraDegeneracy. -/
lemma c1a5_simplicial_augmentation (n : ℕ) :
    QuasiIso (SSet.chainComplexMap
      (SSet.stdSimplex.map (SimplexCategory.const ⦋n⦌ ⦋0⦌ 0)) (ModuleCat.of ℤ ℤ)) := by
  let F := (SSet.chainComplexFunctor (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ)
  let X := SSet.Augmented.stdSimplex.obj ⦋n⦌
  let Y := SSet.Augmented.stdSimplex.obj ⦋0⦌
  have hx : QuasiIso (F.map X.hom) :=
    (c1a5_extraDegeneracy_chainEquiv
      (SSet.Augmented.StandardSimplex.extraDegeneracy ⦋n⦌)).quasiIso_hom
  have hy : QuasiIso (F.map Y.hom) :=
    (c1a5_extraDegeneracy_chainEquiv
      (SSet.Augmented.StandardSimplex.extraDegeneracy ⦋0⦌)).quasiIso_hom
  have w : SSet.stdSimplex.map (SimplexCategory.const ⦋n⦌ ⦋0⦌ 0) ≫ Y.hom = X.hom := by
    apply NatTrans.ext
    funext m
    exact (Limits.terminalIsTerminal (C := Type 0)).hom_ext _ _
  have : QuasiIso (F.map (SSet.stdSimplex.map (SimplexCategory.const ⦋n⦌ ⦋0⦌ 0)) ≫
      F.map Y.hom) := by
    rw [← F.map_comp, w]
    exact hx
  exact quasiIso_of_comp_right _ (F.map Y.hom)

/-- An initial simplicial set has an isomorphic realization unit.
Source: Hatcher, Algebraic Topology, §2.1, the empty chain complex;
Mathlib IsInitial.isInitialObj and sSetTopAdj. -/
lemma c1a5_empty_unit_isIso (K : SSet.{0}) (hK : Limits.IsInitial K) :
    IsIso (sSetTopAdj.unit.app K) := by
  let hT := hK.isInitialObj SSet.toTop K
  have : IsEmpty (SSet.toTop.obj K) :=
    Function.isEmpty (hT.to (TopCat.of PEmpty))
  have (m : SimplexCategoryᵒᵖ) : IsEmpty (K.obj m) :=
    Function.isEmpty ((hK.isInitialObj ((evaluation _ _).obj m) K).to PEmpty)
  have (m : SimplexCategoryᵒᵖ) : IsEmpty ((TopCat.toSSet.obj (SSet.toTop.obj K)).obj m) := by
    refine ⟨fun σ ↦ ?_⟩
    exact isEmptyElim ((TopCat.toSSetObjEquiv _ _ σ) (Convexity.StdSimplex.single 0))
  have (m : SimplexCategoryᵒᵖ) : IsIso ((sSetTopAdj.unit.app K).app m) := by
    rw [isIso_iff_bijective]
    constructor
    · intro x y h
      exact (inferInstance : IsEmpty (K.obj m)).false x |>.elim
    · intro y
      exact (inferInstance : IsEmpty ((TopCat.toSSet.obj (SSet.toTop.obj K)).obj m)).false y |>.elim
  exact NatIso.isIso_of_isIso_app _

/-- Empty comparison on integral chains.
Source: Hatcher, Algebraic Topology, §2.1, the empty chain complex. -/
lemma c1a5_empty_comparison (K : SSet.{0}) (hK : Limits.IsInitial K) :
    QuasiIso (SSet.chainComplexMap (sSetTopAdj.unit.app K) (ModuleCat.of ℤ ℤ)) := by
  have := c1a5_empty_unit_isIso K hK
  infer_instance

/-- The integral simplicial chain functor preserves all monomorphisms.
Source: Mathlib sigmaConst preserves monomorphisms and HomologicalComplex.mono_of_mono_f. -/
instance c1a5_integral_chains_preserves_monomorphisms :
    ((SSet.chainComplexFunctor (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ)).PreservesMonomorphisms where
  preserves f _ := by
    apply HomologicalComplex.mono_of_mono_f
    intro n
    change Mono ((Limits.sigmaConst.obj (ModuleCat.of ℤ ℤ)).map (f.app (Opposite.op ⦋n⦌)))
    infer_instance

end HodgeLean.Foundations.Program
