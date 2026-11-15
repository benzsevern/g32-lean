import HodgeLean.Foundations.Program.CompensationAssemblyPrismAbsolute

noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 10000
set_option maxRecDepth 2048
open CategoryTheory CategoryTheory.Limits AlgebraicTopology
open scoped Simplicial
namespace HodgeLean.Foundations.Program

theorem cq_simplicialPrism_simplex {X Y : SSet.{0}} {f g : X ⟶ Y}
    (H : SSet.Homotopy f g) (n : ℕ) (x : X _⦋n⦌) :
    X.ιChainComplex (R := ModuleCat.of ℚ ℚ) x ≫
        (H.chainComplexMap (ModuleCat.of ℚ ℚ)).hom n (n + 1) =
      -∑ k : Fin (n + 1), ((-1 : ℤ) ^ (k : ℕ)) •
        Y.ιChainComplex (R := ModuleCat.of ℚ ℚ)
          (H.toSimplicialObjectHomotopy.h k x) := by
  dsimp [SSet.Homotopy.chainComplexMap,
    CategoryTheory.SimplicialObject.Homotopy.sSetChainComplexMap,
    CategoryTheory.SimplicialObject.Homotopy.toChainHomotopy]
  rw [CategoryTheory.SimplicialObject.Homotopy.ToChainHomotopy.hom_eq]
  simp [Preadditive.comp_neg, Preadditive.comp_sum, Preadditive.comp_zsmul,
    SSet.ιChainComplex, SimplicialObject.Homotopy.whiskerRight_h,
    sigmaConst, Sigma.map']

set_option backward.isDefEq.respectTransparency false in
theorem cq_simplicialPrism_cochain_simplex {X Y : SSet.{0}} {f g : X ⟶ Y}
    (H : SSet.Homotopy f g) (n : ℕ) (x : X _⦋n⦌)
    (c : AlgebraicTopology.Simplicial.Cochain ℚ Y (n + 1)) :
    c ((H.chainComplexMap (ModuleCat.of ℚ ℚ)).hom n (n + 1)
      (AlgebraicTopology.Simplicial.chainOfSimplex ℚ x)) =
      -∑ k : Fin (n + 1), ((-1 : ℤ) ^ (k : ℕ)) •
        c (AlgebraicTopology.Simplicial.chainOfSimplex ℚ
          (H.toSimplicialObjectHomotopy.h k x)) := by
  have h := ConcreteCategory.congr_hom (cq_simplicialPrism_simplex H n x) (1 : ℚ)
  have h' := congrArg c h
  simpa only [ConcreteCategory.comp_apply, ModuleCat.hom_neg, ModuleCat.hom_sum,
    ModuleCat.hom_zsmul, LinearMap.neg_apply, LinearMap.sum_apply,
    LinearMap.smul_apply, map_neg, map_sum, map_zsmul,
    AlgebraicTopology.Simplicial.chainOfSimplex] using h'

end HodgeLean.Foundations.Program
