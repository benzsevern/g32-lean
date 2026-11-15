import HodgeLean.Foundations.Program.CompensationAssemblyPrismCupEvaluation

noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 10000
set_option maxRecDepth 2048
open CategoryTheory AlgebraicTopology AlgebraicTopology.Singular AlgebraicTopology.Simplicial
open HodgeLean.Foundations
namespace HodgeLean.Foundations.Program

attribute [local implicit_reducible] ShortComplex.moduleCatMk ShortComplex.moduleCatLeftHomologyData

def cq_cupCocycle (X : TopCat.{0}) (p q : ℕ)
    (a : Cocycle ℚ (TopCat.toSSet.obj X) p) (b : Cocycle ℚ (TopCat.toSSet.obj X) q) :
    Cocycle ℚ (TopCat.toSSet.obj X) (p + q) :=
  ⟨Singular.cupCochain X p q a.1 b.1, by
    change coboundary ℚ (p + q) (Singular.cupCochain X p q a.1 b.1) = 0
    rw [Singular.coboundary_cupCochain, show coboundary ℚ p a.1 = 0 from a.2,
      show coboundary ℚ q b.1 = 0 from b.2]
    simp⟩

set_option backward.isDefEq.respectTransparency false in
theorem cq_cupCocycle_class (X : TopCat.{0}) (p q : ℕ)
    (a : Cocycle ℚ (TopCat.toSSet.obj X) p) (b : Cocycle ℚ (TopCat.toSSet.obj X) q) :
    Singular.cup X rfl (Singular.cohomologyClass X p a) (Singular.cohomologyClass X q b) =
      Singular.cohomologyClass X (p + q) (cq_cupCocycle X p q a b) := by
  dsimp only [Singular.cup, Singular.cohomologyClass, LinearMap.comp_apply]
  simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.coe_comp, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.symm_apply_apply]
  rfl

end HodgeLean.Foundations.Program
