import HodgeLean.Foundations.Program.CompensationAssemblyPrismSimplex

noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 10000
set_option maxRecDepth 2048
open CategoryTheory AlgebraicTopology AlgebraicTopology.Simplicial
namespace HodgeLean.Foundations.Program

def cq_chainCocycleMap {X Y : SSet.{0}}
    (a : X.chainComplex (ModuleCat.of ℚ ℚ) ⟶ Y.chainComplex (ModuleCat.of ℚ ℚ))
    (n : ℕ) (c : Cocycle ℚ Y n) : Cocycle ℚ X n :=
  ⟨c.1.comp (a.f n).hom, by
    ext z
    have h := ConcreteCategory.congr_hom (a.comm (n + 1) n) z
    change c.1 ((a.f n).hom (boundary ℚ n z)) = 0
    change boundary ℚ n ((a.f (n + 1)).hom z) = (a.f n).hom (boundary ℚ n z) at h
    rw [← h]
    exact LinearMap.congr_fun c.2 ((a.f (n + 1)).hom z)⟩

end HodgeLean.Foundations.Program
