import HodgeLean.Foundations.Program.G32WeilLineAssemblyProduct
import HodgeLean.Foundations.Program.G32WeilLineAssemblyCupSpan
import HodgeLean.Foundations.Program.G32ContractionClassMultiply
import HodgeLean.Foundations.Program.G32ContractionScalar
import HodgeLean.Foundations.Program.CycleFoundationsPullbackSpan
import HodgeLean.Adapters.DegreeZeroUnconditional
import HodgeLean.Adapters.KleimanProduct

noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 400000
set_option Elab.async false
open scoped TensorProduct CategoryTheory.MonObj
open CategoryTheory.CartesianMonoidalCategory
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint MonoidalCategory
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Foundations HodgeLean.Papers
namespace HodgeLean.Foundations.Program
attribute [local irreducible] cupProductOf algebraicCycleClassSpan

variable {A : g32t_Sixfold}

theorem g32c_oneB_single (X : g32p_Cover A) {r : ℕ}
    (S : Fin r → g32p_Supplier) (hS : ∀ j, g32p_Admissible X.aut (S j)) (j : Fin r) :
    g32c_oneB X S hS ∘ₗ LinearMap.single ℂ (fun i => ℂ ⊗[ℚ] HQ (g32c_parts X S hS i) 1) j =
      (homPullback (cfd_proj r (g32c_parts X S hS) j) 1).baseChange ℂ := by
  classical
  apply LinearMap.ext
  intro x
  simp only [LinearMap.comp_apply, g32c_oneB, LinearMap.sum_apply,
    LinearMap.proj_apply, LinearMap.coe_single]
  rw [Finset.sum_eq_single j]
  · rw [Pi.single_eq_same]
  · intro b hb hbj
    rw [Pi.single_eq_of_ne hbj, map_zero]
  · exact fun hj => False.elim (hj (Finset.mem_univ _))

end HodgeLean.Foundations.Program
