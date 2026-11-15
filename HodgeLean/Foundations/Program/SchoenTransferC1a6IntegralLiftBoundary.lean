import HodgeLean.Foundations.Program.SchoenTransferC1a6IntegralLiftChains

/-! Boundaries of lifted integral one-chains. -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Convexity
open scoped Simplicial
namespace HodgeLean.Foundations.Program

theorem s4_c1a6_simplexVertex_face (X : TopCat)
    (σ : (TopCat.toSSet.obj X) _⦋1⦌) (i : Fin 2) :
    TopCat.toSSetObj₀Equiv ((TopCat.toSSet.obj X).δ i σ) =
      X.toSSetObjEquiv _ σ (StdSimplex.single (i.succAbove 0)) := by
  simp only [TopCat.toSSetObj₀Equiv_apply]
  erw [TopCat.toSSetObjEquiv_δ_apply]
  have hd : (default : StdSimplex ℝ (Fin 1)) = StdSimplex.single 0 := Subsingleton.elim _ _
  rw [hd, StdSimplex.map_single]

end HodgeLean.Foundations.Program
