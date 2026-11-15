import HodgeLean.Foundations.Program.SchoenTransferC1a6IntegralLiftBoundary

/-! Lifted displacements of integral singular cycles project to zero. -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Convexity
open scoped Simplicial
namespace HodgeLean.Foundations.Program
variable {V J X : Type} [AddCommGroup V] [TopologicalSpace V] [ContinuousAdd V]
    [AddCommGroup J] [TopologicalSpace J] [TopologicalSpace X]
    (π : V →+ J) (hπ : IsCoveringMap π ∧ Function.Surjective π)
    (f : X → J) (hf : Continuous f)

/-- The displacement between the endpoints of a chosen lift of a singular simplex. -/
def s4_c1a6_liftDisplacement (σ : (TopCat.toSSet.obj (TopCat.of X)) _⦋1⦌) : V :=
  (b3Rest2_exists_lift π hπ f hf ((TopCat.of X).toSSetObjEquiv _ σ)).choose
      (StdSimplex.single 1) -
    (b3Rest2_exists_lift π hπ f hf ((TopCat.of X).toSSetObjEquiv _ σ)).choose
      (StdSimplex.single 0)

theorem s4_c1a6_liftDisplacement_project
    (σ : (TopCat.toSSet.obj (TopCat.of X)) _⦋1⦌) :
    π (s4_c1a6_liftDisplacement π hπ f hf σ) =
      f (TopCat.toSSetObj₀Equiv ((TopCat.toSSet.obj (TopCat.of X)).δ 0 σ)) -
        f (TopCat.toSSetObj₀Equiv ((TopCat.toSSet.obj (TopCat.of X)).δ 1 σ)) := by
  rw [s4_c1a6_liftDisplacement, map_sub,
    (b3Rest2_exists_lift π hπ f hf ((TopCat.of X).toSSetObjEquiv _ σ)).choose_spec,
    (b3Rest2_exists_lift π hπ f hf ((TopCat.of X).toSSetObjEquiv _ σ)).choose_spec,
    s4_c1a6_simplexVertex_face, s4_c1a6_simplexVertex_face]
  rfl

/-- Integral linear extension of the chosen lifted displacements. -/
def s4_c1a6_liftChain : (s4_c1a6_ZChains (TopCat.of X)).X 1 →ₗ[ℤ] V :=
  s4_c1a6_simplexLinear (TopCat.of X) 1 (s4_c1a6_liftDisplacement π hπ f hf)

theorem s4_c1a6_liftChain_project :
    π.toIntLinearMap.comp (s4_c1a6_liftChain π hπ f hf) =
      (s4_c1a6_simplexLinear (TopCat.of X) 0 (fun σ => f (TopCat.toSSetObj₀Equiv σ))).comp
        ((s4_c1a6_ZChains (TopCat.of X)).d 1 0).hom := by
  unfold s4_c1a6_liftChain
  rw [s4_c1a6_simplexLinear_comp, s4_c1a6_simplexLinear_boundary]
  congr 1
  funext σ
  exact s4_c1a6_liftDisplacement_project π hπ f hf σ

theorem s4_c1a6_liftChain_cycle_project_zero
    (z : (s4_c1a6_ZChains (TopCat.of X)).cycles 1) :
    π (s4_c1a6_liftChain π hπ f hf
      ((s4_c1a6_ZChains (TopCat.of X)).iCycles 1 z)) = 0 := by
  have hz : ((s4_c1a6_ZChains (TopCat.of X)).d 1 0).hom
      ((s4_c1a6_ZChains (TopCat.of X)).iCycles 1 z) = 0 :=
    congrArg (fun k => k.hom z) ((s4_c1a6_ZChains (TopCat.of X)).iCycles_d 1 0)
  have h := LinearMap.congr_fun (s4_c1a6_liftChain_project π hπ f hf)
    ((s4_c1a6_ZChains (TopCat.of X)).iCycles 1 z)
  change π (s4_c1a6_liftChain π hπ f hf
    ((s4_c1a6_ZChains (TopCat.of X)).iCycles 1 z)) =
      s4_c1a6_simplexLinear (TopCat.of X) 0 (fun σ => f (TopCat.toSSetObj₀Equiv σ))
        (((s4_c1a6_ZChains (TopCat.of X)).d 1 0).hom
          ((s4_c1a6_ZChains (TopCat.of X)).iCycles 1 z)) at h
  exact h.trans ((congrArg _ hz).trans (map_zero _))

end HodgeLean.Foundations.Program
