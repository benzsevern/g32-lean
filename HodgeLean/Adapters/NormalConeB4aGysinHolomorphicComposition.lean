import HodgeLean.Adapters.NormalConeB4aClassHolomorphicCoordinates

noncomputable section
namespace HodgeLean.Adapters
open HodgeLean.Foundations.Analytic

/-- Analytic functions of finitely many holomorphic coordinates are holomorphic
on a reduced analytic space, without a smoothness assumption. -/
theorem a3b4a_gysin_holomorphic_coordinate_composition
    {Y : Type*} [TopologicalSpace Y] (S : an_ReducedSpace Y)
    {U : Set Y} {n : ℕ} (g : U → (Fin n → ℂ))
    (hg : ∀ j, S.IsHolFun (fun y => g y j))
    (G : (Fin n → ℂ) → ℂ) (hG : ∀ y, AnalyticAt ℂ G (g y)) :
    S.IsHolFun (fun y => G (g y)) := by
  intro x i hx
  choose N hN hxN H hH hEq using fun j => hg j x i hx
  let H' : (Fin (S.atlas.chart i).n → ℂ) → (Fin n → ℂ) := fun z j => H j z
  have hH' : AnalyticAt ℂ H' ((S.atlas.chart i).toFun x) :=
    analyticAt_pi_iff.mpr hH
  have hvalue : H' ((S.atlas.chart i).toFun x) = g x := by
    funext j
    exact (hEq j x ⟨hxN j, hx⟩).symm
  have hG' : AnalyticAt ℂ G (H' ((S.atlas.chart i).toFun x)) := by
    rw [hvalue]
    exact hG x
  refine ⟨⋂ j, N j, isOpen_iInter_of_finite hN, Set.mem_iInter.mpr hxN,
    G ∘ H', hG'.comp hH', ?_⟩
  intro y hy
  apply congrArg G
  funext j
  exact hEq j y ⟨Set.mem_iInter.mp hy.1 j, hy.2⟩

end HodgeLean.Adapters
