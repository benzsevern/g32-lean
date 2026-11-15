import HodgeLean.Foundations.Analytic.Analytification

/-! # Literal complex linear combinations of holomorphic chart coordinates
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
open TopologicalSpace HodgeLean.Foundations.Analytic
namespace HodgeLean.Foundations.QuotientDuality

/-- Actual complex linear combinations of finitely many holomorphic product coordinates remain holomorphic on the original source.
Source: an_Atlas.IsHolFun; AnalyticAt.comp; analyticAt_pi_iff.
HC no distance; AV milestone no distance. -/
lemma properCycle_holomorphic_linear_coordinates
    {X : Type} [TopologicalSpace X] (S : an_ReducedSpace X) (U : Set X)
    (r d n : ℕ) (f : U → ((Fin r → ℂ) × (Fin d → ℂ)))
    (hf : (∀ i, S.IsHolFun (fun x => (f x).1 i)) ∧
      ∀ i, S.IsHolFun (fun x => (f x).2 i))
    (L : ((Fin r → ℂ) × (Fin d → ℂ)) →L[ℂ] (Fin n → ℂ)) :
    ∀ k, S.IsHolFun (fun x => L (f x) k) := by
  intro k x j hx
  let I := Fin r ⊕ Fin d
  let g : I → U → ℂ := Sum.elim (fun i x => (f x).1 i) (fun i x => (f x).2 i)
  have hg (i : I) : S.IsHolFun (g i) := by
    cases i with
    | inl i => exact hf.1 i
    | inr i => exact hf.2 i
  have hcoord (i : I) := hg i x j hx
  choose V hV hxV G hG hEq using hcoord
  let W : Set X := ⋂ i : I, V i
  have hW : IsOpen W := isOpen_iInter_of_finite hV
  have hxW : x.val ∈ W := Set.mem_iInter.mpr hxV
  let F : (Fin (S.atlas.chart j).n → ℂ) → ((Fin r → ℂ) × (Fin d → ℂ)) :=
    fun v => (fun i => G (Sum.inl i) v, fun i => G (Sum.inr i) v)
  have hF : AnalyticAt ℂ F ((S.atlas.chart j).toFun x.val) :=
    (analyticAt_pi_iff.mpr (fun i => hG (Sum.inl i))).prod
      (analyticAt_pi_iff.mpr (fun i => hG (Sum.inr i)))
  refine ⟨W, hW, hxW, fun v => L (F v) k, ?_, ?_⟩
  · exact ((ContinuousLinearMap.proj k).analyticAt _).comp ((L.analyticAt _).comp hF)
  · intro y hy
    have hvalue : f y = F ((S.atlas.chart j).toFun y.val) := by
      apply Prod.ext
      · funext i
        exact hEq (Sum.inl i) y ⟨Set.mem_iInter.mp hy.1 (Sum.inl i), hy.2⟩
      · funext i
        exact hEq (Sum.inr i) y ⟨Set.mem_iInter.mp hy.1 (Sum.inr i), hy.2⟩
    exact congrArg (fun v => L v k) hvalue

end HodgeLean.Foundations.QuotientDuality
