import HodgeLean.Foundations.Program.G32Native.PairedResidualTorusChartLift
import HodgeLean.Foundations.Program.G32Native.AbelCollisionCurveCoefficients
import HodgeLean.Foundations.Program.SchoenCycleS1j1

/-! # Actual Abel lifts in the supplied symmetric quotient's monic coordinates -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint Filter
open HodgeLean.Adapters HodgeLean.Foundations.Curves.AbelAdapter
open HodgeLean.Foundations.Curves.AbelAdapter.StageTwo
open scoped TensorProduct BigOperators Topology Manifold ContDiff
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Program
variable (Z : Over (Spec ↧ℂ)) [IsIntegral Z.left] [Smooth Z.hom]
  [SmoothOfRelativeDimension 1 Z.hom] [IsProjective Z.hom]
local instance : ConnectedSpace (ComplexPoint Z) := AlgebraicGeometry.ComplexPoint.connectedSpace Z
local notation "hOne" => (Module.finrank_fin_fun (n := 1) ℂ)

/-- A holomorphic torus sum on the specified symmetric quotient has analytic
monic-coordinate lifts with its literal evaluation on every root block.
Source: Schoen, Compositio Mathematica 65 (1988), Lemmas 2.2–2.6;
Forster, Lectures on Riemann Surfaces, §21. -/
theorem residual_monic_torus_lift_from_native
    (B : Over (Spec ↧ℂ)) [IsIntegral B.left] (n : ℕ)
    [SmoothOfRelativeDimension n B.hom]
    (γ : g3_power Z n ⟶ B) [IsFinite γ.left] [Surjective γ.left]
    (hγ : ∀ σ, s2_permute Z n σ ≫ γ = γ)
    (hquot : ∀ (T : Over (Spec ↧ℂ)) (v : g3_power Z n ⟶ T),
      (∀ σ, s2_permute Z n σ ≫ v = v) → ∃! u : B ⟶ T, γ ≫ u = v)
    {L : Type} [AddCommGroup L] [Module.Finite ℤ L]
    (F : Submodule ℂ (ℂ ⊗[ℤ] L)) [DiscreteTopology (b2_latticeMap L F).range]
    (s : ComplexPoint B → b2_torus L F)
    (α : ComplexPoint Z → b2_torus L F)
    (hsum : ∀ u, s (Point.map γ u) = ∑ i, α (Point.map (g3_proj Z n i) u))
    (x : ComplexPoint (g3_power Z n)) (b : ℕ) (m : Fin b → ℕ)
    (hm : ∀ j, 0 < m j) (ι : (Σ j, Fin (m j)) ≃ Fin n)
    (q : Fin b → ComplexPoint Z) (hq : Function.Injective q)
    (hx : ∀ j l, Point.map (g3_proj Z n (ι ⟨j, l⟩)) x = q j)
    (g : (Fin n → ℂ) → b5_V L F)
    (hg : AnalyticAt ℂ g (localChart B n (Point.map γ x) (Point.map γ x)))
    (hgc : ∀ᶠ w in 𝓝 (Point.map γ x),
      b2_torusCover L F (g (localChart B n (Point.map γ x) w)) = s w) :
    ∃ T : ((Σ j, Fin (m j)) → ℂ) → (Fin n → ℂ),
      T 0 = localChart B n (Point.map γ x) (Point.map γ x) ∧
      AnalyticAt ℂ T 0 ∧ AnalyticAt ℂ (g ∘ T) 0 ∧
      ∀ᶠ z in 𝓝 (0 : (Σ j, Fin (m j)) → ℂ),
        b2_torusCover L F ((g ∘ T) (collisionBlockCoefficients m z)) =
          ∑ t : Σ j, Fin (m j),
            α (b3A_disc (q t.1) (b4cov_lineEquiv hOne 1) (z t)) := by
  classical
  let w := Point.map γ x
  let C := localChart B n w
  obtain ⟨e, he, he0, _, hei, hcoef⟩ :=
    s2e_mixed_coefficient_neighbourhood Z B n γ hγ hquot x b m hm ι q hq hx
  let R : ((Σ j, Fin (m j)) → ℂ) →L[ℂ] (Fin n → ℂ) :=
    ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj (ι.symm i)
  let T := fun u => C (e.symm (R u))
  have hi0 : e.symm 0 = w := by
    rw [← he0]
    exact e.left_inv he
  have hT0 : T 0 = C w := by simp only [T, map_zero, hi0]
  have hTa : AnalyticAt ℂ T 0 := hei.comp_of_eq (R.analyticAt 0) (map_zero R)
  have hga : AnalyticAt ℂ g (T 0) := hT0.symm ▸ hg
  refine ⟨T, hT0, hTa, hga.comp hTa, ?_⟩
  let r := fun z => Point.map γ (collisionCurveTuple Z m ι q z)
  have hr : ContinuousAt r 0 := (Point.continuous_map γ).continuousAt.comp
    (collisionCurveTuple_continuousAt Z m ι q)
  have hr0 : r 0 = w := by
    change Point.map γ (collisionCurveTuple Z m ι q 0) = _
    rw [collisionCurveTuple_zero Z m ι q x hx]
  have hroots : ∀ᶠ z in 𝓝 (0 : (Σ j, Fin (m j)) → ℂ),
      e (r z) = R (collisionBlockCoefficients m z) := by
    filter_upwards [collision_curve_tuple_coefficients Z B γ x m ι q hx e hcoef] with z hz
    funext i
    obtain ⟨⟨j, l⟩, rfl⟩ := ι.surjective i
    simpa only [R, ContinuousLinearMap.pi_apply, ContinuousLinearMap.proj_apply,
      Equiv.symm_apply_apply] using hz j l
  have hrt : Tendsto r (𝓝 0) (𝓝 w) := hr0 ▸ hr.tendsto
  have hsource : ∀ᶠ z in 𝓝 (0 : (Σ j, Fin (m j)) → ℂ), r z ∈ e.source :=
    hrt.eventually (e.open_source.mem_nhds he)
  filter_upwards [hroots, hsource, hrt.eventually hgc] with z hz hsz hc
  have hinv : e.symm (R (collisionBlockCoefficients m z)) = r z :=
    (congrArg e.symm hz).symm.trans (e.left_inv hsz)
  change b2_torusCover L F (g (C (e.symm (R (collisionBlockCoefficients m z))))) = _
  rw [hinv, hc]
  refine (hsum (collisionCurveTuple Z m ι q z)).trans ?_
  rw [← Equiv.sum_comp ι]
  apply Finset.sum_congr rfl
  intro s _
  rw [collisionCurveTuple_projection]

#print axioms residual_monic_torus_lift_from_native

/-- A holomorphic torus sum on the specified symmetric quotient has analytic
monic-coordinate lifts with its literal evaluation on every root block.
Source: Schoen, Compositio Mathematica 65 (1988), Lemmas 2.2–2.6;
Forster, Lectures on Riemann Surfaces, §21. -/
theorem residual_monic_torus_lift
    (B : Over (Spec ↧ℂ)) [IsIntegral B.left] (n : ℕ)
    [SmoothOfRelativeDimension n B.hom]
    (γ : g3_power Z n ⟶ B) [IsFinite γ.left] [Surjective γ.left]
    (hγ : ∀ σ, s2_permute Z n σ ≫ γ = γ)
    (hquot : ∀ (T : Over (Spec ↧ℂ)) (v : g3_power Z n ⟶ T),
      (∀ σ, s2_permute Z n σ ≫ v = v) → ∃! u : B ⟶ T, γ ≫ u = v)
    {L : Type} [AddCommGroup L] [Module.Finite ℤ L]
    (F : Submodule ℂ (ℂ ⊗[ℤ] L)) [DiscreteTopology (b2_latticeMap L F).range]
    (s : ComplexPoint B → b2_torus L F)
    (hs : ContMDiff 𝓘(ℂ, Fin n → ℂ) 𝓘(ℂ, b5_V L F) ω s)
    (α : ComplexPoint Z → b2_torus L F)
    (hsum : ∀ u, s (Point.map γ u) = ∑ i, α (Point.map (g3_proj Z n i) u))
    (x : ComplexPoint (g3_power Z n)) (b : ℕ) (m : Fin b → ℕ)
    (hm : ∀ j, 0 < m j) (ι : (Σ j, Fin (m j)) ≃ Fin n)
    (q : Fin b → ComplexPoint Z) (hq : Function.Injective q)
    (hx : ∀ j l, Point.map (g3_proj Z n (ι ⟨j, l⟩)) x = q j) :
    ∃ f : ((Σ j, Fin (m j)) → ℂ) → b5_V L F,
      AnalyticAt ℂ f 0 ∧
      ∀ᶠ z in 𝓝 (0 : (Σ j, Fin (m j)) → ℂ),
        b2_torusCover L F (f (collisionBlockCoefficients m z)) =
          ∑ s : Σ j, Fin (m j),
            α (b3A_disc (q s.1) (b4cov_lineEquiv hOne 1) (z s)) := by
  obtain ⟨g, hg, hgc⟩ := residual_torus_native_chart_lift B n F s hs (Point.map γ x)
  obtain ⟨T, _, _, hf, he⟩ := residual_monic_torus_lift_from_native Z B n γ hγ hquot
    F s α hsum x b m hm ι q hq hx g hg hgc
  exact ⟨g ∘ T, hf, he⟩

#print axioms residual_monic_torus_lift
end HodgeLean.Foundations.Program.G32Native
