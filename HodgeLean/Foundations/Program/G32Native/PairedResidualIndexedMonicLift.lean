import HodgeLean.Foundations.Program.G32Native.PairedResidualMonicTorusLift
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
theorem residual_monic_torus_lift_indexed_from_native
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
    (x : ComplexPoint (g3_power Z n))
    {A : Type} [Fintype A] [DecidableEq A] (m : A → ℕ)
    (hm : ∀ j, 0 < m j) (ι : (Σ j, Fin (m j)) ≃ Fin n)
    (q : A → ComplexPoint Z) (hq : Function.Injective q)
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
  let e := (Fintype.equivFin A).symm
  let mF := fun j : Fin (Fintype.card A) => m (e j)
  let E : (Σ j, Fin (mF j)) ≃ (Σ j, Fin (m j)) := Equiv.sigmaCongrLeft (β := fun j : A => Fin (m j)) e
  obtain ⟨T, hT0, hTa, hf, he⟩ := residual_monic_torus_lift_from_native Z B n γ hγ hquot F s α hsum
    x (Fintype.card A) mF (fun j => hm (e j)) (E.trans ι)
    (q ∘ e) (hq.comp e.injective) (fun j l => hx (e j) l) g hg hgc
  let R : ((Σ j, Fin (m j)) → ℂ) →L[ℂ] ((Σ j, Fin (mF j)) → ℂ) :=
    ContinuousLinearMap.pi fun t => ContinuousLinearMap.proj (E t)
  have hfR : AnalyticAt ℂ (g ∘ T) (R 0) := (map_zero R).symm ▸ hf
  have hTR : AnalyticAt ℂ T (R 0) := (map_zero R).symm ▸ hTa
  refine ⟨T ∘ R, ?_, hTR.comp (R.analyticAt 0), hfR.comp (R.analyticAt 0), ?_⟩
  · change T (R 0) = _
    rw [map_zero, hT0]
  ·
    have hrt : Tendsto R (𝓝 0) (𝓝 0) := by
      have ht : Tendsto R (𝓝 (0 : (Σ j, Fin (m j)) → ℂ)) (𝓝 (R 0)) :=
        R.continuous.continuousAt.tendsto
      rw [map_zero] at ht
      exact ht
    filter_upwards [hrt.eventually he] with z hz
    have hcomm : R (collisionBlockCoefficients m z) = collisionBlockCoefficients mF (R z) := by
      funext t
      rfl
    change b2_torusCover L F ((g ∘ T) (R (collisionBlockCoefficients m z))) = _
    rw [hcomm]
    exact hz.trans (E.sum_comp (fun t : Σ j, Fin (m j) =>
      α (b3A_disc (q t.1) (b4cov_lineEquiv hOne 1) (z t))))

#print axioms residual_monic_torus_lift_indexed_from_native

/-- A holomorphic torus sum on the specified symmetric quotient has analytic
monic-coordinate lifts with its literal evaluation on every root block.
Source: Schoen, Compositio Mathematica 65 (1988), Lemmas 2.2–2.6;
Forster, Lectures on Riemann Surfaces, §21. -/
theorem residual_monic_torus_lift_indexed
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
    (x : ComplexPoint (g3_power Z n))
    {A : Type} [Fintype A] [DecidableEq A] (m : A → ℕ)
    (hm : ∀ j, 0 < m j) (ι : (Σ j, Fin (m j)) ≃ Fin n)
    (q : A → ComplexPoint Z) (hq : Function.Injective q)
    (hx : ∀ j l, Point.map (g3_proj Z n (ι ⟨j, l⟩)) x = q j) :
    ∃ f : ((Σ j, Fin (m j)) → ℂ) → b5_V L F,
      AnalyticAt ℂ f 0 ∧
      ∀ᶠ z in 𝓝 (0 : (Σ j, Fin (m j)) → ℂ),
        b2_torusCover L F (f (collisionBlockCoefficients m z)) =
          ∑ s : Σ j, Fin (m j),
            α (b3A_disc (q s.1) (b4cov_lineEquiv hOne 1) (z s)) := by
  obtain ⟨g, hg, hgc⟩ := residual_torus_native_chart_lift B n F s hs (Point.map γ x)
  obtain ⟨T, _, _, hf, he⟩ := residual_monic_torus_lift_indexed_from_native Z B n γ hγ hquot
    F s α hsum x m hm ι q hq hx g hg hgc
  exact ⟨g ∘ T, hf, he⟩

#print axioms residual_monic_torus_lift_indexed
end HodgeLean.Foundations.Program.G32Native
