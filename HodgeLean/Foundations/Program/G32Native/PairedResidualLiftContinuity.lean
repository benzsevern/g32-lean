import HodgeLean.Foundations.Program.G32Native.PairedResidualSystemEvaluation
import HodgeLean.Foundations.Program.SchoenCycleS1j2
import HodgeLean.Foundations.Program.SchoenCycleStationaryAnalyticCoordinates
import HodgeLean.Foundations.Program.SchoenCyclePairedOffDivisorVariation
import HodgeLean.Foundations.Program.SchoenCycleFiniteBlockPartition

/-! # Scalar kernel for paired projective parameter curves -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint Filter Topology Manifold
open HodgeLean.Adapters
open scoped BigOperators ContDiff Classical
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Program

/-- The specified full-system homogeneous lift remains continuous through collisions. -/
theorem residual_system_homogeneous_lift_continuousAt
    (Z B : Over (Spec ↧ℂ)) [IsIntegral Z.left] [Smooth Z.hom]
    [SmoothOfRelativeDimension 1 Z.hom] [IsProjective Z.hom]
    [IsIntegral B.left] [Smooth B.hom] [IsProjective B.hom]
    (k r d : ℕ)
    (y : Fin (2 * r) → ComplexPoint Z) (hy : Function.Injective y)
    (W : Submodule ℂ (TangentBundle 𝓘(ℂ, Fin 1 → ℂ) (ComplexPoint Z) → ℂ))
    (hW : ∀ q : W, b4c_IsMeroForm (Module.finrank_fin_fun (n := 1) ℂ) q.val ∧
      (∀ p, ((-1 : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt
        (HurwitzPrymRR_loc (Module.finrank_fin_fun (n := 1) ℂ) q.val p) 0) ∧
      (∀ p ∉ Set.range y, AnalyticAt ℂ
        (HurwitzPrymRR_loc (Module.finrank_fin_fun (n := 1) ℂ) q.val p) 0) ∧
      ∀ p ∈ Set.range y, ∀ u, q.val ⟨p, u⟩ = 0)
    [FiniteDimensional ℂ W]
    (hgenus : 2 * k + 2 = 2 * Module.finrank ℂ
      (b3_HolForm (Fin 1 → ℂ) (ComplexPoint Z)) + 2 * r)
    (hd : Module.finrank ℂ W = d + 1)
    (γ : g3_power Z (2 * k) ⟶ B) [IsFinite γ.left]
    (hγ : ∀ σ, s2_permute Z (2 * k) σ ≫ γ = γ)
    (hsurj : Function.Surjective (Point.map γ))
    (hquot : ∀ (T : Over (Spec ↧ℂ)) (v : g3_power Z (2 * k) ⟶ T),
      (∀ σ, s2_permute Z (2 * k) σ ≫ v = v) → ∃! u : B ⟶ T, γ ≫ u = v)
    (ℓ : Over.mk (ProjectiveSpace.toBase (Fin (d + 1)) (Spec ↧ℂ)) ⟶ B)
    (hℓ : let : ConnectedSpace (ComplexPoint Z) := AlgebraicGeometry.ComplexPoint.connectedSpace Z
      let ep := s2e_finiteDimensionalProjectivePointEquiv (V := W) d hd
      Point.map ℓ = fun R => residualProjectiveSystemPoint
        (Module.finrank_fin_fun (n := 1) ℂ) y hy W hW hgenus γ id (ep.symm R))
    (b : Module.Basis (Fin (d + 1)) ℂ
      W)
    (a : Fin (d + 1) → ℂ) (ha : (∑ i, a i • b i) ≠ 0)
    (A : (Fin (d + 1) → ℂ) →
      ComplexPoint (Over.mk (ProjectiveSpace.toBase (Fin (d + 1)) (Spec ↧ℂ))))
    (hA :
      let ep := s2e_finiteDimensionalProjectivePointEquiv
        (V := W) d hd
      ∀ᶠ t in 𝓝 0, ∃ ht : (∑ i, (a + t) i • b i) ≠ 0,
        A t = ep (Projectivization.mk ℂ (∑ i, (a + t) i • b i) ht))
    : ContinuousAt (fun t => Point.map ℓ (A t)) 0 := by
  letI : ConnectedSpace (ComplexPoint Z) := AlgebraicGeometry.ComplexPoint.connectedSpace Z
  dsimp only at hℓ hA
  let G := fun v : Fin (d + 1) → ℂ => Point.map ℓ (A (v - a))
  have ht : Tendsto (fun v : Fin (d + 1) → ℂ => v - a) (𝓝 a) (𝓝 0) := by
    simpa only [sub_self] using (show Continuous (fun v : Fin (d + 1) → ℂ => v - a) from
        continuous_id.sub continuous_const).tendsto a
  have hG : ContinuousAt G a := by
    apply residual_system_evaluation_continuousAt Z B k r y hy W hW hgenus γ hγ
      (fun i => b i) a ha G
    filter_upwards [ht.eventually hA] with v hv
    obtain ⟨hne, hv⟩ := hv
    have heq : a + (v - a) = v := by abel
    simp only [heq] at hne hv
    refine ⟨hne, ?_⟩
    change Point.map ℓ (A (v - a)) = _
    rw [hℓ, hv]
    dsimp only
    rw [Equiv.symm_apply_apply]
  have hh := hG.comp_of_eq (continuousAt_const.add continuousAt_id)
    (show a + (0 : Fin (d + 1) → ℂ) = a from add_zero a)
  change ContinuousAt (fun t : Fin (d + 1) → ℂ => Point.map ℓ (A ((a + t) - a))) 0 at hh
  simpa only [add_sub_cancel_left] using hh

#print axioms residual_system_homogeneous_lift_continuousAt
end HodgeLean.Foundations.Program.G32Native
