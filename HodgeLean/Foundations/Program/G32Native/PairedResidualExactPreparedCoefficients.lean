import HodgeLean.Foundations.Program.G32Native.PairedResidualRetainedDivisor
import HodgeLean.Foundations.Program.G32Native.PairedResidualGivenPreparationClusters
import HodgeLean.Foundations.Program.G32Native.PairedResidualPrescribedPreparation
import HodgeLean.Foundations.Program.G32Native.PairedResidualSystemEvaluation
import HodgeLean.Foundations.Program.SchoenCyclePairedEvaluation
import HodgeLean.Foundations.Program.SchoenCycleS1j1
import HodgeLean.Foundations.Program.SchoenCyclePairedDivisorRecovery
import HodgeLean.Foundations.Program.SchoenCyclePrescribedPreparation
import HodgeLean.Foundations.Program.SchoenCycleBlockMultiplicity
import HodgeLean.Foundations.Program.SchoenCycleGivenPreparationClusters
import HodgeLean.Foundations.Program.SchoenCyclePreparedChartComparison

/-! # Exact S1 pullback of prepared coefficients
Implication from the explicit inputs to the stated local comparisons.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint MvPolynomial
open Filter Topology Manifold HodgeLean.Adapters
open HodgeLean.Foundations.AnalyticDivisorAlgebraic4
open scoped BigOperators ContDiff Classical
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Program

/-- Supplied full-system preparations equal the actual retained block coefficients. -/
theorem residual_system_exact_prepared_coefficients
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
    [SmoothOfRelativeDimension (2 * k) B.hom]
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
    (x : ComplexPoint (g3_power Z (2 * k)))
    (hx : Point.map γ x = Point.map ℓ (A 0))
    (s : ℕ) (m : Fin s → ℕ) (hm : ∀ l, 0 < m l)
    (ι : (Σ l, Fin (m l)) ≃ Fin (2 * k))
    (p : Fin s → ComplexPoint Z) (hp : Function.Injective p)
    (hxp : ∀ l i, Point.map (g3_proj Z (2 * k) (ι ⟨l, i⟩)) x = p l)
    (e : OpenPartialHomeomorph (ComplexPoint B) (Fin (2 * k) → ℂ))
    (he : ∀ᶠ q in 𝓝 x, ∀ l (j : Fin (m l)),
      e (Point.map γ q) (ι ⟨l, j⟩) =
        (-1 : ℂ) ^ (m l - j.val) *
        aeval (fun i : Fin (m l) =>
          (b4cov_lineEquiv (Module.finrank_fin_fun (n := 1) ℂ)).symm
            (extChartAt 𝓘(ℂ, Fin 1 → ℂ) (p l)
              (Point.map (g3_proj Z (2 * k) (ι ⟨l, i⟩)) q) -
             extChartAt 𝓘(ℂ, Fin 1 → ℂ) (p l) (p l)))
          (esymm (Fin (m l)) ℂ (m l - j.val)))
    (l : Fin s) :
    ∃ (g u : (Fin (d + 1) → ℂ) × ℂ → ℂ)
      (c : Fin (m l) → (Fin (d + 1) → ℂ) → ℂ),
      (∀ t, AnalyticAt ℂ g (t, 0)) ∧
      (∀ᶠ z in 𝓝[≠] (0 : ℂ), ∀ t,
        (if p l ∈ Set.range y then z else 1) *
          HurwitzPrymRR_loc (Module.finrank_fin_fun (n := 1) ℂ)
            (((∑ i, t i • b i) : W).val) (p l) z = g (t, z)) ∧
      AnalyticAt ℂ u 0 ∧ u 0 ≠ 0 ∧
      (∀ j, AnalyticAt ℂ (c j) 0 ∧ c j 0 = 0) ∧
      ((fun tz => g (a + tz.1, tz.2)) =ᶠ[𝓝 0]
        fun tz => u tz * monicInLast c tz) ∧
      (∀ᶠ t in 𝓝 0, ∀ j, c j t = e (Point.map ℓ (A t)) (ι ⟨l, j⟩)) := by
  letI : ConnectedSpace (ComplexPoint Z) := AlgebraicGeometry.ComplexPoint.connectedSpace Z
  dsimp only at hA hℓ
  have hcentral : residualProjectiveSystemPoint (Module.finrank_fin_fun (n := 1) ℂ) y hy W hW hgenus γ id
      (Projectivization.mk ℂ (∑ i, a i • b i) ha) = Point.map γ x := by
    obtain ⟨ha0, hAt0⟩ := hA.self_of_nhds
    simp only [add_zero] at ha0 hAt0
    rw [hx, hℓ, hAt0]
    dsimp only
    rw [Equiv.symm_apply_apply]
  have hD := residual_system_divisor_of_retained_lift Z B k r y hy W hW hgenus γ hγ hsurj hquot (∑ i, a i • b i) ha x hcentral
  have hmult (l : Fin s) : (m l : ℤ) =
      (b4c_divForm (hE := (Module.finrank_fin_fun (n := 1) ℂ)) ((∑ i, a i • b i) : W).val + s2e_markedPoleDivisor y) (p l) := by
    rw [hD]
    exact (s2e_block_tuple_divisor_multiplicity m ι p hp
      (fun i => Point.map (g3_proj Z (2 * k) i) x) hxp l).symm
  have hsum : ∑ l, m l = 2 * k := by
    simpa only [Fintype.card_sigma, Fintype.card_fin] using Fintype.card_congr ι
  choose g hg heG ho u hu hu0 c hc hprep using fun l =>
    residual_system_prescribed_preparation (Module.finrank_fin_fun (n := 1) ℂ) y hy W hW (fun i => b i) (p l) a ha (m l) (hmult l)
  have hcluster := residual_system_given_preparations_cluster_divisors
    (Module.finrank_fin_fun (n := 1) ℂ) y hy W hW hgenus
    (fun i => b i) a ha m hsum p hp g u c heG hu hu0 hprep
    (fun l j => (hc l j).1.continuousAt) (fun l j => (hc l j).2)
  have hcoeff : ∀ᶠ t in 𝓝 (0 : Fin (d + 1) → ℂ), ∀ l j,
      c l j t = e (Point.map ℓ (A t)) (ι ⟨l, j⟩) := by
    apply s2e_prepared_clusters_eq_retained_coefficients Z B (2 * k) s (d + 1)
      γ x m ι p hxp e he c (fun l j => (hc l j).1.continuousAt)
      (fun l j => (hc l j).2) (fun t => Point.map ℓ (A t))
    filter_upwards [hcluster, hA] with t ht hAt
    obtain ⟨hne, hAt⟩ := hAt
    intro z hz
    have hev := residual_system_quotient_eq_clusters Z B k r y hy W hW hgenus γ hγ (∑ i, (a + t) i • b i) ht.1 m ι.symm
      (fun l j => (extChartAt 𝓘(ℂ, Fin 1 → ℂ) (p l)).symm
        (extChartAt 𝓘(ℂ, Fin 1 → ℂ) (p l) (p l) +
          b4cov_lineEquiv (Module.finrank_fin_fun (n := 1) ℂ) (z l j))) (ht.2 z hz)
    refine hev.symm.trans ?_
    rw [hℓ, hAt]
    dsimp only
    rw [Equiv.symm_apply_apply]
  refine ⟨g l, u l, c l, hg l, heG l, hu l, hu0 l, hc l, hprep l, ?_⟩
  filter_upwards [hcoeff] with t ht
  exact ht l

#print axioms residual_system_exact_prepared_coefficients
end HodgeLean.Foundations.Program.G32Native
