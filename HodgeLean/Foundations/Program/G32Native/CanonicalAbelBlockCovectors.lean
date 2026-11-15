import HodgeLean.Foundations.Program.G32Native.CanonicalAbelCoefficientSheet
import HodgeLean.Foundations.Program.G32Native.AbelCollisionCurveCoefficients
import HodgeLean.Foundations.Program.G32Native.CanonicalCurveCoefficientPrimitive
import HodgeLean.Foundations.Program.G32Native.CanonicalCoefficientFunctional
import HodgeLean.Foundations.Program.G32Native.AbelCollisionLiftJets
import HodgeLean.Foundations.Program.G32Native.AbelRootSheetEvaluation

/-! # Original Abel covectors retain all collision-block vanishing orders -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint Filter
open HodgeLean.Adapters HodgeLean.Foundations.Curves.AbelAdapter.StageTwo
open HodgeLean.Foundations.Curves.AbelAdapter
open scoped Topology BigOperators
namespace HodgeLean.Foundations.Program.G32Native

/-- An annihilating original Abel covector has every local multiplicity of the marked root blocks. -/
theorem canonical_abel_covector_block_orders (G : CanonicalAbelGeometry) (p : ComplexPoint G.Z)
    (F : ComplexPoint G.Q → (Fin (G.k + G.k) → ℂ) → (Fin (G.k + 1) → ℂ))
    (x : ComplexPoint G.Q)
    (hFa : AnalyticAt ℂ (F x)
      (localChart G.W (G.k + G.k) (Point.map G.ι x) (Point.map G.ι x)))
    (hFe : ∀ᶠ w in 𝓝 (Point.map G.ι x), ∀ z : Fin (2 * G.k) → ComplexPoint G.Z,
      Point.map G.γ (s2_lift (2 * G.k) z) = Point.map G.β w →
      canonicalPeriodQuotient G (F x (localChart G.W (G.k + G.k) (Point.map G.ι x) w)) =
        ∑ i, analyticAbel (Module.finrank_fin_fun (n := 1) ℂ) p (z i))
    (z : ComplexPoint (g3_power G.Z (2 * G.k)))
    (hz : Point.map G.γ z = Point.map G.β (Point.map G.ι x))
    (b : ℕ) (m : Fin b → ℕ) (hm : ∀ a, 0 < m a)
    (ι : (Σ a, Fin (m a)) ≃ Fin (2 * G.k))
    (q : Fin b → ComplexPoint G.Z) (hq : Function.Injective q)
    (hzq : ∀ a i, Point.map (g3_proj G.Z (2 * G.k) (ι ⟨a, i⟩)) z = q a)
    (a : Fin (G.k + 1) → ℂ)
    (hzero : ∀ v, canonicalAbelDifferential G F x v a = 0) :
    ∀ j, (m j : ℕ∞) ≤ analyticOrderAt
      (HurwitzPrymRR_loc (Module.finrank_fin_fun (n := 1) ℂ) (canonicalCoefficientForm G a) (q j)) 0 := by
  let h := Module.finrank_fin_fun (n := 1) ℂ
  letI := b3_periodLattice_finite (C := ComplexPoint G.Z) h
  letI := b3_periodLattice_free (E := Fin 1 → ℂ) (C := ComplexPoint G.Z)
  letI := b2_latticeMap_discrete _ (b3_isWeightOne (C := ComplexPoint G.Z) h)
  let w := Point.map G.ι x
  let D := localChart G.W (G.k + G.k) w
  obtain ⟨e, he, he0, s, hs0, hsc, hsa, hse, hecoef⟩ :=
    canonical_abel_coefficient_sheet G w z hz b m hm ι q hq hzq
  let R : ((Σ j, Fin (m j)) → ℂ) →L[ℂ] (Fin (2 * G.k) → ℂ) :=
    ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj (ι.symm i)
  let U := fun c => D (s (R c))
  have hU0 : U 0 = D w := by simp only [U, map_zero, hs0]
  have hsaR : AnalyticAt ℂ (fun c => D (s c)) (R 0) := by
    rw [map_zero]
    exact hsa
  have hUa : AnalyticAt ℂ U 0 := hsaR.comp (R.analyticAt 0)
  have hFat : AnalyticAt ℂ (F x) (U 0) := by rw [hU0]; exact hFa
  let f := F x ∘ U
  have hfa : AnalyticAt ℂ f 0 := hFat.comp hUa
  let ℓ := canonicalCoefficientFunctional G a
  have hscalar : fderiv ℂ (ℓ ∘ f) 0 = 0 := by
    have hd := fderiv_comp 0 ((ℓ.differentiableAt).comp (U 0) hFat.differentiableAt)
      hUa.differentiableAt
    change fderiv ℂ (ℓ ∘ f) 0 = _ at hd
    rw [hU0, canonical_covector_scalar_derivative_zero G F x a hFa.differentiableAt hzero,
      ContinuousLinearMap.zero_comp] at hd
    exact hd
  choose g hg using (fun j : Fin b => canonical_curve_coefficient_primitive G p (q j))
  have hga (j : Fin b) := (hg j).1
  have hgc (j : Fin b) := (hg j).2.1
  have hgd (j : Fin b) := (hg j).2.2
  let P := fun u => R (collisionBlockCoefficients m u)
  have hPc : ContinuousAt P 0 := R.continuous.continuousAt.comp (collisionBlockCoefficients_continuous m).continuousAt
  have hP0 : P 0 = 0 := by simp only [P, collisionBlockCoefficients_zero, map_zero]
  let r := fun u => Point.map G.γ (collisionCurveTuple G.Z m ι q u)
  have hrc : ContinuousAt r 0 := (Point.continuous_map G.γ).continuousAt.comp
    (collisionCurveTuple_continuousAt G.Z m ι q)
  have hr0 : r 0 = Point.map G.β w := by
    change Point.map G.γ (collisionCurveTuple G.Z m ι q 0) = _
    rw [collisionCurveTuple_zero G.Z m ι q z hzq, hz]
  have hroots : ∀ᶠ u in 𝓝 (0 : (Σ j, Fin (m j)) → ℂ), e (r u) = P u := by
    filter_upwards [collision_curve_tuple_coefficients G.Z G.B G.γ z m ι q hzq e hecoef] with u hu
    funext i
    obtain ⟨⟨j, l⟩, rfl⟩ := ι.surjective i
    simpa only [P, R, ContinuousLinearMap.pi_apply, ContinuousLinearMap.proj_apply,
      Equiv.symm_apply_apply] using hu j l
  have hsroots := root_sheet_evaluation (Point.map G.β) e s P r hPc hP0 hrc
    (by rw [hr0]; exact he) hse hroots
  have hsw : Tendsto (fun u => s (P u)) (𝓝 0) (𝓝 w) := by
    have hc := hsc.comp_of_eq hPc hP0
    have ht := hc.tendsto
    change Tendsto (fun u => s (P u)) (𝓝 0) (𝓝 (s (P 0))) at ht
    rw [hP0, hs0] at ht
    exact ht
  have hgcover : ∀ᶠ u in 𝓝 (0 : (Σ j, Fin (m j)) → ℂ), ∀ t : Σ j, Fin (m j),
      canonicalPeriodHom G (g t.1 (u t)) =
        analyticAbel h p (b3A_disc (q t.1) (b4cov_lineEquiv h 1) (u t)) := by
    apply eventually_all.mpr
    intro t
    have ht : Tendsto (fun u : (Σ j, Fin (m j)) → ℂ => u t) (𝓝 0) (𝓝 0) :=
      (continuous_apply t).continuousAt.tendsto
    exact ht.eventually (hgc t.1)
  have htrace : ∀ᶠ u in 𝓝 (0 : (Σ j, Fin (m j)) → ℂ),
      canonicalPeriodHom G (f (collisionBlockCoefficients m u)) =
        ∑ t : Σ j, Fin (m j), canonicalPeriodHom G (g t.1 (u t)) := by
    filter_upwards [hsw.eventually hFe, hsroots, hgcover] with u hFu hru hgu
    have hval := hFu (fun i => b3A_disc (q (ι.symm i).1)
      (b4cov_lineEquiv h 1) (u (ι.symm i))) hru.symm
    change canonicalPeriodHom G (f (collisionBlockCoefficients m u)) = _ at hval
    rw [← Equiv.sum_comp ι] at hval
    exact hval.trans (by apply Finset.sum_congr rfl; intro t _; simpa only [Equiv.symm_apply_apply] using (hgu t).symm)
  have hjets := collision_quotient_lift_jet_orders m (canonicalPeriodHom G)
    (canonicalPeriodQuotient_isLocalHomeomorph G) f hfa.differentiableAt g hga ℓ hscalar htrace
  intro j
  have heq : deriv (ℓ ∘ g j) =ᶠ[𝓝 0]
      HurwitzPrymRR_loc h (canonicalCoefficientForm G a) (q j) := hgd j a
  rw [← analyticOrderAt_congr heq]
  exact hjets j

#print axioms canonical_abel_covector_block_orders
end HodgeLean.Foundations.Program.G32Native
