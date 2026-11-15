import HodgeLean.Foundations.Program.G32Native.PairedResidualPoleDivisors
import HodgeLean.Foundations.Program.SchoenCyclePoleClearing

/-! # Analytic coefficients for the full normalized pole system -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open HodgeLean.Adapters Filter Topology Manifold
open scoped BigOperators ContDiff
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Program
attribute [local instance] Classical.propDecidable
variable {E C : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace C] [ChartedSpace E C] [IsManifold 𝓘(ℂ, E) ω C]

/-- Every finite linear chart in the full pole space has jointly analytic corrected coefficients. -/
theorem residual_system_pole_correction
    (hE : Module.finrank ℂ E = 1) (S : Set C)
    (W : Submodule ℂ (TangentBundle 𝓘(ℂ, E) C → ℂ))
    (hW : ∀ q : W, b4c_IsMeroForm hE q.val ∧
      (∀ p, ((-1 : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt (HurwitzPrymRR_loc hE q.val p) 0) ∧
      ∀ p ∉ S, AnalyticAt ℂ (HurwitzPrymRR_loc hE q.val p) 0)
    {m : ℕ} (b : Fin m → W) (p : C) :
    ∃ g : (Fin m → ℂ) × ℂ → ℂ,
      (∀ a, AnalyticAt ℂ g (a, 0)) ∧
      (∀ᶠ z in 𝓝[≠] (0 : ℂ), ∀ a, (if p ∈ S then z else 1) *
        HurwitzPrymRR_loc hE (∑ i, a i • b i : W).val p z = g (a, z)) := by
  classical
  let f := fun i => HurwitzPrymRR_loc hE (b i).val p
  have heq (a : Fin m → ℂ) (z : ℂ) :
      HurwitzPrymRR_loc hE (∑ i, a i • b i : W).val p z = ∑ i, a i * f i z := by
    simp only [Submodule.coe_sum, Submodule.coe_smul, HurwitzPrymRR_loc, b4cov_coef,
      Finset.sum_apply, Pi.smul_apply, smul_eq_mul, f]
  by_cases hp : p ∈ S
  · obtain ⟨g, hg, he⟩ := s2e_linear_simple_pole_family f
      (fun i => (hW (b i)).1.2 p)
      (fun i => by
        have hc : ((-1 : ℤ) : WithTop ℤ) = (-1 : WithTop ℤ) := by norm_cast
        simpa only [hc] using (hW (b i)).2.1 p)
    refine ⟨g, hg, ?_⟩
    filter_upwards [he] with z hz
    intro a
    simpa only [ite_eq_left hp, heq] using hz a
  · refine ⟨fun az => ∑ i, az.1 i * f i az.2, ?_, ?_⟩
    · intro a
      apply Finset.analyticAt_fun_sum
      intro i hi
      have ha : AnalyticAt ℂ (fun az : (Fin m → ℂ) × ℂ => az.1 i) (a, 0) :=
        ((ContinuousLinearMap.proj i : (Fin m → ℂ) →L[ℂ] ℂ).comp
          (ContinuousLinearMap.fst ℂ (Fin m → ℂ) ℂ)).analyticAt _
      have hf : AnalyticAt ℂ (f i) 0 := (hW (b i)).2.2 p hp
      have hc : AnalyticAt ℂ (fun az : (Fin m → ℂ) × ℂ => f i az.2) (a, 0) :=
        AnalyticAt.comp (g := f i) (f := fun az : (Fin m → ℂ) × ℂ => az.2) hf
          (analyticAt_snd (𝕜 := ℂ) (p := (a, 0)))
      exact ha.mul hc
    · exact Filter.Eventually.of_forall (fun z a => by
        simp only [ite_eq_right hp, one_mul, heq])

#print axioms residual_system_pole_correction

/-- Corrected analytic coefficients retain the exact adjusted divisor multiplicity. -/
theorem residual_normalized_pole_corrected_order
    [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (hE : Module.finrank ℂ E = 1) {n : ℕ} (y : Fin n → C)
    (hy : Function.Injective y) (w : b4c_MeroForm E C hE)
    (hw : (w : TangentBundle 𝓘(ℂ, E) C → ℂ) ≠ 0)
    (ha : ∀ p ∉ Set.range y, AnalyticAt ℂ (HurwitzPrymRR_loc hE w p) 0)
    (hz : ∀ p ∈ Set.range y, ∀ u, w ⟨p, u⟩ = 0)
    (p : C) (g : ℂ → ℂ) (hg : AnalyticAt ℂ g 0)
    (he : (fun z => (if p ∈ Set.range y then z else 1) * HurwitzPrymRR_loc hE w p z)
      =ᶠ[𝓝[≠] 0] g) :
    ∃ d : ℕ, analyticOrderAt g 0 = d ∧
      (d : ℤ) = (b4c_divForm (hE := hE) w + s2e_markedPoleDivisor y) p := by
  classical
  have hd := RiemannRochEichler_divForm_order hE w
    (residual_normalized_form_has_finite_order hE (Set.range y) w hw ha hz) p
  have hord : meromorphicOrderAt g 0 =
      (((b4c_divForm (hE := hE) w + s2e_markedPoleDivisor y) p : ℤ) : WithTop ℤ) := by
    rw [← meromorphicOrderAt_congr he]
    by_cases hp : p ∈ Set.range y
    · obtain ⟨j, hj⟩ := hp
      have hmark : s2e_markedPoleDivisor y p = 1 := by
        rw [← hj, s2e_markedPoleDivisor_apply_of_injective y hy]
      simp only [ite_eq_left (show p ∈ Set.range y from ⟨j, hj⟩)]
      change meromorphicOrderAt ((id : ℂ → ℂ) * HurwitzPrymRR_loc hE w p) 0 = _
      rw [meromorphicOrderAt_mul analyticAt_id.meromorphicAt (w.property.2 p),
        meromorphicOrderAt_id, ← hd]
      simp only [Finsupp.add_apply, hmark, WithTop.coe_add, WithTop.coe_one]
      exact add_comm _ _
    · simp only [ite_eq_right hp, one_mul]
      rw [← hd]
      simp only [Finsupp.add_apply, s2e_markedPoleDivisor_apply_outside y p hp, add_zero]
  have hn : analyticOrderAt g 0 ≠ ⊤ := by
    intro ht
    have hh := hg.meromorphicOrderAt_eq
    rw [ht, ENat.map_top, hord] at hh
    exact WithTop.coe_ne_top hh
  obtain ⟨d, hd'⟩ := ENat.ne_top_iff_exists.mp hn
  refine ⟨d, hd'.symm, ?_⟩
  rw [hg.meromorphicOrderAt_eq, ← hd', ENat.map_natCast] at hord
  exact_mod_cast hord

#print axioms residual_normalized_pole_corrected_order

/-- Full-system linear charts have preparation with their exact divisor multiplicities. -/
theorem residual_system_local_preparation
    [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (hE : Module.finrank ℂ E = 1) {n m : ℕ} (y : Fin n → C)
    (hy : Function.Injective y)
    (W : Submodule ℂ (TangentBundle 𝓘(ℂ, E) C → ℂ))
    (hW : ∀ q : W, b4c_IsMeroForm hE q.val ∧
      (∀ p, ((-1 : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt (HurwitzPrymRR_loc hE q.val p) 0) ∧
      (∀ p ∉ Set.range y, AnalyticAt ℂ (HurwitzPrymRR_loc hE q.val p) 0) ∧
      ∀ p ∈ Set.range y, ∀ u, q.val ⟨p, u⟩ = 0)
    (b : Fin m → W) (p : C) :
    ∃ g : (Fin m → ℂ) × ℂ → ℂ,
      (∀ a, AnalyticAt ℂ g (a, 0)) ∧
      (∀ᶠ z in 𝓝[≠] (0 : ℂ), ∀ a, (if p ∈ Set.range y then z else 1) *
        HurwitzPrymRR_loc hE (∑ i, a i • b i : W).val p z = g (a, z)) ∧
      ∀ a, (∑ i, a i • b i : W) ≠ 0 →
        ∃ d : ℕ, (d : ℤ) =
            (b4c_divForm (hE := hE) (∑ i, a i • b i : W).val + s2e_markedPoleDivisor y) p ∧
          analyticOrderAt (fun z => g (a, z)) 0 = d ∧
          ∃ u : (Fin m → ℂ) × ℂ → ℂ, AnalyticAt ℂ u 0 ∧ u 0 ≠ 0 ∧
            ∃ c : Fin d → (Fin m → ℂ) → ℂ,
              (∀ j, AnalyticAt ℂ (c j) 0 ∧ c j 0 = 0) ∧
              (fun tz => g (a + tz.1, tz.2)) =ᶠ[𝓝 0]
                fun tz => u tz * HodgeLean.Foundations.AnalyticDivisorAlgebraic4.monicInLast c tz := by
  obtain ⟨g, hg, he⟩ := residual_system_pole_correction hE (Set.range y) W
    (fun q => ⟨(hW q).1, (hW q).2.1, (hW q).2.2.1⟩) b p
  refine ⟨g, hg, ?_, ?_⟩
  · filter_upwards [he] with z hz
    intro a
    by_cases hp : p ∈ Set.range y
    · simpa only [ite_eq_left hp] using hz a
    · simpa only [ite_eq_right hp] using hz a
  intro a ha
  let v : W := ∑ i, a i • b i
  have hv : v.val ≠ 0 := fun h => ha (Subtype.ext h)
  have hg' : AnalyticAt ℂ (fun z => g (a, z)) 0 :=
    (hg a).comp (f := fun z : ℂ => (a, z)) (analyticAt_const.prod analyticAt_id)
  obtain ⟨d, hd, hD⟩ := residual_normalized_pole_corrected_order hE y hy
    ⟨v.val, (hW v).1⟩ hv (hW v).2.2.1 (hW v).2.2.2 p
    (fun z => g (a, z)) hg' (by
      filter_upwards [he] with z hz
      by_cases hp : p ∈ Set.range y
      · simpa only [ite_eq_left hp, v] using hz a
      · simpa only [ite_eq_right hp, v] using hz a)
  refine ⟨d, hD, hd, ?_⟩
  have hf : AnalyticAt ℂ (fun tz : (Fin m → ℂ) × ℂ => g (a + tz.1, tz.2)) 0 :=
    (hg a).comp_of_eq ((analyticAt_const.add analyticAt_fst).prod analyticAt_snd)
      (by simp only [Prod.fst_zero, Prod.snd_zero, add_zero])
  apply HodgeLean.Foundations.AnalyticDivisorAlgebraic4.spec_weierstrass_preparation hf
  simpa only [Prod.fst_zero, add_zero] using hd

#print axioms residual_system_local_preparation

end HodgeLean.Foundations.Program.G32Native
