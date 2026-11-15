import HodgeLean.Foundations.Program.SchoenCycleCorrectedResidues
import HodgeLean.Foundations.Program.SchoenCyclePairedLocalPolynomial
import HodgeLean.Foundations.AnalyticDivisorAlgebraic5

/-! # Prepared constant terms and signed residue coordinates -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open Filter Topology Manifold
open HodgeLean.Foundations.AnalyticDivisorAlgebraic4
open HodgeLean.Foundations.AnalyticDivisorAlgebraic5
open scoped BigOperators ContDiff
namespace HodgeLean.Foundations.Program

/-- Restriction of a prepared equation to its central section gives the constant
coefficient as an analytic unit times the original central value.
Source: Gunning–Rossi, Analytic Functions of Several Complex Variables, Chapter II, §B,
Theorem 2, evaluated on the central section. -/
theorem s2e_prepared_constant_term_unit
    {m d : ℕ} (f u : (Fin m → ℂ) × ℂ → ℂ)
    (c : Fin d → (Fin m → ℂ) → ℂ) (ρ : (Fin m → ℂ) → ℂ)
    (hu : AnalyticAt ℂ u 0) (hu0 : u 0 ≠ 0)
    (hprep : f =ᶠ[𝓝 0] fun tz => u tz * monicInLast c tz)
    (hvalue : ∀ t, f (t, 0) = ρ t) :
    ∃ η : (Fin m → ℂ) → ℂ, AnalyticAt ℂ η 0 ∧ η 0 ≠ 0 ∧
      ∀ᶠ t in 𝓝 0, (monicPoly c t).coeff 0 = η t * ρ t := by
  let η : (Fin m → ℂ) → ℂ := fun t => (u (t, 0))⁻¹
  have hu' : AnalyticAt ℂ (fun t : Fin m → ℂ => u (t, 0)) 0 :=
    hu.comp (f := fun t : Fin m → ℂ => (t, (0 : ℂ)))
      (analyticAt_id.prod analyticAt_const)
  refine ⟨η, hu'.inv hu0, inv_ne_zero hu0, ?_⟩
  have ht : Tendsto (fun t : Fin m → ℂ => (t, (0 : ℂ))) (𝓝 0) (𝓝 0) :=
    (continuous_id.prodMk continuous_const).tendsto 0
  have he := hprep.comp_tendsto ht
  filter_upwards [he, hu'.continuousAt.eventually_ne hu0] with t ht hne
  have hv : ρ t = u (t, 0) * monicInLast c (t, 0) := (hvalue t).symm.trans ht
  have hp : (monicPoly c t).coeff 0 = monicInLast c (t, 0) := by
    rw [Polynomial.coeff_zero_eq_eval_zero, (spec_monicPoly c t).2.2]
  rw [hp, hv]
  change monicInLast c (t, 0) = (u (t, 0))⁻¹ * (u (t, 0) * monicInLast c (t, 0))
  rw [← mul_assoc, inv_mul_cancel₀ hne, one_mul]

variable {E C : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace C] [ChartedSpace E C] [IsManifold 𝓘(ℂ, E) ω C]

/-- At either member of a paired branch, the actual prepared polynomial has
constant coefficient equal to an analytic unit times its signed residue coordinate.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.4, printed p. 15;
Gunning–Rossi, Analytic Functions of Several Complex Variables, Chapter II, §B, Theorem 2. -/
theorem s2e_paired_prepared_signed_constant_term
    [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (hE : Module.finrank ℂ E = 1) {r m : ℕ}
    (w : Fin r → b4c_MeroForm E C hE) (y : Fin (2 * r) → C)
    (hy : Function.Injective y)
    (hres : ∀ i j, b4c_res (hE := hE) (w i)
      (y ⟨2 * j.val + 1, by omega⟩) = if i = j then 1 else 0)
    (hpair : ∀ i j, b4c_res (hE := hE) (w i)
      (y ⟨2 * j.val, by omega⟩) = if i = j then -1 else 0)
    (horder : ∀ i p, (-1 : WithTop ℤ) ≤ meromorphicOrderAt
      (HurwitzPrymRR_loc hE (w i) p) 0)
    (hout : ∀ i p, p ∉ Set.range y → AnalyticAt ℂ
      (HurwitzPrymRR_loc hE (w i) p) 0)
    (b : Fin m → b3_HolForm E C × (Fin r → ℂ))
    (a : Fin m → ℂ) (ha : (∑ i, a i • b i) ≠ 0) (j : Fin r) (s : Bool) :
    let p := if s then y ⟨2 * j.val + 1, by omega⟩ else y ⟨2 * j.val, by omega⟩
    let sign : ℂ := if s then 1 else -1
    ∃ (g : (Fin m → ℂ) × ℂ → ℂ) (d : ℕ)
      (u : (Fin m → ℂ) × ℂ → ℂ) (c : Fin d → (Fin m → ℂ) → ℂ)
      (η : (Fin m → ℂ) → ℂ),
      (∀ a', AnalyticAt ℂ g (a', 0)) ∧
      (∀ᶠ z in 𝓝[≠] (0 : ℂ), ∀ a', z * HurwitzPrymRR_loc hE
        (s2e_pairedDifferentialLinear hE w (∑ i, a' i • b i)) p z = g (a', z)) ∧
      (d : ℤ) = s2e_adjustedDifferentialDivisor hE w y (∑ i, a i • b i) p ∧
      AnalyticAt ℂ u 0 ∧ u 0 ≠ 0 ∧
      (∀ i, AnalyticAt ℂ (c i) 0 ∧ c i 0 = 0) ∧
      ((fun tz => g (a + tz.1, tz.2)) =ᶠ[𝓝 0]
        fun tz => u tz * monicInLast c tz) ∧
      AnalyticAt ℂ η 0 ∧ η 0 ≠ 0 ∧
      ∀ᶠ t in 𝓝 0, (monicPoly c t).coeff 0 =
        η t * ((∑ i, (a + t) i • b i).2 j * sign) := by
  classical
  dsimp only
  let xs : Fin r → C := fun l =>
    if s then y ⟨2 * l.val + 1, by omega⟩ else y ⟨2 * l.val, by omega⟩
  let sign : ℂ := if s then 1 else -1
  have hs : ∀ i l, b4c_res (hE := hE) (w i) (xs l) =
      if i = l then sign else 0 := by
    cases s
    · exact hpair
    · exact hres
  have hx (l : Fin r) : xs l ∈ Set.range y := by
    cases s
    · exact ⟨⟨2 * l.val, by omega⟩, rfl⟩
    · exact ⟨⟨2 * l.val + 1, by omega⟩, rfl⟩
  obtain ⟨g, hg, he, hp⟩ := s2e_paired_family_local_preparation hE w
    (fun l => y ⟨2 * l.val + 1, by omega⟩) hres y hy horder hout b (xs j)
  obtain ⟨d, hd, _, u, hu, hu0, c, hc, hprep⟩ := hp a ha
  have he' : ∀ᶠ z in 𝓝[≠] (0 : ℂ), ∀ a', z * HurwitzPrymRR_loc hE
      (s2e_pairedDifferentialLinear hE w (∑ i, a' i • b i)) (xs j) z = g (a', z) := by
    simpa only [ite_eq_left (hx j)] using he
  have hv (t : Fin m → ℂ) : g (a + t, 0) = (∑ i, (a + t) i • b i).2 j * sign := by
    apply s2e_corrected_paired_coefficient_value hE w xs sign hs _ j
      (fun z => g (a + t, z))
    · exact (hg (a + t)).comp (f := fun z : ℂ => (a + t, z))
        (analyticAt_const.prod analyticAt_id)
    · filter_upwards [he'] with z hz
      exact hz (a + t)
  obtain ⟨η, hη, hη0, hηeq⟩ := s2e_prepared_constant_term_unit
    (fun tz => g (a + tz.1, tz.2)) u c
    (fun t => (∑ i, (a + t) i • b i).2 j * sign) hu hu0 hprep hv
  exact ⟨g, d, u, c, η, hg, he', hd, hu, hu0, hc, hprep, hη, hη0, hηeq⟩

end HodgeLean.Foundations.Program
