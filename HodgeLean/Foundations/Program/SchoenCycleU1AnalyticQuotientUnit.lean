import HodgeLean.Foundations.AnalyticDivisorAlgebraic4

/-! # Analytic divisor quotients with equal base multiplicities -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open Filter Topology Metric
namespace HodgeLean.Foundations.Program

/-- An analytic quotient is a unit when numerator and denominator have the
same finite order at the base point.
Source: Gunning--Rossi, Analytic Functions of Several Complex Variables,
Chapter II, section B, Weierstrass preparation; Mathlib, `analyticOrderAt_mul`. -/
theorem s2e_u1_analytic_quotient_unit_of_equal_order
    (F P u : ℂ → ℂ) (hP : AnalyticAt ℂ P 0) (hu : AnalyticAt ℂ u 0)
    (he : F =ᶠ[𝓝 0] (fun z => u z * P z)) (d : ℕ)
    (hF : analyticOrderAt F 0 = d) (hPd : analyticOrderAt P 0 = d) : u 0 ≠ 0 := by
  have ho : analyticOrderAt F 0 = analyticOrderAt u 0 + analyticOrderAt P 0 :=
    (analyticOrderAt_congr he).trans (analyticOrderAt_mul hu hP)
  rw [hF, hPd] at ho
  have hz : analyticOrderAt u 0 = 0 := by
    apply ENat.add_left_injective_of_ne_top (n := (d : ℕ∞)) (by simp)
    simpa only [zero_add] using ho.symm
  exact hu.analyticOrderAt_eq_zero.mp hz

/-- Fibrewise divisor domination and equality of the finite base orders give
an actual analytic unit quotient near the parameter origin.
Source: Gunning--Rossi, Analytic Functions of Several Complex Variables,
Chapter II, section B, Weierstrass preparation and analytic division. -/
theorem s2e_u1_analytic_unit_quotient_of_orders
    {n : ℕ} (F P : (Fin n → ℂ) × ℂ → ℂ) (δ r : ℝ) (hδ : 0 < δ) (hr : 0 < r)
    (hF : AnalyticOnNhd ℂ F (closedBall 0 δ ×ˢ closedBall 0 r))
    (hP : AnalyticOnNhd ℂ P (closedBall 0 δ ×ˢ closedBall 0 r))
    (hne : ∀ t ∈ closedBall 0 δ, ∀ z ∈ sphere 0 r, P (t, z) ≠ 0)
    (hord : ∀ t ∈ ball 0 δ, ∀ z ∈ ball 0 r,
      analyticOrderAt (fun z => P (t, z)) z ≤ analyticOrderAt (fun z => F (t, z)) z)
    (d : ℕ) (hFd : analyticOrderAt (fun z => F (0, z)) 0 = d)
    (hPd : analyticOrderAt (fun z => P (0, z)) 0 = d) :
    ∃ u : (Fin n → ℂ) × ℂ → ℂ, AnalyticAt ℂ u (0, 0) ∧ u (0, 0) ≠ 0 ∧
      F =ᶠ[𝓝 (0, 0)] (fun tz => u tz * P tz) := by
  obtain ⟨u, hu, he⟩ :=
    HodgeLean.Foundations.AnalyticDivisorAlgebraic4.spec_exists_analytic_quotient hF hP hne hord
  have hcenter : ((0 : Fin n → ℂ), (0 : ℂ)) ∈ ball 0 δ ×ˢ ball 0 r :=
    ⟨mem_ball_self hδ, mem_ball_self hr⟩
  have hcenter' : ((0 : Fin n → ℂ), (0 : ℂ)) ∈ closedBall 0 δ ×ˢ closedBall 0 r :=
    ⟨mem_closedBall_self hδ.le, mem_closedBall_self hr.le⟩
  have hlocal : F =ᶠ[𝓝 ((0 : Fin n → ℂ), (0 : ℂ))] (fun tz => u tz * P tz) :=
    Filter.eventually_of_mem ((isOpen_ball.prod isOpen_ball).mem_nhds hcenter) he
  have hslice : AnalyticAt ℂ (fun z : ℂ => ((0 : Fin n → ℂ), z)) 0 :=
    analyticAt_const.prod analyticAt_id
  have hu0 := hu (0, 0) hcenter
  refine ⟨u, hu0, ?_, hlocal⟩
  exact s2e_u1_analytic_quotient_unit_of_equal_order
    (fun z => F (0, z)) (fun z => P (0, z)) (fun z => u (0, z))
    ((hP (0, 0) hcenter').comp_of_eq hslice rfl)
    (hu0.comp_of_eq hslice rfl)
    (hlocal.comp_tendsto hslice.continuousAt.tendsto) d hFd hPd

/-- Eventual fibrewise order domination near the origin suffices for an
analytic unit quotient when the two base orders agree and are finite.
Source: Gunning--Rossi, Analytic Functions of Several Complex Variables,
Chapter II, section B, analytic division on a sufficiently small polydisc. -/
theorem s2e_u1_analytic_unit_quotient_germ_of_orders
    {n : ℕ} (F P : (Fin n → ℂ) × ℂ → ℂ)
    (hF : AnalyticAt ℂ F (0, 0)) (hP : AnalyticAt ℂ P (0, 0))
    (hord : ∀ᶠ tz in 𝓝 ((0 : Fin n → ℂ), (0 : ℂ)),
      analyticOrderAt (fun z => P (tz.1, z)) tz.2 ≤
        analyticOrderAt (fun z => F (tz.1, z)) tz.2)
    (d : ℕ) (hFd : analyticOrderAt (fun z => F (0, z)) 0 = d)
    (hPd : analyticOrderAt (fun z => P (0, z)) 0 = d) :
    ∃ u : (Fin n → ℂ) × ℂ → ℂ, AnalyticAt ℂ u (0, 0) ∧ u (0, 0) ≠ 0 ∧
      F =ᶠ[𝓝 (0, 0)] (fun tz => u tz * P tz) := by
  have hgood := hF.eventually_analyticAt.and hord
  rw [nhds_prod_eq] at hgood
  obtain ⟨A, hA, B, hB, hAB⟩ := Filter.mem_prod_iff.mp hgood
  obtain ⟨ε, hε, hεA⟩ := Metric.nhds_basis_closedBall.mem_iff.mp hA
  obtain ⟨η, hη, hηB⟩ := Metric.nhds_basis_closedBall.mem_iff.mp hB
  have hrect (t : Fin n → ℂ) (ht : t ∈ closedBall 0 ε)
      (z : ℂ) (hz : z ∈ closedBall 0 η) :
      AnalyticAt ℂ F (t, z) ∧
        analyticOrderAt (fun z => P (t, z)) z ≤ analyticOrderAt (fun z => F (t, z)) z :=
    hAB ⟨hεA ht, hηB hz⟩
  obtain ⟨r, hr, hrη, δ, hδ, hPa, hne, _⟩ :=
    HodgeLean.Foundations.AnalyticDivisorAlgebraic4.spec_exists_weierstrass_radii hP hPd hη
  have hF' : AnalyticOnNhd ℂ F (closedBall 0 (min ε δ) ×ˢ closedBall 0 r) := by
    rintro ⟨t, z⟩ ⟨ht, hz⟩
    exact (hrect t (mem_closedBall.mpr ((mem_closedBall.mp ht).trans (min_le_left _ _)))
      z (mem_closedBall.mpr ((mem_closedBall.mp hz).trans hrη.le))).1
  have hP' : AnalyticOnNhd ℂ P (closedBall 0 (min ε δ) ×ˢ closedBall 0 r) := by
    rintro ⟨t, z⟩ ⟨ht, hz⟩
    exact hPa (t, z) ⟨mem_closedBall.mpr
      ((mem_closedBall.mp ht).trans (min_le_right _ _)), hz⟩
  apply s2e_u1_analytic_unit_quotient_of_orders F P (min ε δ) r (lt_min hε hδ) hr hF' hP'
    (fun t ht z hz => hne t (mem_closedBall.mpr
      ((mem_closedBall.mp ht).trans (min_le_right _ _))) z hz) ?_ d hFd hPd
  intro t ht z hz
  exact (hrect t (mem_closedBall.mpr ((mem_ball.mp ht).le.trans (min_le_left _ _)))
    z (mem_closedBall.mpr ((mem_ball.mp hz).le.trans hrη.le))).2

end HodgeLean.Foundations.Program
