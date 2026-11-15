import HodgeLean.Foundations.Analytic.ComplexAnalyticSpaceFibreParam

/-! # Local parametrization of a prime component

Helpers prefixed `ancrs_`. For a set `C ⊆ ℂᴺ` whose germ at `y` is the zero germ of a prime `Q`
of dimension `e` with vanishing ideal `Q`, the local parametrization (finite parameters,
primitive linear form, minimal polynomial and common denominator) is bundled in `ancrs_Param`:
a linear projection `π` to `ℂᵉ`, a linear form `ℓ`, functions `q(w, t)`, `r(w, t)` polynomial in
`t` and `Δ(w)`, analytic near the origin, such that near `y` the points `y + v` of `C` satisfy
`q(π v, ℓ v) = 0` and `Δ(π v) v = r(π v, ℓ v)`, the roots of `q(w, ·)` off `Δ = 0` are simple and
give back points of `C`, and `Δ ∘ π` does not vanish on `C` near `y`.
HC no distance; AV milestone no distance.
-/

noncomputable section

open Set Filter Topology Polynomial
open scoped ContDiff

namespace HodgeLean.Foundations.Analytic

open HodgeLean.Foundations HodgeLean.Foundations.AnalyticDivisorAlgebraic6

/-- The local parametrization of `C` near `y`, in coordinates `v = z - y`.
Source: Gunning–Rossi, *Analytic Functions of Several Complex Variables*, Ch. III, §§B–C (local
parametrization of prime germs); built by `ancrs_param_exists`. -/
structure ancrs_Param (N e : ℕ) (C : Set (Fin N → ℂ)) (y : Fin N → ℂ) where
  /-- the parameter projection -/
  π : (Fin N → ℂ) →L[ℂ] (Fin e → ℂ)
  /-- the primitive linear form -/
  ℓ : (Fin N → ℂ) →L[ℂ] ℂ
  /-- the minimal polynomial of `ℓ`, as a function of `(w, t)` -/
  qf : (Fin e → ℂ) × ℂ → ℂ
  /-- the numerators of the coordinates -/
  Rf : (Fin e → ℂ) × ℂ → (Fin N → ℂ)
  /-- the common denominator -/
  Δ : (Fin e → ℂ) → ℂ
  /-- the radius in `ℂᴺ` on which the data are valid -/
  ρ : ℝ
  ρ_pos : 0 < ρ
  /-- the radius in the parameter space on which the data are valid -/
  ρw : ℝ
  π_small : ∀ v : Fin N → ℂ, ‖v‖ < ρ → ‖π v‖ < ρw
  qf_an : ∀ w : Fin e → ℂ, ‖w‖ < ρw → ∀ t, AnalyticAt ℂ qf (w, t)
  Rf_an : ∀ w : Fin e → ℂ, ‖w‖ < ρw → ∀ t, AnalyticAt ℂ Rf (w, t)
  Δ_an : ∀ w : Fin e → ℂ, ‖w‖ < ρw → AnalyticAt ℂ Δ w
  eq_root : ∀ v : Fin N → ℂ, ‖v‖ < ρ → y + v ∈ C → qf (π v, ℓ v) = 0
  eq_coord : ∀ v : Fin N → ℂ, ‖v‖ < ρ → y + v ∈ C → ∀ i, Δ (π v) * v i = Rf (π v, ℓ v) i
  simple : ∀ w : Fin e → ℂ, ‖w‖ < ρw → ∀ t, qf (w, t) = 0 → Δ w ≠ 0 →
    fderiv ℂ qf (w, t) (0, 1) ≠ 0
  roots : ∀ w : Fin e → ℂ, ‖w‖ < ρw → ∀ t, Δ w ≠ 0 → qf (w, t) = 0 →
    y + (fun i ↦ Rf (w, t) i / Δ w) ∈ C ∧ π (fun i ↦ Rf (w, t) i / Δ w) = w ∧
      ℓ (fun i ↦ Rf (w, t) i / Δ w) = t
  nonvanish : ¬ ∀ᶠ v in 𝓝 (0 : Fin N → ℂ), y + v ∈ C → Δ (π v) = 0

section Exists

/-- The derivative in `t` of a representative polynomial is its formal derivative. -/
theorem ancrs_fderiv_evPoly_t {d : ℕ} (T : Polynomial (AnalyticGerm d)) {w : Fin d → ℂ}
    (hw : w ∈ ancrs_polyDom T) (t : ℂ) :
    fderiv ℂ (fun u : (Fin d → ℂ) × ℂ ↦ (ancrs_evPoly T u.1).eval u.2) (w, t) (0, 1) =
      (ancrs_evPoly T w).derivative.eval t := by
  set F : (Fin d → ℂ) × ℂ → ℂ := fun u ↦ (ancrs_evPoly T u.1).eval u.2
  have hFa := ancrs_evPoly_analyticAt T hw t
  have h1 : HasFDerivAt (fun s ↦ F (w, s))
      (fderiv ℂ F (w, t) ∘L ContinuousLinearMap.inr ℂ (Fin d → ℂ) ℂ) t :=
    hFa.differentiableAt.hasFDerivAt.comp t (hasFDerivAt_prodMk_right w t)
  have h2 : HasFDerivAt (fun s ↦ F (w, s))
      ((1 : ℂ →L[ℂ] ℂ).smulRight ((ancrs_evPoly T w).derivative.eval t)) t :=
    (Polynomial.hasDerivAt (ancrs_evPoly T w) t).hasFDerivAt
  have := congrArg (fun A : ℂ →L[ℂ] ℂ ↦ A 1) (h1.unique h2)
  simpa using this

/-- The coefficients of a representative polynomial represent the coefficients. -/
theorem ancrs_repPoly_coeff_germ {d : ℕ} (T : Polynomial (AnalyticGerm d)) (i : ℕ) :
    Filter.Germ.ofFun ((ancrs_repPoly T).coeff i) = (T.coeff i).val := by
  have := congrArg (fun F ↦ F.coeff i) (ancrs_repPoly_map T)
  simpa [Polynomial.coeff_map] using this

/-- **Existence of the local parametrization** of a prime component. -/
theorem ancrs_param_exists {N : ℕ} {C : Set (Fin N → ℂ)} {y : Fin N → ℂ}
    {Q : Ideal (AnalyticGerm N)} (hQ : Q.IsPrime) (hI : adim2_ideal N (adim2_germ N C y) = Q)
    (hZ : adim2_germ N C y = adim2_zeroSet N Q) {e : ℕ}
    (he : ringKrullDim (AnalyticGerm N ⧸ Q) = (e : WithBot ℕ∞)) :
    Nonempty (ancrs_Param N e C y) := by
  classical
  obtain ⟨d', π, θ, -, hfinite, hinj, hcomp, hdim⟩ := adim5_finite_parameters N Q hQ
  have hd' : d' = e := by
    have h := (adim6_parameter_dimension d').symm.trans (hdim.trans he)
    exact_mod_cast h
  subst hd'
  let c : Fin N → AnalyticGerm N := fun i ↦ ⟨Filter.Germ.ofFun (fun z : Fin N → ℂ ↦ z i), _,
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin N ↦ ℂ) i).analyticAt 0, rfl⟩
  obtain ⟨ℓ, v, Qp, δ, R, B, C', hv, -, -, hδ, hbez, hmin, hcoord⟩ :=
    adim7_primitive_form N d' Q hQ π θ hfinite hinj hcomp c (fun _ ↦ rfl)
  -- membership in `Q` gives vanishing on `C` near `y`
  have hvan : ∀ (H : AnalyticGerm N) (φ : (Fin N → ℂ) → ℂ), Filter.Germ.ofFun φ = H.val →
      H ∈ Q → ∀ᶠ z in 𝓝 (0 : Fin N → ℂ), y + z ∈ C → φ z = 0 := by
    intro H φ hφ hH
    rw [← hI] at hH
    exact (anrem_mem_ideal_iff C y H φ hφ).1 hH
  -- (E1)
  have hE1 : ∀ᶠ z in 𝓝 (0 : Fin N → ℂ), y + z ∈ C →
      (ancrs_evPoly Qp (π z)).eval (ℓ z) = 0 := by
    obtain ⟨H, hHmk, hHval⟩ := ancrs_eval₂_rep (P := Q) π θ hcomp Qp v hv
    have hHP : H ∈ Q := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, hHmk]; exact (hmin Qp).2 dvd_rfl
    exact hvan H _ hHval.symm hHP
  -- (E2)
  let dδ : AnalyticGerm N := ⟨Filter.Germ.ofFun (fun z ↦ ancrs_rep δ (π z)), _,
    (ancrs_rep_analyticAt δ).comp_of_eq (π.analyticAt 0) (map_zero π), rfl⟩
  have hθδ : θ δ = Ideal.Quotient.mk Q dδ :=
    hcomp δ (ancrs_rep δ) (ancrs_rep_analyticAt δ) (ancrs_rep_germ δ) dδ rfl
  have hE2 : ∀ᶠ z in 𝓝 (0 : Fin N → ℂ), y + z ∈ C →
      ∀ i, ancrs_rep δ (π z) * z i = (ancrs_evPoly (R i) (π z)).eval (ℓ z) := by
    have hi : ∀ i, ∀ᶠ z in 𝓝 (0 : Fin N → ℂ), y + z ∈ C →
        ancrs_rep δ (π z) * z i = (ancrs_evPoly (R i) (π z)).eval (ℓ z) := by
      intro i
      obtain ⟨H, hHmk, hHval⟩ := ancrs_eval₂_rep (P := Q) π θ hcomp (R i) v hv
      have hEP : dδ * c i - H ∈ Q := by
        rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, ← hθδ, hHmk, hcoord i, sub_self]
      have hval : Filter.Germ.ofFun (fun z ↦ ancrs_rep δ (π z) * z i -
          (ancrs_evPoly (R i) (π z)).eval (ℓ z)) = (dδ * c i - H).val := by
        change _ = dδ.val * (c i).val - H.val
        rw [hHval]
        rfl
      filter_upwards [hvan _ _ hval hEP] with z hz h0
      exact sub_eq_zero.1 (hz h0)
    filter_upwards [Filter.eventually_all.2 hi] with z hz h0 i using hz i h0
  -- (E3)
  have hE3 : ∀ᶠ w in 𝓝 (0 : Fin d' → ℂ), ∀ t, (ancrs_evPoly Qp w).eval t = 0 →
      ancrs_rep δ w ≠ 0 → (ancrs_evPoly Qp w).derivative.eval t ≠ 0 := by
    filter_upwards [ancrs_bezout_rep Qp B C' δ hbez] with w hw t hq hΔ hq'
    apply hΔ
    rw [← hw t, hq, hq']
    ring
  -- (E4)
  obtain ⟨m, g, f, U, hgen, hrep, hU, hU0, hf, hzero⟩ := ancrs_generators Q
  have hCf : ∀ᶠ z in 𝓝 (0 : Fin N → ℂ), (y + z ∈ C ↔ ∀ j, f j z = 0) := by
    have h1 : adim2_germ N C y = Filter.Germ.ofFun (fun z ↦ ∀ j, f j z = 0) := hZ.trans hzero
    have h2 := Filter.Germ.coe_eq.1 h1
    filter_upwards [h2] with z hz
    exact iff_of_eq hz
  obtain ⟨ε, hε, hεC⟩ := Metric.eventually_nhds_iff.1 hCf
  have hq : ∀ i, Filter.Germ.ofFun ((ancrs_repPoly Qp).coeff i) = (Qp.coeff i).val :=
    ancrs_repPoly_coeff_germ Qp
  have hr : ∀ j i, Filter.Germ.ofFun ((ancrs_repPoly (R j)).coeff i) = ((R j).coeff i).val :=
    fun j ↦ ancrs_repPoly_coeff_germ (R j)
  obtain ⟨V4, hV4, hV40, hroots⟩ := adim9b_all_roots_off_discriminant N d' Q hQ.ne_top π θ
    hfinite hcomp c (fun _ ↦ rfl) ℓ v hv Qp δ R hmin hcoord (ancrs_repPoly Qp) (ancrs_rep δ)
    (fun i ↦ ancrs_repPoly (R i)) hq (ancrs_rep_germ δ) hr m g hgen f U hU hU0 hf hrep
  have hsmall := adim9b_reconstructed_coordinates_small N d' Q hQ.ne_top π θ hfinite hcomp c
    (fun _ ↦ rfl) v Qp δ R hmin hcoord (ancrs_repPoly Qp) (ancrs_rep δ)
    (fun i ↦ ancrs_repPoly (R i)) hq (ancrs_rep_germ δ) hr ε hε
  have hE4 : ∀ᶠ w in 𝓝 (0 : Fin d' → ℂ), ∀ t, ancrs_rep δ w ≠ 0 →
      (ancrs_evPoly Qp w).eval t = 0 →
      y + (fun i ↦ (ancrs_evPoly (R i) w).eval t / ancrs_rep δ w) ∈ C ∧
      π (fun i ↦ (ancrs_evPoly (R i) w).eval t / ancrs_rep δ w) = w ∧
      ℓ (fun i ↦ (ancrs_evPoly (R i) w).eval t / ancrs_rep δ w) = t := by
    filter_upwards [hsmall, hV4.mem_nhds hV40] with w hw hwV t hΔ hq0
    have hq0' : (ancrs_repPoly Qp).eval₂ (Pi.evalRingHom (fun _ : Fin d' → ℂ ↦ ℂ) w) t = 0 := by
      rw [← hq0, ancrs_evPoly, Polynomial.eval_map]
    have hzi : ∀ i, (ancrs_evPoly (R i) w).eval t =
        (ancrs_repPoly (R i)).eval₂ (Pi.evalRingHom (fun _ : Fin d' → ℂ ↦ ℂ) w) t := by
      intro i; rw [ancrs_evPoly, Polynomial.eval_map]
    obtain ⟨-, hπ, hℓ, hfz⟩ := hroots w hwV t hΔ hq0'
    have hsm := hw t hΔ hq0'
    simp only [hzi]
    refine ⟨?_, hπ, hℓ⟩
    have hnorm : ‖(fun i ↦ (ancrs_repPoly (R i)).eval₂
        (Pi.evalRingHom (fun _ : Fin d' → ℂ ↦ ℂ) w) t / ancrs_rep δ w)‖ < ε :=
      (pi_norm_lt_iff hε).2 hsm
    exact (hεC (by simpa using hnorm)).2 hfz
  -- the analyticity domains
  have hΔev : ∀ᶠ w in 𝓝 (0 : Fin d' → ℂ), AnalyticAt ℂ (ancrs_rep δ) w :=
    (ancrs_rep_analyticAt δ).eventually_analyticAt
  have hdomQ : ∀ᶠ w in 𝓝 (0 : Fin d' → ℂ), w ∈ ancrs_polyDom Qp :=
    (ancrs_isOpen_polyDom Qp).mem_nhds (ancrs_zero_mem_polyDom Qp)
  have hdomR : ∀ᶠ w in 𝓝 (0 : Fin d' → ℂ), ∀ i, w ∈ ancrs_polyDom (R i) :=
    Filter.eventually_all.2 fun i ↦
      (ancrs_isOpen_polyDom (R i)).mem_nhds (ancrs_zero_mem_polyDom (R i))
  obtain ⟨ρ1, hρ1, hρ1w⟩ := Metric.eventually_nhds_iff.1
    (hE3.and (hE4.and (hΔev.and (hdomQ.and hdomR))))
  obtain ⟨ρ2, hρ2, hρ2z⟩ := Metric.eventually_nhds_iff.1 (hE1.and hE2)
  have hπc : Continuous π := π.continuous
  -- a common radius: points of `ℂᴺ` in the ball map into the parameter ball
  obtain ⟨ρ3, hρ3, hρ3π⟩ : ∃ ρ3 > 0, ∀ z : Fin N → ℂ, ‖z‖ < ρ3 → ‖π z‖ < ρ1 := by
    have := (hπc.tendsto 0).eventually (Metric.ball_mem_nhds (π 0) hρ1)
    obtain ⟨ρ3, hρ3, h⟩ := Metric.eventually_nhds_iff.1 this
    refine ⟨ρ3, hρ3, fun z hz ↦ ?_⟩
    have := h (show dist z 0 < ρ3 by simpa using hz)
    simpa [map_zero] using this
  set ρ := min ρ1 (min ρ2 ρ3)
  have hρ : 0 < ρ := lt_min hρ1 (lt_min hρ2 hρ3)
  have hρ1' : ρ ≤ ρ1 := min_le_left _ _
  have hρ2' : ρ ≤ ρ2 := (min_le_right _ _).trans (min_le_left _ _)
  have hρ3' : ρ ≤ ρ3 := (min_le_right _ _).trans (min_le_right _ _)
  have hw1 : ∀ w : Fin d' → ℂ, ‖w‖ < ρ1 → _ := fun w hw ↦
    hρ1w (show dist w 0 < ρ1 by simpa using hw)
  refine ⟨{
    π := π
    ℓ := ℓ
    qf := fun u ↦ (ancrs_evPoly Qp u.1).eval u.2
    Rf := fun u i ↦ (ancrs_evPoly (R i) u.1).eval u.2
    Δ := ancrs_rep δ
    ρ := ρ
    ρ_pos := hρ
    ρw := ρ1
    π_small := fun z hz ↦ hρ3π z (hz.trans_le hρ3')
    qf_an := fun w hw t ↦ ancrs_evPoly_analyticAt Qp (hw1 w hw).2.2.2.1 t
    Rf_an := fun w hw t ↦ analyticAt_pi_iff.2 fun i ↦
      ancrs_evPoly_analyticAt (R i) ((hw1 w hw).2.2.2.2 i) t
    Δ_an := fun w hw ↦ (hw1 w hw).2.2.1
    eq_root := fun z hz hzC ↦
      (hρ2z (show dist z 0 < ρ2 by simpa using hz.trans_le hρ2')).1 hzC
    eq_coord := fun z hz hzC ↦
      (hρ2z (show dist z 0 < ρ2 by simpa using hz.trans_le hρ2')).2 hzC
    simple := fun w hw t hq0 hΔ ↦ by
      have h := hw1 w hw
      rw [ancrs_fderiv_evPoly_t Qp h.2.2.2.1 t]
      exact h.1 t hq0 hΔ
    roots := fun w hw t hΔ hq0 ↦ (hw1 w hw).2.1 t hΔ hq0
    nonvanish := ?_ }⟩
  -- `Δ ∘ π` is not in `Q`
  intro hall
  apply hδ
  apply hinj
  rw [map_zero, hθδ, Ideal.Quotient.eq_zero_iff_mem, ← hI]
  exact (anrem_mem_ideal_iff C y dδ _ rfl).2 hall

end Exists

section Book

variable {N : ℕ}

/-- The zero set of a function analytic at `y` has local equations at `y`. -/
theorem ancrs_locEq_zero {h : (Fin N → ℂ) → ℂ} {y : Fin N → ℂ} (hh : AnalyticAt ℂ h y) :
    anrem_LocEq {z | h z = 0} y :=
  ⟨{z | AnalyticAt ℂ h z}, isOpen_analyticAt ℂ h, hh, 1, fun _ ↦ h, fun _ z hz ↦ hz,
    fun z _ ↦ by simp⟩

/-- An open set has local equations at its points. -/
theorem ancrs_locEq_open {O : Set (Fin N → ℂ)} (hO : IsOpen O) {y : Fin N → ℂ} (hy : y ∈ O) :
    anrem_LocEq O y :=
  ⟨O, hO, hy, 0, fun j ↦ j.elim0, fun j ↦ j.elim0, fun z hz ↦ by simp [hz]⟩

/-- Local equations at `y` give local equations at the points near `y`. -/
theorem ancrs_locEq_nhds {A : Set (Fin N → ℂ)} {y : Fin N → ℂ} (h : anrem_LocEq A y) :
    ∀ᶠ z in 𝓝 y, anrem_LocEq A z := by
  obtain ⟨U, hU, hyU, m, f, hf, hA⟩ := h
  filter_upwards [hU.mem_nhds hyU] with z hz using ⟨U, hU, hz, m, f, hf, hA⟩

/-- A set avoiding a neighbourhood of `y` has local equations at `y`. -/
theorem ancrs_locEq_of_eventually_not_mem {A : Set (Fin N → ℂ)} {y : Fin N → ℂ}
    (h : ∀ᶠ z in 𝓝 y, z ∉ A) : anrem_LocEq A y := by
  obtain ⟨U, hU, hUo, hyU⟩ := eventually_nhds_iff.1 h
  exact ⟨U, hUo, hyU, 1, fun _ _ ↦ 1, fun _ ↦ analyticOnNhd_const,
    fun z hz ↦ by simp [hU z hz]⟩

/-- A set with local equations at a point outside it avoids a neighbourhood of the point. -/
theorem ancrs_eventually_not_mem {A : Set (Fin N → ℂ)} {y : Fin N → ℂ} (h : anrem_LocEq A y)
    (hy : y ∉ A) : ∀ᶠ z in 𝓝 y, z ∉ A := by
  obtain ⟨U, hU, hyU, m, f, hf, hA⟩ := h
  have hne : ¬ ∀ j, f j y = 0 := fun h0 ↦ hy ((hA y hyU).2 h0)
  push Not at hne
  obtain ⟨j, hj⟩ := hne
  have hc : ContinuousAt (f j) y := (hf j y hyU).continuousAt
  filter_upwards [hU.mem_nhds hyU, hc.eventually_ne hj] with z hzU hz hzA
  exact hz ((hA z hzU).1 hzA j)

/-- Local equations transfer along sets agreeing near the point. -/
theorem ancrs_locEq_congr {A B : Set (Fin N → ℂ)} {y : Fin N → ℂ}
    (h : ∀ᶠ z in 𝓝 y, (z ∈ A ↔ z ∈ B)) (hA : anrem_LocEq A y) : anrem_LocEq B y := by
  obtain ⟨O, hO, hOo, hyO⟩ := eventually_nhds_iff.1 h
  refine anrem_locEq_congr hOo hyO ?_ hA
  ext z
  exact ⟨fun ⟨hz, hzO⟩ ↦ ⟨(hO z hzO).1 hz, hzO⟩, fun ⟨hz, hzO⟩ ↦ ⟨(hO z hzO).2 hz, hzO⟩⟩

/-- The dimension of the germ of a set at one of its points is a natural number at most `N`. -/
theorem ancrs_dimension_cases {A : Set (Fin N → ℂ)} {y : Fin N → ℂ} (hy : y ∈ A) :
    ∃ j : ℕ, j ≤ N ∧ adim2_dimension N (adim2_germ N A y) = j := by
  have hnt : Nontrivial (AnalyticGerm N ⧸ adim2_ideal N (adim2_germ N A y)) :=
    Ideal.Quotient.nontrivial_iff.mpr (adim9b_germ_ideal_ne_top N A y hy)
  have hle : ringKrullDim (AnalyticGerm N ⧸ adim2_ideal N (adim2_germ N A y)) ≤ (N : WithBot ℕ∞) :=
    (ringKrullDim_le_of_surjective _ Ideal.Quotient.mk_surjective).trans
      (adim6_parameter_dimension N).le
  exact anr_dim_cases N hle

/-- A set cut out on an open `U` by functions continuous there meets a closed ball inside `U` in a
closed set. -/
theorem ancrs_isClosed_inter_closedBall {C U : Set (Fin N → ℂ)} {m : ℕ}
    {f : Fin m → (Fin N → ℂ) → ℂ} (hf : ∀ j, ContinuousOn (f j) U)
    (hC : ∀ z ∈ U, (z ∈ C ↔ ∀ j, f j z = 0)) {a : Fin N → ℂ} {R : ℝ}
    (hRU : Metric.closedBall a R ⊆ U) : IsClosed (C ∩ Metric.closedBall a R) := by
  have hF : ContinuousOn (fun z j ↦ f j z) (Metric.closedBall a R) :=
    continuousOn_pi.2 fun j ↦ (hf j).mono hRU
  have h1 : C ∩ Metric.closedBall a R =
      Metric.closedBall a R ∩ (fun z j ↦ f j z) ⁻¹' {(0 : Fin m → ℂ)} := by
    ext z
    constructor
    · rintro ⟨hzC, hzB⟩
      exact ⟨hzB, funext fun j ↦ (hC z (hRU hzB)).1 hzC j⟩
    · rintro ⟨hzB, hz⟩
      exact ⟨(hC z (hRU hzB)).2 fun j ↦ congrFun hz j, hzB⟩
  rw [h1]
  exact hF.preimage_isClosed_of_isClosed Metric.isClosed_closedBall isClosed_singleton

end Book

section Linear

/-- **A nonzero maximal minor.** A matrix with injective `mulVec` has a square submatrix (a choice
of rows) with nonzero determinant. -/
theorem ancrs_exists_minor {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (A : Matrix ι κ ℂ) (h : Function.Injective A.mulVec) :
    ∃ s : κ → ι, (A.submatrix s id).det ≠ 0 := by
  classical
  have hrank : A.rank = Fintype.card κ := by
    rw [Matrix.rank]
    have : Function.Injective (A.mulVecLin) := h
    rw [LinearMap.finrank_range_of_inj this, Module.finrank_fintype_fun_eq_card]
  have hspan : Submodule.span ℂ (Set.range A.row) = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [← Matrix.rank_eq_finrank_span_row, hrank, Module.finrank_fintype_fun_eq_card]
  obtain ⟨t, ht, hsp, hli⟩ := exists_linearIndependent ℂ (Set.range A.row)
  have htop : Submodule.span ℂ t = ⊤ := hsp.trans hspan
  have : Fintype t := ((Set.finite_range _).subset ht).fintype
  let b : Module.Basis t ℂ (κ → ℂ) := Module.Basis.mk hli (by rw [Subtype.range_coe]; exact htop.ge)
  have hcard : Fintype.card t = Fintype.card κ := by
    have := Module.finrank_eq_card_basis b
    rw [Module.finrank_fintype_fun_eq_card] at this
    exact this.symm
  let eqv : κ ≃ t := Fintype.equivOfCardEq hcard.symm
  have hrow : ∀ k, ∃ i, A.row i = (eqv k : κ → ℂ) := fun k ↦ ht (eqv k).2
  choose s hs using hrow
  refine ⟨s, ?_⟩
  have hli' : LinearIndependent ℂ (A.submatrix s id).row := by
    have h1 : (A.submatrix s id).row = (fun x : t ↦ (x : κ → ℂ)) ∘ eqv := by
      funext k
      rw [Function.comp_apply, ← hs k]
      rfl
    rw [h1]
    exact hli.comp _ eqv.injective
  have hu : IsUnit (A.submatrix s id) := Matrix.linearIndependent_row_iff_isUnit.1 hli'
  exact (Matrix.isUnit_iff_isUnit_det _).1 hu |>.ne_zero

/-- A matrix with a nonzero maximal minor has injective `mulVec`. -/
theorem ancrs_injective_of_minor {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (A : Matrix ι κ ℂ) (s : κ → ι) (hs : (A.submatrix s id).det ≠ 0) :
    Function.Injective A.mulVec := by
  have hu : IsUnit (A.submatrix s id) := (Matrix.isUnit_iff_isUnit_det _).2 (Ne.isUnit hs)
  have hinj : Function.Injective (A.submatrix s id).mulVec :=
    Matrix.mulVec_injective_iff_isUnit.2 hu
  intro x x' hxx'
  apply hinj
  have h1 : ∀ x, (A.submatrix s id).mulVec x = A.mulVec x ∘ s := fun x ↦ by
    funext k; simp [Matrix.mulVec, dotProduct, Matrix.submatrix_apply]
  rw [h1, h1, hxx']

/-- **Local injectivity.** A map with an injective strict derivative between finite-dimensional
spaces is injective near the point. -/
theorem ancrs_injOn_of_injective {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
    {f : E → F} {f' : E →L[ℂ] F} {p : E} (hf : HasStrictFDerivAt f f' p)
    (hinj : Function.Injective f') :
    ∃ U ∈ 𝓝 p, InjOn f U := by
  obtain ⟨lin0, hlin0⟩ := (f' : E →ₗ[ℂ] F).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.2 hinj)
  let linc : F →L[ℂ] E := LinearMap.toContinuousLinearMap lin0
  have hcomp : linc ∘L f' = ContinuousLinearMap.id ℂ E := by
    ext1 u
    exact congrArg (fun T : E →ₗ[ℂ] E ↦ T u) hlin0
  have hg : HasStrictFDerivAt (fun x ↦ linc (f x))
      ((ContinuousLinearEquiv.refl ℂ E : E ≃L[ℂ] E) : E →L[ℂ] E) p := by
    have := linc.hasStrictFDerivAt.comp p hf
    rw [hcomp] at this
    exact this
  refine ⟨(hg.toOpenPartialHomeomorph _).source,
    (hg.toOpenPartialHomeomorph _).open_source.mem_nhds hg.mem_toOpenPartialHomeomorph_source,
    fun x hx x' hx' hxx' ↦ ?_⟩
  have := (hg.toOpenPartialHomeomorph _).injOn hx hx'
  exact this (by simp only [HasStrictFDerivAt.toOpenPartialHomeomorph_coe]; rw [hxx'])

end Linear

section Cut

variable {N e K : ℕ} {C : Set (Fin N → ℂ)} {y : Fin N → ℂ}

namespace ancrs_Param

variable (D : ancrs_Param N e C y) (L : (Fin N → ℂ) →L[ℂ] (Fin K → ℂ))

/-- The reconstructed point `r(w, t) / Δ(w)`. -/
def Θ (p : (Fin e → ℂ) × ℂ) : Fin N → ℂ := (D.Δ p.1)⁻¹ • D.Rf p

/-- The map `(w, t) ↦ (q(w, t), L(r(w, t) / Δ(w)))`. -/
def Ψ (p : (Fin e → ℂ) × ℂ) : ℂ × (Fin K → ℂ) := (D.qf p, L (D.Θ p))

/-- The derivative of `Ψ` with its second component multiplied by `Δ²`: analytic everywhere. -/
def A (p : (Fin e → ℂ) × ℂ) : ((Fin e → ℂ) × ℂ) →L[ℂ] ℂ × (Fin K → ℂ) :=
  (fderiv ℂ D.qf p).prod (L ∘L (D.Δ p.1 • fderiv ℂ D.Rf p -
    (fderiv ℂ D.Δ p.1 ∘L ContinuousLinearMap.fst ℂ (Fin e → ℂ) ℂ).smulRight (D.Rf p)))

end ancrs_Param

/-- Vectors indexed by `Fin e ⊕ Unit` as points of `ℂᵉ × ℂ`. -/
def ancrs_toV {e : ℕ} (x : (Fin e ⊕ Unit) → ℂ) : (Fin e → ℂ) × ℂ :=
  (fun i ↦ x (Sum.inl i), x (Sum.inr ()))

/-- Coordinates of `ℂ × ℂᴷ` indexed by `Unit ⊕ Fin K`. -/
def ancrs_coordW {K : ℕ} (w : ℂ × (Fin K → ℂ)) : (Unit ⊕ Fin K) → ℂ :=
  Sum.elim (fun _ ↦ w.1) w.2

theorem ancrs_toV_linear {e : ℕ} (x : (Fin e ⊕ Unit) → ℂ) :
    ancrs_toV x = ∑ c, x c • ancrs_toV (Pi.single c 1) := by
  have h1 : ∀ c, ancrs_toV (x c • Pi.single c (1 : ℂ)) = x c • ancrs_toV (Pi.single c 1) := by
    intro c; ext <;> simp [ancrs_toV]
  have h2 : ancrs_toV (∑ c, x c • Pi.single c (1 : ℂ)) = ∑ c, ancrs_toV (x c • Pi.single c 1) := by
    ext <;> simp [ancrs_toV, Finset.sum_apply, Prod.fst_sum, Prod.snd_sum]
  rw [← Finset.sum_congr rfl fun c _ ↦ h1 c, ← h2]
  congr 1
  ext c
  simp [Finset.sum_apply, Pi.single_apply]

theorem ancrs_toV_injective {e : ℕ} : Function.Injective (ancrs_toV (e := e)) := by
  intro x x' h
  funext c
  rcases c with i | u
  · exact congrFun (congrArg Prod.fst h) i
  · cases u; exact congrArg Prod.snd h

theorem ancrs_toV_surjective {e : ℕ} : Function.Surjective (ancrs_toV (e := e)) := by
  intro p
  exact ⟨Sum.elim p.1 (fun _ ↦ p.2), rfl⟩

theorem ancrs_coordW_injective {K : ℕ} : Function.Injective (ancrs_coordW (K := K)) := by
  intro w w' h
  ext
  · exact congrFun h (Sum.inl ())
  · exact congrFun h (Sum.inr _)

theorem ancrs_coordW_add {K : ℕ} (w w' : ℂ × (Fin K → ℂ)) :
    ancrs_coordW (w + w') = ancrs_coordW w + ancrs_coordW w' := by
  funext r; rcases r with u | i <;> rfl

theorem ancrs_coordW_smul {K : ℕ} (a : ℂ) (w : ℂ × (Fin K → ℂ)) :
    ancrs_coordW (a • w) = a • ancrs_coordW w := by
  funext r; rcases r with u | i <;> rfl

namespace ancrs_Param

variable (D : ancrs_Param N e C y) (L : (Fin N → ℂ) →L[ℂ] (Fin K → ℂ))

/-- The matrix of `A`. -/
def mat (p : (Fin e → ℂ) × ℂ) : Matrix (Unit ⊕ Fin K) (Fin e ⊕ Unit) ℂ :=
  Matrix.of fun r c ↦ ancrs_coordW (D.A L p (ancrs_toV (Pi.single c 1))) r

theorem mat_mulVec (p : (Fin e → ℂ) × ℂ) (x : (Fin e ⊕ Unit) → ℂ) :
    (D.mat L p).mulVec x = ancrs_coordW (D.A L p (ancrs_toV x)) := by
  have hsum : ∀ (t : Finset (Fin e ⊕ Unit)) (f : (Fin e ⊕ Unit) → ℂ × (Fin K → ℂ)),
      ancrs_coordW (∑ c ∈ t, f c) = ∑ c ∈ t, ancrs_coordW (f c) := by
    intro t f
    induction t using Finset.induction_on with
    | empty => funext r; rcases r with u | i <;> rfl
    | insert a t ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, ancrs_coordW_add, ih]
  rw [ancrs_toV_linear x, map_sum, hsum]
  simp_rw [map_smul, ancrs_coordW_smul]
  funext r
  simp [Matrix.mulVec, dotProduct, mat, Finset.sum_apply, mul_comm]

theorem mat_injective_iff (p : (Fin e → ℂ) × ℂ) :
    Function.Injective (D.mat L p).mulVec ↔ Function.Injective (D.A L p) := by
  constructor
  · intro h u u' huu'
    obtain ⟨x, rfl⟩ := ancrs_toV_surjective u
    obtain ⟨x', rfl⟩ := ancrs_toV_surjective u'
    have := h (show (D.mat L p).mulVec x = (D.mat L p).mulVec x' by
      rw [mat_mulVec, mat_mulVec, huu'])
    rw [this]
  · intro h x x' hxx'
    rw [mat_mulVec, mat_mulVec] at hxx'
    exact ancrs_toV_injective (h (ancrs_coordW_injective hxx'))

/-- The minor of `A` on the rows `s`. -/
def minor (s : (Fin e ⊕ Unit) → (Unit ⊕ Fin K)) (p : (Fin e → ℂ) × ℂ) : ℂ :=
  ((D.mat L p).submatrix s id).det

/-- The cut function: `Δ(π v)` times a minor of `A` at `(π v, ℓ v)`, `v = z - y`. -/
def cut (s : (Fin e ⊕ Unit) → (Unit ⊕ Fin K)) (z : Fin N → ℂ) : ℂ :=
  D.Δ (D.π (z - y)) * D.minor L s (D.π (z - y), D.ℓ (z - y))

end ancrs_Param

/-- The determinant of a matrix of analytic functions is analytic. -/
theorem ancrs_analyticAt_det {ι E : Type*} [Fintype ι] [DecidableEq ι] [NormedAddCommGroup E]
    [NormedSpace ℂ E] {M : E → Matrix ι ι ℂ} {p : E}
    (h : ∀ i j, AnalyticAt ℂ (fun x ↦ M x i j) p) : AnalyticAt ℂ (fun x ↦ (M x).det) p := by
  simp only [Matrix.det_apply]
  refine Finset.analyticAt_fun_sum _ fun σ _ ↦ ?_
  simp only [Units.smul_def, zsmul_eq_mul]
  exact analyticAt_const.mul (Finset.analyticAt_fun_prod _ fun i _ ↦ h _ _)

namespace ancrs_Param

variable (D : ancrs_Param N e C y) (L : (Fin N → ℂ) →L[ℂ] (Fin K → ℂ))

theorem A_apply_analyticAt {p : (Fin e → ℂ) × ℂ} (hp : ‖p.1‖ < D.ρw)
    (u : (Fin e → ℂ) × ℂ) : AnalyticAt ℂ (fun p' ↦ D.A L p' u) p := by
  have hq : AnalyticAt ℂ (fun p' ↦ fderiv ℂ D.qf p' u) p :=
    ((ContinuousLinearMap.apply ℂ ℂ u).analyticAt _).comp (D.qf_an p.1 hp p.2).fderiv
  have hR : AnalyticAt ℂ (fun p' ↦ fderiv ℂ D.Rf p' u) p :=
    ((ContinuousLinearMap.apply ℂ (Fin N → ℂ) u).analyticAt _).comp
      (D.Rf_an p.1 hp p.2).fderiv
  have hΔ1 : AnalyticAt ℂ (fun p' : (Fin e → ℂ) × ℂ ↦ fderiv ℂ D.Δ p'.1 u.1) p :=
    (((ContinuousLinearMap.apply ℂ ℂ u.1).analyticAt _).comp (D.Δ_an p.1 hp).fderiv).comp
      analyticAt_fst
  have hΔ0 : AnalyticAt ℂ (fun p' : (Fin e → ℂ) × ℂ ↦ D.Δ p'.1) p :=
    (D.Δ_an p.1 hp).comp analyticAt_fst
  have hR0 : AnalyticAt ℂ D.Rf p := D.Rf_an p.1 hp p.2
  have : (fun p' ↦ D.A L p' u) = fun p' ↦ (fderiv ℂ D.qf p' u,
      L (D.Δ p'.1 • fderiv ℂ D.Rf p' u - fderiv ℂ D.Δ p'.1 u.1 • D.Rf p')) := by
    funext p'
    simp [A]
  rw [this]
  exact hq.prod ((L.analyticAt _).comp ((hΔ0.smul hR).sub (hΔ1.smul hR0)))

theorem minor_analyticAt (s : (Fin e ⊕ Unit) → (Unit ⊕ Fin K)) {p : (Fin e → ℂ) × ℂ}
    (hp : ‖p.1‖ < D.ρw) : AnalyticAt ℂ (D.minor L s) p := by
  unfold minor
  refine ancrs_analyticAt_det fun i j ↦ ?_
  simp only [Matrix.submatrix_apply, id, mat, Matrix.of_apply]
  rcases (s i) with u | k
  · exact analyticAt_fst.comp (D.A_apply_analyticAt L hp _)
  · exact ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin K ↦ ℂ) k).analyticAt _).comp
      (analyticAt_snd.comp (D.A_apply_analyticAt L hp _))

theorem cut_analyticAt (s : (Fin e ⊕ Unit) → (Unit ⊕ Fin K)) : AnalyticAt ℂ (D.cut L s) y := by
  have hφ : AnalyticAt ℂ (fun z : Fin N → ℂ ↦ z - y) y := analyticAt_id.sub analyticAt_const
  have hπ : AnalyticAt ℂ (fun z : Fin N → ℂ ↦ D.π (z - y)) y := (D.π.analyticAt _).comp hφ
  have hℓ : AnalyticAt ℂ (fun z : Fin N → ℂ ↦ D.ℓ (z - y)) y := (D.ℓ.analyticAt _).comp hφ
  have h0 : ‖D.π (y - y)‖ < D.ρw := D.π_small _ (by simpa using D.ρ_pos)
  unfold cut
  refine (AnalyticAt.comp_of_eq (g := D.Δ) (f := fun z ↦ D.π (z - y)) (D.Δ_an _ h0) hπ
    rfl).mul ?_
  exact AnalyticAt.comp_of_eq (g := D.minor L s) (f := fun z ↦ (D.π (z - y), D.ℓ (z - y)))
    (D.minor_analyticAt L s (p := (D.π (y - y), D.ℓ (y - y))) h0) (hπ.prod hℓ) rfl

end ancrs_Param

namespace ancrs_Param

variable (D : ancrs_Param N e C y) (L : (Fin N → ℂ) →L[ℂ] (Fin K → ℂ))

theorem Θ_analyticAt {p : (Fin e → ℂ) × ℂ} (hp : ‖p.1‖ < D.ρw) (hΔ : D.Δ p.1 ≠ 0) :
    AnalyticAt ℂ D.Θ p :=
  (((D.Δ_an p.1 hp).comp analyticAt_fst).inv hΔ).smul (D.Rf_an p.1 hp p.2)

theorem Ψ_analyticAt {p : (Fin e → ℂ) × ℂ} (hp : ‖p.1‖ < D.ρw) (hΔ : D.Δ p.1 ≠ 0) :
    AnalyticAt ℂ (D.Ψ L) p :=
  (D.qf_an p.1 hp p.2).prod ((L.analyticAt _).comp (D.Θ_analyticAt hp hΔ))

/-- On `C`, the reconstructed point is the point. -/
theorem Θ_eq {v : Fin N → ℂ} (hv : ‖v‖ < D.ρ) (hvC : y + v ∈ C) (hΔ : D.Δ (D.π v) ≠ 0) :
    D.Θ (D.π v, D.ℓ v) = v := by
  funext i
  have := D.eq_coord v hv hvC i
  simp only [Θ, Pi.smul_apply, smul_eq_mul]
  rw [← this]
  field_simp

/-- The derivative of `Ψ` and `A`. -/
theorem A_eq {p : (Fin e → ℂ) × ℂ} (hp : ‖p.1‖ < D.ρw) (hΔ : D.Δ p.1 ≠ 0)
    (x : (Fin e → ℂ) × ℂ) :
    D.A L p x = ((fderiv ℂ (D.Ψ L) p x).1, (D.Δ p.1) ^ 2 • (fderiv ℂ (D.Ψ L) p x).2) := by
  have hΘ := (D.Θ_analyticAt hp hΔ).differentiableAt.hasFDerivAt
  have hq := (D.qf_an p.1 hp p.2).differentiableAt.hasFDerivAt
  have hΨ : HasFDerivAt (D.Ψ L) ((fderiv ℂ D.qf p).prod (L ∘L fderiv ℂ D.Θ p)) p :=
    hq.prodMk (L.hasFDerivAt.comp p hΘ)
  rw [hΨ.fderiv]
  have hΔf : HasFDerivAt (fun p' : (Fin e → ℂ) × ℂ ↦ D.Δ p'.1)
      (fderiv ℂ D.Δ p.1 ∘L ContinuousLinearMap.fst ℂ (Fin e → ℂ) ℂ) p :=
    (D.Δ_an p.1 hp).differentiableAt.hasFDerivAt.comp p hasFDerivAt_fst
  have hev : (fun p' : (Fin e → ℂ) × ℂ ↦ D.Δ p'.1 • D.Θ p') =ᶠ[𝓝 p] D.Rf := by
    have hc : ContinuousAt (fun p' : (Fin e → ℂ) × ℂ ↦ D.Δ p'.1) p := hΔf.continuousAt
    filter_upwards [hc.eventually_ne hΔ] with p' hp'
    simp only [Θ, smul_smul, mul_inv_cancel₀ hp', one_smul]
  have hR : HasFDerivAt D.Rf (D.Δ p.1 • fderiv ℂ D.Θ p +
      (fderiv ℂ D.Δ p.1 ∘L ContinuousLinearMap.fst ℂ (Fin e → ℂ) ℂ).smulRight (D.Θ p)) p :=
    (hΔf.smul hΘ).congr_of_eventuallyEq hev.symm
  have hRp : D.Rf p = D.Δ p.1 • D.Θ p := (hev.self_of_nhds).symm
  simp only [A, ContinuousLinearMap.prod_apply, ContinuousLinearMap.comp_apply, hR.fderiv]
  refine Prod.ext rfl ?_
  simp only [sub_apply, smul_apply,
    ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst', hRp, map_sub, map_smul, add_apply,
    map_add, smul_add, smul_smul]
  rw [sq]
  module

theorem injective_fderiv_Ψ_iff {p : (Fin e → ℂ) × ℂ} (hp : ‖p.1‖ < D.ρw) (hΔ : D.Δ p.1 ≠ 0) :
    Function.Injective (D.A L p) ↔ Function.Injective (fderiv ℂ (D.Ψ L) p) := by
  have h2 : (D.Δ p.1) ^ 2 ≠ 0 := pow_ne_zero 2 hΔ
  constructor
  · intro h x x' hxx'
    apply h
    rw [D.A_eq L hp hΔ, D.A_eq L hp hΔ, hxx']
  · intro h x x' hxx'
    apply h
    rw [D.A_eq L hp hΔ, D.A_eq L hp hΔ] at hxx'
    have h1 := congrArg Prod.fst hxx'
    have h3 := smul_right_injective _ h2 (congrArg Prod.snd hxx')
    exact Prod.ext h1 h3

/-- **The cut vanishes at points not isolated in their fibre.** At a point `y + v` of `C` off
`Δ ∘ π = 0` that is not isolated in its fibre of `L` on `C`, every minor of `A` vanishes at
`(π v, ℓ v)`: otherwise `Ψ` would be injective near that point. -/
theorem minor_eq_zero_of_not_isolated {v : Fin N → ℂ} (hv : ‖v‖ < D.ρ) (hvC : y + v ∈ C)
    (hΔ : D.Δ (D.π v) ≠ 0)
    (hni : ¬ ∀ᶠ z in 𝓝 (y + v), z ∈ C → L z = L (y + v) → z = y + v)
    (s : (Fin e ⊕ Unit) → (Unit ⊕ Fin K)) : D.minor L s (D.π v, D.ℓ v) = 0 := by
  by_contra hne
  set p : (Fin e → ℂ) × ℂ := (D.π v, D.ℓ v)
  have hp : ‖p.1‖ < D.ρw := D.π_small v hv
  have hinjA := (D.mat_injective_iff L p).1 (ancrs_injective_of_minor _ s hne)
  have hinjΨ := (D.injective_fderiv_Ψ_iff L hp hΔ).1 hinjA
  obtain ⟨U, hU, hinjU⟩ := ancrs_injOn_of_injective
    (D.Ψ_analyticAt L hp hΔ).hasStrictFDerivAt hinjΨ
  set φ : (Fin N → ℂ) → (Fin e → ℂ) × ℂ := fun z ↦ (D.π (z - y), D.ℓ (z - y))
  have hφc : Continuous φ :=
    (D.π.continuous.comp (continuous_id.sub continuous_const)).prodMk
      (D.ℓ.continuous.comp (continuous_id.sub continuous_const))
  have hφp : φ (y + v) = p := by simp [φ, p]
  have hev1 : ∀ᶠ z in 𝓝 (y + v), φ z ∈ U :=
    hφc.continuousAt.preimage_mem_nhds (hφp ▸ hU)
  have hev2 : ∀ᶠ z in 𝓝 (y + v), ‖z - y‖ < D.ρ := by
    have hc : Continuous fun z : Fin N → ℂ ↦ ‖z - y‖ := (continuous_id.sub continuous_const).norm
    exact hc.continuousAt.eventually_lt continuousAt_const (by simpa using hv)
  have hev3 : ∀ᶠ z in 𝓝 (y + v), D.Δ (D.π (z - y)) ≠ 0 := by
    have hc : ContinuousAt (fun z : Fin N → ℂ ↦ D.Δ (D.π (z - y))) (y + v) := by
      have h1 : ContinuousAt D.Δ (D.π v) := (D.Δ_an _ hp).continuousAt
      exact h1.comp_of_eq (D.π.continuous.comp (continuous_id.sub continuous_const)).continuousAt
        (by simp)
    exact hc.eventually_ne (by simpa using hΔ)
  apply hni
  filter_upwards [hev1, hev2, hev3] with z hzU hzρ hzΔ hzC hzL
  have hzC' : y + (z - y) ∈ C := by simpa using hzC
  have hΘz : D.Θ (φ z) = z - y := D.Θ_eq hzρ hzC' hzΔ
  have hΘp : D.Θ p = v := D.Θ_eq hv hvC hΔ
  have key : D.Ψ L (φ z) = D.Ψ L p := by
    simp only [Ψ]
    refine Prod.ext ?_ ?_
    · exact (D.eq_root _ hzρ hzC').trans (D.eq_root v hv hvC).symm
    · change L (D.Θ (φ z)) = L (D.Θ p)
      rw [hΘz, hΘp, map_sub, hzL, map_add, add_sub_cancel_left]
  have h1 := hinjU hzU (mem_of_mem_nhds hU) key
  have : z - y = v := by rw [← hΘz, h1, hΘp]
  rw [← this, add_sub_cancel]

end ancrs_Param

/-- **Implicit function at a simple zero.** -/
theorem ancrs_implicit {d : ℕ} {F : (Fin d → ℂ) × ℂ → ℂ} {w₀ : Fin d → ℂ} {t₀ : ℂ}
    (hFa : AnalyticAt ℂ F (w₀, t₀)) (hF0 : F (w₀, t₀) = 0)
    (hd : fderiv ℂ F (w₀, t₀) (0, 1) ≠ 0) :
    ∃ τ : (Fin d → ℂ) → ℂ, AnalyticAt ℂ τ w₀ ∧ τ w₀ = t₀ ∧
      ∃ U : Set ((Fin d → ℂ) × ℂ), IsOpen U ∧ (w₀, t₀) ∈ U ∧
        ∀ u ∈ U, (F u = 0 ↔ τ u.1 = u.2) := by
  have cdf : ContDiffAt ℂ ω F (w₀, t₀) := hFa.contDiffAt
  have pn : (ω : WithTop ℕ∞) ≠ 0 := by simp
  set c := fderiv ℂ F (w₀, t₀) (0, 1)
  have hder : fderiv ℂ F (w₀, t₀) ∘L ContinuousLinearMap.inr ℂ (Fin d → ℂ) ℂ =
      (1 : ℂ →L[ℂ] ℂ).smulRight c := by
    ext1
    simp [c]
  have if₂ : (fderiv ℂ F (w₀, t₀) ∘L ContinuousLinearMap.inr ℂ (Fin d → ℂ) ℂ).IsInvertible := by
    rw [hder]
    refine ⟨ContinuousLinearEquiv.unitsEquivAut ℂ (Units.mk0 c hd), ?_⟩
    ext
    simp [ContinuousLinearEquiv.unitsEquivAut_apply]
  refine ⟨cdf.implicitFunction pn if₂, (cdf.contDiffAt_implicitFunction pn if₂).analyticAt,
    cdf.implicitFunction_apply_self pn if₂, ?_⟩
  obtain ⟨U, hU, hUo, hU0⟩ :=
    eventually_nhds_iff.1 (cdf.eventually_apply_eq_iff_implicitFunction pn if₂)
  refine ⟨U, hUo, hU0, fun u hu ↦ ?_⟩
  have := hU u hu
  simp only [hF0] at this
  exact this

namespace ancrs_Param

variable (D : ancrs_Param N e C y) (L : (Fin N → ℂ) →L[ℂ] (Fin K → ℂ))

theorem Θ_eq_div (p : (Fin e → ℂ) × ℂ) : D.Θ p = fun i ↦ D.Rf p i / D.Δ p.1 := by
  funext i
  simp [Θ, div_eq_inv_mul]

/-- **The kernel argument.** Along an analytic branch `τ` of roots, if `L ∘ Θ ∘ (id, τ)` has an
injective derivative at `w`, then `Ψ` has an injective derivative at `(w, τ w)`. -/
theorem injective_fderiv_Ψ_of_branch {τ : (Fin e → ℂ) → ℂ} {w : Fin e → ℂ}
    (hw : ‖w‖ < D.ρw) (hΔ : D.Δ w ≠ 0) (hτ : AnalyticAt ℂ τ w)
    (hroot : ∀ᶠ w' in 𝓝 w, D.qf (w', τ w') = 0)
    (hinj : Function.Injective (fderiv ℂ (fun w' ↦ L (D.Θ (w', τ w'))) w)) :
    Function.Injective (fderiv ℂ (D.Ψ L) (w, τ w)) := by
  set p : (Fin e → ℂ) × ℂ := (w, τ w)
  have hp : ‖p.1‖ < D.ρw := hw
  have hq := (D.qf_an w hw (τ w)).differentiableAt.hasFDerivAt
  have hΘ : HasFDerivAt D.Θ (fderiv ℂ D.Θ (w, τ w)) (w, τ w) :=
    (D.Θ_analyticAt hp hΔ).differentiableAt.hasFDerivAt
  have hΨ : HasFDerivAt (D.Ψ L) ((fderiv ℂ D.qf p).prod (L ∘L fderiv ℂ D.Θ p)) p :=
    hq.prodMk (L.hasFDerivAt.comp p hΘ)
  have hb : HasFDerivAt (fun w' ↦ (w', τ w'))
      ((ContinuousLinearMap.id ℂ (Fin e → ℂ)).prod (fderiv ℂ τ w)) w :=
    (hasFDerivAt_id w).prodMk hτ.differentiableAt.hasFDerivAt
  -- the derivative of `q` vanishes along the branch
  have hq0 : (fderiv ℂ D.qf p) ∘L ((ContinuousLinearMap.id ℂ (Fin e → ℂ)).prod (fderiv ℂ τ w)) =
      0 := by
    have h1 : HasFDerivAt (fun w' ↦ D.qf (w', τ w'))
        ((fderiv ℂ D.qf p) ∘L ((ContinuousLinearMap.id ℂ (Fin e → ℂ)).prod (fderiv ℂ τ w))) w :=
      hq.comp w hb
    have h2 : HasFDerivAt (fun w' ↦ D.qf (w', τ w')) (0 : (Fin e → ℂ) →L[ℂ] ℂ) w :=
      (hasFDerivAt_const (0 : ℂ) w).congr_of_eventuallyEq hroot
    exact h1.unique h2
  have hΘb : HasFDerivAt (fun w' ↦ D.Θ (w', τ w'))
      (fderiv ℂ D.Θ p ∘L ((ContinuousLinearMap.id ℂ (Fin e → ℂ)).prod (fderiv ℂ τ w))) w :=
    HasFDerivAt.comp (g := D.Θ) (f := fun w' ↦ (w', τ w')) w hΘ hb
  have hG : HasFDerivAt (fun w' ↦ L (D.Θ (w', τ w')))
      (L ∘L fderiv ℂ D.Θ p ∘L ((ContinuousLinearMap.id ℂ (Fin e → ℂ)).prod (fderiv ℂ τ w))) w :=
    L.hasFDerivAt.comp w hΘb
  rw [hG.fderiv] at hinj
  rw [hΨ.fderiv]
  have hsim := D.simple w hw (τ w) ((hroot.self_of_nhds)) hΔ
  rw [injective_iff_map_eq_zero]
  rintro ⟨u, σ⟩ hx
  have hx1 : fderiv ℂ D.qf p (u, σ) = 0 := congrArg Prod.fst hx
  have hx2 : L (fderiv ℂ D.Θ p (u, σ)) = 0 := congrArg Prod.snd hx
  have hqu : fderiv ℂ D.qf p (u, fderiv ℂ τ w u) = 0 := by
    have := congrArg (fun T : (Fin e → ℂ) →L[ℂ] ℂ ↦ T u) hq0
    simpa using this
  have hσ : σ = fderiv ℂ τ w u := by
    have h3 : fderiv ℂ D.qf p ((0 : Fin e → ℂ), σ - fderiv ℂ τ w u) = 0 := by
      have : ((0 : Fin e → ℂ), σ - fderiv ℂ τ w u) = (u, σ) - (u, fderiv ℂ τ w u) := by
        ext <;> simp
      rw [this, map_sub, hx1, hqu, sub_zero]
    have h4 : ((0 : Fin e → ℂ), σ - fderiv ℂ τ w u) =
        (σ - fderiv ℂ τ w u) • ((0 : Fin e → ℂ), 1) := by
      ext <;> simp
    rw [h4, map_smul, smul_eq_mul] at h3
    exact sub_eq_zero.1 ((mul_eq_zero.1 h3).resolve_right hsim)
  have hu : u = 0 := by
    apply hinj
    rw [map_zero]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
      ContinuousLinearMap.id_apply]
    rw [← hσ]
    exact hx2
  rw [hσ, hu, map_zero]
  rfl

end ancrs_Param

namespace ancrs_Param

variable (D : ancrs_Param N e C y) (L : (Fin N → ℂ) →L[ℂ] (Fin K → ℂ))

/-- **Regular points are dense.** Near `y`, every point of `C` is a limit of points of `C` off
`Δ ∘ π = 0`: the part of `C` on `Δ ∘ π = 0` has dimension `< e` near `y` (Krull), while `C` has
dimension `e` at its points near `y`. -/
theorem dense_regular {Q : Ideal (AnalyticGerm N)} (hQ : Q.IsPrime)
    (hI : adim2_ideal N (adim2_germ N C y) = Q)
    (he : ringKrullDim (AnalyticGerm N ⧸ Q) = (e : WithBot ℕ∞)) (hloc : anrem_LocEq C y)
    (hpure : ∀ᶠ z in 𝓝 y, z ∈ C → adim2_dimension N (adim2_germ N C z) = (e : WithBot ℕ∞)) :
    ∀ᶠ z₁ in 𝓝 y, z₁ ∈ C → ∀ ε > 0, ∃ z ∈ C, dist z z₁ < ε ∧ D.Δ (D.π (z - y)) ≠ 0 := by
  classical
  set D' : Set (Fin N → ℂ) := C ∩ {z | D.Δ (D.π (z - y)) = 0}
  have h0 : ‖D.π 0‖ < D.ρw := D.π_small 0 (by simpa using D.ρ_pos)
  have han0 : AnalyticAt ℂ (fun v ↦ D.Δ (D.π v)) 0 :=
    AnalyticAt.comp_of_eq (g := D.Δ) (f := D.π) (D.Δ_an _ h0) (D.π.analyticAt 0) rfl
  let hg : AnalyticGerm N := ⟨Filter.Germ.ofFun (fun v ↦ D.Δ (D.π v)), _, han0, rfl⟩
  have hhJ : hg ∈ adim2_ideal N (adim2_germ N D' y) := by
    rw [anrem_mem_ideal_iff D' y hg _ rfl]
    exact Eventually.of_forall fun v hv ↦ by simpa [D'] using hv.2
  have hhQ : hg ∉ Q := by
    rw [← hI, anrem_mem_ideal_iff C y hg _ rfl]
    exact D.nonvanish
  have hQJ : Q ≤ adim2_ideal N (adim2_germ N D' y) :=
    hI ▸ anr_ideal_anti inter_subset_left y
  have hdrop := ancrs_dim_sup_lt (P := Q) hhJ hhQ
  rw [sup_eq_right.2 hQJ, he] at hdrop
  have hlocD' : anrem_LocEq D' y := by
    have hz : AnalyticAt ℂ (fun z ↦ D.Δ (D.π (z - y))) y :=
      AnalyticAt.comp_of_eq (g := fun v ↦ D.Δ (D.π v)) (f := fun z ↦ z - y) (by simpa using han0)
        (analyticAt_id.sub analyticAt_const) (by simp)
    exact anrem_locEq_inter hloc (ancrs_locEq_zero hz)
  have hsmall : ∀ᶠ z in 𝓝 y, z ∈ D' → adim2_dimension N (adim2_germ N D' z) < (e : WithBot ℕ∞) := by
    by_cases hyD : y ∈ D'
    · obtain ⟨j, -, hj⟩ := ancrs_dimension_cases hyD
      have hje : j + 1 ≤ e := by
        have : ((j : ℕ) : WithBot ℕ∞) + 1 ≤ (e : WithBot ℕ∞) := by
          change adim2_dimension N (adim2_germ N D' y) + 1 ≤ _ at hdrop
          rwa [hj] at hdrop
        exact_mod_cast this
      filter_upwards [anrem_dimension_upper hlocD' (e := j) hj.le] with z hz _
      exact lt_of_le_of_lt hz (by exact_mod_cast (show j < e by omega))
    · filter_upwards [ancrs_eventually_not_mem hlocD' hyD] with z hz hzD using absurd hzD hz
  filter_upwards [hsmall, hpure] with z₁ hz₁D hz₁C hz₁ ε hε
  by_contra hcon
  push Not at hcon
  have hsub : ∀ᶠ z in 𝓝 z₁, z ∈ C → z ∈ D' := by
    filter_upwards [Metric.ball_mem_nhds z₁ hε] with z hz hzC
    exact ⟨hzC, hcon z hzC hz⟩
  have hmono := anrem_dimension_mono hsub
  have hz₁D' : z₁ ∈ D' := ⟨hz₁, hcon z₁ hz₁ (by simpa using hε)⟩
  have := lt_of_le_of_lt hmono (hz₁D hz₁D')
  rw [hz₁C hz₁] at this
  exact lt_irrefl _ this

end ancrs_Param

namespace ancrs_Param

variable (D : ancrs_Param N e C y) (L : (Fin N → ℂ) →L[ℂ] (Fin K → ℂ))

/-- **Some cut function does not vanish on `C` near `y`.** If every neighbourhood of `y` contains
points of `C` isolated in their fibre of `L` on `C`, some minor of `A` does not vanish identically
on `C` near `y`. Otherwise, near such a point, on an analytic branch of roots through a nearby
regular point, `L ∘ Θ` would have finite fibres but nowhere an injective derivative. -/
theorem exists_cut_ne {Q : Ideal (AnalyticGerm N)} (hQ : Q.IsPrime)
    (hI : adim2_ideal N (adim2_germ N C y) = Q)
    (he : ringKrullDim (AnalyticGerm N ⧸ Q) = (e : WithBot ℕ∞)) (hloc : anrem_LocEq C y)
    (hpure : ∀ᶠ z in 𝓝 y, z ∈ C → adim2_dimension N (adim2_germ N C z) = (e : WithBot ℕ∞))
    (hfin : ∀ U ∈ 𝓝 y, ∃ z₁ ∈ C ∩ U, ∀ᶠ z in 𝓝 z₁, z ∈ C → L z = L z₁ → z = z₁) :
    ∃ s, ¬ ∀ᶠ z in 𝓝 y, z ∈ C → D.cut L s z = 0 := by
  classical
  by_contra hall
  push Not at hall
  have hH : ∀ᶠ z in 𝓝 y, z ∈ C → ∀ s, D.cut L s z = 0 := by
    have := Filter.eventually_all.2 hall
    filter_upwards [this] with z hz hzC s using hz s hzC
  have hdense := D.dense_regular hQ hI he hloc hpure
  obtain ⟨U₀, hU₀, hyU₀, m, f, hf, hCU₀⟩ := hloc
  have hU₀ev : ∀ᶠ z in 𝓝 y, z ∈ U₀ := hU₀.mem_nhds hyU₀
  have hballev : ∀ᶠ z in 𝓝 y, z ∈ Metric.ball y D.ρ := Metric.ball_mem_nhds y D.ρ_pos
  obtain ⟨O, hOsub, hOo, hyO⟩ := eventually_nhds_iff.1
    (hH.and (hdense.and (hU₀ev.and hballev)))
  obtain ⟨z₁, ⟨hz₁C, hz₁O⟩, hiso⟩ := hfin O (hOo.mem_nhds hyO)
  obtain ⟨Riso, hRiso, hiso'⟩ := Metric.eventually_nhds_iff.1 hiso
  obtain ⟨R₀, hR₀, hR₀O⟩ := Metric.isOpen_iff.1 hOo z₁ hz₁O
  set R := min R₀ Riso / 2 with hRdef
  have hR : 0 < R := by positivity
  have hRR₀ : R < R₀ := by
    have := min_le_left R₀ Riso; rw [hRdef]; linarith
  have hRRi : R < Riso := by
    have := min_le_right R₀ Riso; rw [hRdef]; linarith
  have hcbO : Metric.closedBall z₁ R ⊆ O :=
    (Metric.closedBall_subset_ball hRR₀).trans hR₀O
  have hK : IsClosed (C ∩ Metric.closedBall z₁ R) :=
    ancrs_isClosed_inter_closedBall (fun j ↦ (hf j).continuousOn) hCU₀
      (hcbO.trans fun z hz ↦ (hOsub z hz).2.2.1)
  have hsph0 : ∀ z ∈ C ∩ Metric.closedBall z₁ R, L z = L z₁ → ‖z - z₁‖ ≠ R := by
    intro z hz hzL h
    have hd : dist z z₁ < Riso := by rw [dist_eq_norm, h]; exact hRRi
    have := hiso' hd hz.1 hzL
    rw [this, sub_self, norm_zero] at h
    exact hR.ne h
  obtain ⟨r, hr, hsph⟩ := anr_box_radius (C ∩ Metric.closedBall z₁ R) hK L z₁ R hsph0
  have hBloc : ∀ z ∈ C ∩ Metric.ball z₁ R, anrem_LocEq (C ∩ Metric.ball z₁ R) z := by
    intro z hz
    have hzU : z ∈ U₀ := (hOsub z (hcbO (Metric.ball_subset_closedBall hz.2))).2.2.1
    exact anrem_locEq_inter ⟨U₀, hU₀, hzU, m, f, hf, hCU₀⟩
      (ancrs_locEq_open Metric.isOpen_ball hz.2)
  have hfinB : ∀ c, ‖c - L z₁‖ < r →
      {z | z ∈ C ∩ Metric.ball z₁ R ∧ ‖z - z₁‖ < R ∧ L z = c}.Finite := fun c hc ↦
    anr_fib_finite (C ∩ Metric.ball z₁ R) (C ∩ Metric.closedBall z₁ R) hK
      (inter_subset_inter_right _ Metric.ball_subset_closedBall) hBloc L z₁ R r hsph c hc
      (fun z hz hzR _ ↦ ⟨hz.1, by rwa [Metric.mem_ball, dist_eq_norm]⟩)
  obtain ⟨εL, hεL, hLc⟩ := Metric.continuousAt_iff.1 L.continuous.continuousAt (r / 2)
    (by positivity)
  -- a regular point near `z₁`
  obtain ⟨z₂, hz₂C, hz₂d, hz₂Δ⟩ := (hOsub z₁ hz₁O).2.1 hz₁C (min (R / 2) εL) (by positivity)
  have hz₂R : dist z₂ z₁ < R / 2 := hz₂d.trans_le (min_le_left _ _)
  have hz₂L : dist (L z₂) (L z₁) < r / 2 := hLc (hz₂d.trans_le (min_le_right _ _))
  have hz₂O : z₂ ∈ O := hR₀O (show dist z₂ z₁ < R₀ by linarith)
  set v₂ := z₂ - y with hv₂def
  have hv₂ : ‖v₂‖ < D.ρ := by
    have := (hOsub z₂ hz₂O).2.2.2
    rwa [Metric.mem_ball, dist_eq_norm] at this
  have hv₂C : y + v₂ ∈ C := by simpa [v₂] using hz₂C
  set w₂ := D.π v₂
  set t₂ := D.ℓ v₂
  have hw₂ : ‖w₂‖ < D.ρw := D.π_small v₂ hv₂
  have hq₂ : D.qf (w₂, t₂) = 0 := D.eq_root v₂ hv₂ hv₂C
  have hsim₂ := D.simple w₂ hw₂ t₂ hq₂ hz₂Δ
  obtain ⟨τ, hτa, hτ₂, U', hU'o, hp₂U', hU'⟩ := ancrs_implicit (D.qf_an w₂ hw₂ t₂) hq₂ hsim₂
  set g : (Fin e → ℂ) → (Fin N → ℂ) := fun w ↦ D.Θ (w, τ w) with hgdef
  have hb : AnalyticAt ℂ (fun w ↦ (w, τ w)) w₂ := analyticAt_id.prod hτa
  have hga : AnalyticAt ℂ g w₂ :=
    AnalyticAt.comp_of_eq (g := D.Θ) (f := fun w ↦ (w, τ w))
      (D.Θ_analyticAt (p := (w₂, t₂)) hw₂ hz₂Δ) hb (by rw [hτ₂])
  have hg₂ : g w₂ = v₂ := by
    simp only [g, hτ₂]
    exact D.Θ_eq hv₂ hv₂C hz₂Δ
  have hgc : ContinuousAt (fun w ↦ y + g w) w₂ := continuousAt_const.add hga.continuousAt
  have hz₂' : y + g w₂ = z₂ := by rw [hg₂, hv₂def, add_sub_cancel]
  have e1 : ∀ᶠ w in 𝓝 w₂, (w, τ w) ∈ U' :=
    hb.continuousAt.preimage_mem_nhds (hU'o.mem_nhds (by simpa [hτ₂] using hp₂U'))
  have e4 : ∀ᶠ w in 𝓝 w₂, D.Δ w ≠ 0 := (D.Δ_an w₂ hw₂).continuousAt.eventually_ne hz₂Δ
  have e5 : ∀ᶠ w in 𝓝 w₂, ‖w‖ < D.ρw :=
    continuous_norm.continuousAt.eventually_lt continuousAt_const hw₂
  have e6 : ∀ᶠ w in 𝓝 w₂, dist (y + g w) z₁ < R :=
    (hgc.dist continuousAt_const).eventually_lt continuousAt_const
      (by simp only; rw [hz₂']; linarith)
  have e7 : ∀ᶠ w in 𝓝 w₂, dist (L (y + g w)) (L z₁) < r :=
    ((L.continuous.continuousAt.comp hgc).dist continuousAt_const).eventually_lt
      continuousAt_const (by simp only [Function.comp_apply]; rw [hz₂']; linarith)
  have hev : ∀ᶠ w in 𝓝 w₂, (w, τ w) ∈ U' ∧ AnalyticAt ℂ g w ∧ AnalyticAt ℂ τ w ∧
      D.Δ w ≠ 0 ∧ ‖w‖ < D.ρw ∧ dist (y + g w) z₁ < R ∧ dist (L (y + g w)) (L z₁) < r :=
    e1.and (hga.eventually_analyticAt.and (hτa.eventually_analyticAt.and (e4.and (e5.and
      (e6.and e7)))))
  obtain ⟨η, hη, hηW⟩ := Metric.eventually_nhds_iff.1 hev
  have hWroot : ∀ w ∈ Metric.ball w₂ η, D.qf (w, τ w) = 0 := fun w hw ↦
    (hU' _ (hηW hw).1).2 rfl
  have hWC : ∀ w ∈ Metric.ball w₂ η, y + g w ∈ C ∧ D.π (g w) = w ∧ D.ℓ (g w) = τ w := by
    intro w hw
    obtain ⟨-, -, -, hΔw, hρw, -, -⟩ := hηW hw
    have := D.roots w hρw (τ w) hΔw (hWroot w hw)
    rw [← D.Θ_eq_div] at this
    exact this
  set G : (Fin e → ℂ) → (Fin K → ℂ) := fun w ↦ L (g w) with hGdef
  have hGa : AnalyticOnNhd ℂ G (Metric.ball w₂ η) := fun w hw ↦
    (L.analyticAt _).comp (hηW hw).2.1
  have hGfin : ∀ c, {w | w ∈ Metric.ball w₂ η ∧ G w = c}.Finite := by
    intro c
    by_cases hne : {w | w ∈ Metric.ball w₂ η ∧ G w = c}.Nonempty
    · obtain ⟨w₀, hw₀W, hw₀c⟩ := hne
      have hc : ‖(c + L y) - L z₁‖ < r := by
        have := (hηW hw₀W).2.2.2.2.2.2
        rw [dist_eq_norm, map_add] at this
        rwa [add_comm, ← hw₀c]
      refine Set.Finite.of_injOn (f := fun w ↦ y + g w) ?_ ?_ (hfinB (c + L y) hc)
      · rintro w ⟨hwW, hwc⟩
        refine ⟨⟨(hWC w hwW).1, ?_⟩, ?_, ?_⟩
        · exact (hηW hwW).2.2.2.2.2.1
        · rw [← dist_eq_norm]; exact (hηW hwW).2.2.2.2.2.1
        · simp only [map_add]
          rw [add_comm]
          exact congrArg (· + L y) hwc
      · intro w hw w' hw' hww'
        have h1 : g w = g w' := add_left_cancel hww'
        rw [← (hWC w hw.1).2.1, ← (hWC w' hw'.1).2.1, h1]
    · rw [Set.not_nonempty_iff_eq_empty] at hne
      rw [hne]
      exact Set.finite_empty
  obtain ⟨w, hwW, hinj⟩ := ancrs_exists_injective_of_finite_fibres Metric.isOpen_ball
    ⟨w₂, Metric.mem_ball_self hη⟩ hGa hGfin
  obtain ⟨-, -, hτw, hΔw, hρw, hdw, -⟩ := hηW hwW
  have hzC := (hWC w hwW).1
  have hzO : y + g w ∈ O := hR₀O (show dist (y + g w) z₁ < R₀ by linarith)
  have hcut := (hOsub _ hzO).1 hzC
  have hminor : ∀ s, D.minor L s (w, τ w) = 0 := by
    intro s
    have := hcut s
    simp only [cut, add_sub_cancel_left, (hWC w hwW).2.1, (hWC w hwW).2.2] at this
    exact (mul_eq_zero.1 this).resolve_left hΔw
  have hrootev : ∀ᶠ w' in 𝓝 w, D.qf (w', τ w') = 0 := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hwW] with w' hw' using hWroot w' hw'
  have hΨinj := D.injective_fderiv_Ψ_of_branch L hρw hΔw hτw hrootev hinj
  have hAinj := (D.injective_fderiv_Ψ_iff L (p := (w, τ w)) hρw hΔw).2 hΨinj
  have hmat := (D.mat_injective_iff L (w, τ w)).2 hAinj
  obtain ⟨s, hs⟩ := ancrs_exists_minor _ hmat
  exact hs (hminor s)

end ancrs_Param

end Cut

section Main

variable {N : ℕ}

/-- A level set of a linear map has local equations everywhere. -/
theorem ancrs_locEq_level {p : ℕ} (P : (Fin N → ℂ) →L[ℂ] (Fin p → ℂ)) (c : Fin p → ℂ)
    (z : Fin N → ℂ) : anrem_LocEq (P ⁻¹' {c}) z :=
  ⟨univ, isOpen_univ, trivial, p, fun i z ↦ P z i - c i,
    fun i _ _ ↦ (((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin p ↦ ℂ) i).comp
      P).analyticAt _).sub analyticAt_const,
    fun w _ ↦ by
      simp only [mem_preimage, mem_singleton_iff, sub_eq_zero]
      exact ⟨fun h i ↦ by rw [h], fun h ↦ funext h⟩⟩

/-- Slicing data at a point of small fibre dimension: a ball on which the fibre has local
equations and germs of dimension at most `m`. -/
theorem ancrs_slice_ball {mP : ℕ} {C : Set (Fin N → ℂ)} {z₀ : Fin N → ℂ}
    (hloc : ∀ᶠ z in 𝓝 z₀, anrem_LocEq C z) (P : (Fin N → ℂ) →L[ℂ] (Fin mP → ℂ)) {m : ℕ}
    (hd : adim2_dimension N (adim2_germ N (C ∩ P ⁻¹' {P z₀}) z₀) ≤ m) :
    ∃ ρ > 0, (∀ w ∈ C ∩ P ⁻¹' {P z₀} ∩ Metric.ball z₀ ρ,
      anrem_LocEq (C ∩ P ⁻¹' {P z₀} ∩ Metric.ball z₀ ρ) w) ∧
      ∀ w ∈ C ∩ P ⁻¹' {P z₀} ∩ Metric.ball z₀ ρ,
        ∀ Q ∈ (adim2_ideal N (adim2_germ N (C ∩ P ⁻¹' {P z₀} ∩ Metric.ball z₀ ρ) w)).minimalPrimes,
          ringKrullDim (AnalyticGerm N ⧸ Q) ≤ (m : WithBot ℕ∞) := by
  have hX : ∀ᶠ z in 𝓝 z₀, anrem_LocEq (C ∩ P ⁻¹' {P z₀}) z := by
    filter_upwards [hloc] with z hz using anrem_locEq_inter hz (ancrs_locEq_level P _ z)
  have hdim := anrem_dimension_upper hX.self_of_nhds hd
  obtain ⟨ρ, hρ, hρw⟩ := Metric.eventually_nhds_iff.1 (hX.and hdim)
  refine ⟨ρ, hρ, fun w hw ↦ ?_, fun w hw Q hQ ↦ ?_⟩
  · exact anrem_locEq_inter (hρw hw.2).1 (ancrs_locEq_open Metric.isOpen_ball hw.2)
  · rw [anrem_germ_inter_nhds _ _ w (Metric.isOpen_ball.mem_nhds hw.2)] at hQ
    exact (anr_minimal_le_dim _ Q hQ).trans (hρw hw.2).2

/-- **The cut of a prime component.** Let `C` be, near `y`, an irreducible (prime) component of
dimension `e`, pure of dimension `e` near `y`, and suppose every neighbourhood of `y` contains
points of `C` whose `P`-fibre in `C` has dimension at most `m`. Then a function analytic at `y`, not
vanishing identically on `C` near `y`, vanishes at the points of `C` near `y` whose fibre has
dimension at least `m + 1`.
Source: Fischer, *Complex Analytic Geometry*, LNM 538, §3.6; Gunning–Rossi, Ch. III, §C (local
parametrization). -/
theorem ancrs_cut {mP : ℕ} {C : Set (Fin N → ℂ)} {y : Fin N → ℂ} (hloc : anrem_LocEq C y)
    {Q : Ideal (AnalyticGerm N)} (hQ : Q.IsPrime) (hI : adim2_ideal N (adim2_germ N C y) = Q)
    (hZ : adim2_germ N C y = adim2_zeroSet N Q) {e : ℕ}
    (he : ringKrullDim (AnalyticGerm N ⧸ Q) = (e : WithBot ℕ∞))
    (hpure : ∀ᶠ z in 𝓝 y, z ∈ C → adim2_dimension N (adim2_germ N C z) = (e : WithBot ℕ∞))
    (P : (Fin N → ℂ) →L[ℂ] (Fin mP → ℂ)) (m : ℕ)
    (hgen : ∀ U ∈ 𝓝 y, ∃ z ∈ C ∩ U,
      adim2_dimension N (adim2_germ N (C ∩ P ⁻¹' {P z}) z) ≤ (m : WithBot ℕ∞)) :
    ∃ h : (Fin N → ℂ) → ℂ, AnalyticAt ℂ h y ∧ ¬ (∀ᶠ z in 𝓝 y, z ∈ C → h z = 0) ∧
      ∀ᶠ z in 𝓝 y, z ∈ C → ((m + 1 : ℕ) : WithBot ℕ∞) ≤
        adim2_dimension N (adim2_germ N (C ∩ P ⁻¹' {P z}) z) → h z = 0 := by
  classical
  obtain ⟨D⟩ := ancrs_param_exists hQ hI hZ he
  -- points of small fibre dimension converging to `y`
  have hseq : ∀ j : ℕ, ∃ z ∈ C ∩ Metric.ball y (1 / ((j : ℝ) + 1)),
      adim2_dimension N (adim2_germ N (C ∩ P ⁻¹' {P z}) z) ≤ (m : WithBot ℕ∞) :=
    fun j ↦ hgen _ (Metric.ball_mem_nhds y (by positivity))
  choose zs hzs hzsd using hseq
  have hlocev := ancrs_locEq_nhds hloc
  obtain ⟨Uc, hUc, hUco, hyUc⟩ := eventually_nhds_iff.1 hlocev
  -- the slices
  have hS : ∀ j : ℕ, ∃ S : Set (Fin N → ℂ), (∀ w ∈ S, anrem_LocEq S w) ∧
      (∀ w ∈ S, ∀ Q ∈ (adim2_ideal N (adim2_germ N S w)).minimalPrimes,
        ringKrullDim (AnalyticGerm N ⧸ Q) ≤ (m : WithBot ℕ∞)) ∧
      (zs j ∈ Uc → ∃ ρ > 0, S = C ∩ P ⁻¹' {P (zs j)} ∩ Metric.ball (zs j) ρ) := by
    intro j
    by_cases hj : zs j ∈ Uc
    · have hl : ∀ᶠ z in 𝓝 (zs j), anrem_LocEq C z :=
        Filter.mem_of_superset (hUco.mem_nhds hj) fun z hz ↦ hUc z hz
      obtain ⟨ρ, hρ, h1, h2⟩ := ancrs_slice_ball hl P (hzsd j)
      exact ⟨_, h1, h2, fun _ ↦ ⟨ρ, hρ, rfl⟩⟩
    · exact ⟨∅, fun w hw ↦ hw.elim, fun w hw ↦ hw.elim, fun h ↦ (hj h).elim⟩
  choose S hS1 hS2 hS3 using hS
  obtain ⟨ξ, hξ⟩ := anr_slice S zs (fun _ ↦ m) (fun j w hw ↦ hS1 j w hw)
    (fun j w hw ↦ hS2 j w hw) m
  set L := anrem_appendL P ξ with hLdef
  have hLeq : ∀ z z', L z = L z' ↔ P z = P z' ∧ ξ z = ξ z' := by
    intro z z'
    simp only [hLdef, anrem_appendL_apply]
    exact ⟨anrem_append_inj, fun ⟨h1, h2⟩ ↦ by rw [h1, h2]⟩
  -- `L` is finite at the points `zs j` near `y`
  have hfinj : ∀ j, zs j ∈ Uc → ∀ᶠ z in 𝓝 (zs j), z ∈ C → L z = L (zs j) → z = zs j := by
    intro j hj
    obtain ⟨ρ, hρ, hSj⟩ := hS3 j hj
    have hmem : zs j ∈ S j ∩ {z | ξ z = ξ (zs j)} := by
      rw [hSj]; exact ⟨⟨⟨(hzs j).1, rfl⟩, Metric.mem_ball_self hρ⟩, rfl⟩
    have hiso := anr_isolated_of_dims _ _ hmem fun Q hQ ↦ by
      have := hξ j (zs j) hmem Q hQ
      simpa using this
    filter_upwards [hiso, Metric.ball_mem_nhds (zs j) hρ] with z hz hzb hzC hzL
    rw [hLeq] at hzL
    exact hz ⟨by rw [hSj]; exact ⟨⟨hzC, hzL.1⟩, hzb⟩, hzL.2⟩
  have hfin : ∀ U ∈ 𝓝 y, ∃ z₁ ∈ C ∩ U, ∀ᶠ z in 𝓝 z₁, z ∈ C → L z = L z₁ → z = z₁ := by
    intro U hU
    obtain ⟨ε, hε, hεU⟩ := Metric.mem_nhds_iff.1 (Filter.inter_mem hU (hUco.mem_nhds hyUc))
    obtain ⟨j, hj⟩ := exists_nat_one_div_lt hε
    have hzb : zs j ∈ Metric.ball y ε := Metric.ball_subset_ball hj.le (hzs j).2
    exact ⟨zs j, ⟨(hzs j).1, (hεU hzb).1⟩, hfinj j (hεU hzb).2⟩
  obtain ⟨s, hs⟩ := D.exists_cut_ne L hQ hI he hloc hpure hfin
  refine ⟨D.cut L s, D.cut_analyticAt L s, hs, ?_⟩
  -- the cut vanishes on the large fibres
  have hρev : ∀ᶠ z in 𝓝 y, ‖z - y‖ < D.ρ := by
    filter_upwards [Metric.ball_mem_nhds y D.ρ_pos] with z hz
    rwa [Metric.mem_ball, dist_eq_norm] at hz
  filter_upwards [hlocev, hρev] with z hzl hzρ hzC hzd
  set v := z - y with hvdef
  have hvC : y + v ∈ C := by simpa [v] using hzC
  by_cases hΔ : D.Δ (D.π v) = 0
  · simp only [ancrs_Param.cut, ← hvdef, hΔ, zero_mul]
  · have hni : ¬ ∀ᶠ z' in 𝓝 (y + v), z' ∈ C → L z' = L (y + v) → z' = y + v := by
      intro hiso
      have hyv : y + v = z := by simp [v]
      rw [hyv] at hiso
      have hX : anrem_LocEq (C ∩ P ⁻¹' {P z}) z := anrem_locEq_inter hzl (ancrs_locEq_level P _ z)
      have hzX : z ∈ C ∩ P ⁻¹' {P z} := ⟨hzC, rfl⟩
      have hle := anrem_dimension_le_of_isolated_linear hzX hX ξ (by
        filter_upwards [hiso] with z' hz' hz'X hz'ξ
        exact hz' hz'X.1 ((hLeq z' z).2 ⟨hz'X.2, hz'ξ⟩))
      have := hzd.trans hle
      have h' : ((m + 1 : ℕ) : WithBot ℕ∞) ≤ (m : WithBot ℕ∞) := this
      norm_cast at h'
      omega
    have := D.minor_eq_zero_of_not_isolated L hzρ hvC hΔ hni s
    simp only [ancrs_Param.cut, ← hvdef, this, mul_zero]

end Main

end HodgeLean.Foundations.Analytic
