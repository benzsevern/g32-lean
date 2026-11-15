import HodgeLean.Foundations.Program.PeriodFunctionIntegratedProofs

/-! # Period function on the shared marked-root family
Implication from retained geometry and H7 to analytic period coordinates, and from an explicit
fibre comparison and later stage inputs to a period map for the selected Prym family.
HC no distance; AV milestone no distance.
-/
noncomputable section
open Set Manifold Filter Topology HodgeLean.Papers
open scoped ContDiff TensorProduct
namespace HodgeLean.Foundations.Program
attribute [local instance] b64c_RootFamily.topC b64c_RootFamily.chartC b64c_RootFamily.manC
  b64c_RootFamily.t2C b64c_RootFamily.compactC b64c_RootFamily.connectedC
  b64c_RootFamily.actionC b64c_RootFamily.totalChart b64c_RootFamily.totalMan
  b64c_RootFamily.fibreChart b64c_RootFamily.fibreMan b64c_RootFamily.fibreT2
  b64c_RootFamily.fibreCompact b64c_RootFamily.fibreConnected b64c_RootFamily.fibreFaithful

attribute [local instance] b4cov_sphChartedSpace b4cov_sph_isManifold
attribute [local instance] rf8_SharedFamily.topC rf8_SharedFamily.chartC
  rf8_SharedFamily.manC rf8_SharedFamily.t2C rf8_SharedFamily.compactC
  rf8_SharedFamily.connectedC rf8_SharedFamily.actionC rf8_SharedFamily.totalChart
  rf8_SharedFamily.totalMan rf8_SharedFamily.fibreChart rf8_SharedFamily.fibreMan
  rf8_SharedFamily.fibreT2 rf8_SharedFamily.fibreCompact rf8_SharedFamily.fibreConnected
  rf8_SharedFamily.fibreFaithful

/-- The period-family projection retains the same surface, map and integral data.
Source: `b64i_rootFamily`; shared-family integration review. -/
theorem b64i_projection (R : rf8_SharedFamily) :
    (b64i_rootFamily R).C = R.C ∧ (b64i_rootFamily R).f = R.atlas.f ∧
      (b64i_rootFamily R).P = R.P ∧ (b64i_rootFamily R).Q = R.Q ∧
      (b64i_rootFamily R).A = R.A :=
  b64i_projection_aux R

example := @b64i_projection

/-- Transport uses the identical retained period comparison.
Source: `b64c_transportedFamily`, `rf8_transportedFamily`. -/
theorem b64i_transport (R : rf8_SharedFamily) (s : b6t_polydisc mr_base) :
    b64c_transportedFamily mr_base (b64i_rootFamily R).C (b64i_rootFamily R).hC
      (b6t_polydisc mr_base) (Subset.refl _) (b64i_rootFamily R).P s =
        rf8_transportedFamily R s :=
  b64i_transport_aux R s

example := @b64i_transport

/-- Analyticity on the shared family with H7 as the remaining marking input.
Source: `rf8_root_filtration_frame`, `b63d_lattice_rank`,
`b64c_geomPeriod_analytic_of_frames`; Griffiths, Periods I, §1. -/
theorem b64i_analytic (R : rf8_SharedFamily) (s : b6t_polydisc mr_base)
    (m : (ℚ ⊗[ℤ] b63l_parameterLattice mr_base R.C R.hC (b6t_polydisc mr_base)
      (Subset.refl _) s) ≃ₗ[ℚ] (ℚ ⊗[ℤ] b60_Lattice))
    (hJ : ∀ x, m ((R.A s).baseChange ℚ x) = b60_omega.baseChange ℚ (m x))
    (hpol : ∀ x y, b60_E.baseChange ℚ (m x) (m y) =
      (b63e_singularQ mr_base R.C R.hC (b6t_polydisc mr_base) (Subset.refl _)
        s (R.P s) (R.Q s)).baseChange ℚ x y) :
    AnalyticOnNhd ℂ (b64i_period R s m) (b6t_polydisc mr_base) :=
  b64i_analytic_aux R s m hJ hpol

example := @b64i_analytic

/-- The period coordinate represents the shared transported filtration in the domain.
Source: `b64c_geomPeriod_chart`, `b64i_transport`. -/
theorem b64i_chart (R : rf8_SharedFamily) (s : b6t_polydisc mr_base)
    (m : (ℚ ⊗[ℤ] b63l_parameterLattice mr_base R.C R.hC (b6t_polydisc mr_base)
      (Subset.refl _) s) ≃ₗ[ℚ] (ℚ ⊗[ℤ] b60_Lattice))
    (hJ : ∀ x, m ((R.A s).baseChange ℚ x) = b60_omega.baseChange ℚ (m x))
    (hpol : ∀ x y, b60_E.baseChange ℚ (m x) (m y) =
      (b63e_singularQ mr_base R.C R.hC (b6t_polydisc mr_base) (Subset.refl _)
        s (R.P s) (R.Q s)).baseChange ℚ x y) :
    ∀ t ∈ b6t_polydisc mr_base, b64i_period R s m t ∈ g32m_Domain ∧
      b60_F (b64i_period R s m t) = b64c_markedF _ m (rf8_transportedFamily R s) t :=
  b64i_chart_aux R s m hJ hpol

example := @b64i_chart

/-- Chain to the selected Prym family through an explicit comparison of geometric fibres.
The comparison and later isogeny, curve, jet and codifferential stages remain inputs.
Source: `g32r_PeriodMap`; `b63gP_IsMarked`, F-2217; `b63g5_fiber`. -/
theorem b64i_periodMap (R : rf8_SharedFamily) (s : b6t_polydisc mr_base)
    (m : (ℚ ⊗[ℤ] b63l_parameterLattice mr_base R.C R.hC (b6t_polydisc mr_base)
      (Subset.refl _) s) ≃ₗ[ℚ] (ℚ ⊗[ℤ] b60_Lattice))
    (hJ : ∀ x, m ((R.A s).baseChange ℚ x) = b60_omega.baseChange ℚ (m x))
    (hpol : ∀ x y, b60_E.baseChange ℚ (m x) (m y) =
      (b63e_singularQ mr_base R.C R.hC (b6t_polydisc mr_base) (Subset.refl _)
        s (R.P s) (R.Q s)).baseChange ℚ x y)
    (B : Module.Basis (Fin 12) ℤ (b63l_parameterLattice mr_base R.C R.hC
      (b6t_polydisc mr_base) (Subset.refl _) s))
    (Fm : g32m_UniversalFamily)
    (j : b6t_polydisc mr_base ≃ b63gP_family.S)
    (hcompare : ∀ t, b63gP_family.fiber (j t) = b63g5_fiber mr_base R.C R.hC (b6t_polydisc mr_base) (Subset.refl _)
        R.hG mr_base_mem_chart R.atlas.f R.atlas.hf R.atlas.hsurj R.hk
        R.Q₀ R.hQ₀ R.Q R.hQ R.P R.hP s B t)
    (hisog : ∀ (t : b6t_polydisc mr_base)
      (hm : b64i_period R s m t.val ∈ g32m_Domain),
      g32t_KIsog (b63g5_fiber mr_base R.C R.hC (b6t_polydisc mr_base) (Subset.refl _)
        R.hG mr_base_mem_chart R.atlas.f R.atlas.hf R.atlas.hsurj R.hk
        R.Q₀ R.hQ₀ R.Q R.hQ R.P R.hP s B t) (Fm.univ ⟨b64i_period R s m t.val, hm⟩))
    (curve : ℂ → Fin 10 → ℂ) (curve_cont : ContinuousAt curve 0)
    (curve_zero : curve 0 ∈ b6t_polydisc mr_base)
    (jet : ℂ → Matrix (Fin 9) (Fin 10) ℂ) (jet_certified : g32r_CertifiedJet jet)
    (codiff : ∀ᶠ θ in 𝓝 (0 : ℂ), ∃ L : Matrix (Fin 9) (Fin 9) ℂ,
      ∃ T : Matrix (Fin 10) (Fin 10) ℂ, IsUnit L ∧ IsUnit T ∧
        jet θ = L * LinearMap.toMatrix'
          (fderiv ℂ (b64i_period R s m) (curve θ) :
            (Fin 10 → ℂ) →ₗ[ℂ] Fin 9 → ℂ) * T) :
    ∃ F : g32r_PeriodMap Fm b63gP_family,
      F.V = b6t_polydisc mr_base ∧ F.period = b64i_period R s m :=
  b64i_periodMap_aux R s m hJ hpol B Fm j hcompare hisog curve curve_cont curve_zero jet jet_certified codiff

example := @b64i_periodMap

/-- The retained shared package has a checked geometric inhabitant on this base.
No new statement is used to select it. -/
example : Nonempty rf8_SharedFamily := by
  obtain ⟨R, _⟩ := rf8_shared_root
  exact ⟨R⟩

/-- The marked polydisc contains a genuinely displaced moving branch value. -/
example : ∃ t ∈ b6t_polydisc mr_base, t 0 - mr_base 0 ≠ 0 ∧
    ‖t 0 - mr_base 0‖ < rf7_radius mr_base := by
  have hr : 0 < b6t_radius mr_base := (b6t_discs mr_base mr_base_mem_chart).1
  refine ⟨Function.update mr_base 0 (mr_base 0 + (b6t_radius mr_base / 2 : ℝ)), ?_, ?_, ?_⟩
  · intro i
    rw [Metric.mem_ball]
    by_cases h : i = 0
    · subst h
      simp only [Function.update_self, dist_self_add_left, Complex.norm_real,
        Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ b6t_radius mr_base / 2)]
      linarith
    · simp [Function.update_of_ne h, hr]
  · simp only [Function.update_self, add_sub_cancel_left]
    exact_mod_cast (by positivity : (b6t_radius mr_base / 2 : ℝ) ≠ 0)
  · simp only [Function.update_self, add_sub_cancel_left, Complex.norm_real,
      Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ b6t_radius mr_base / 2), rf7_radius]
    linarith

/-- Every retained fibre has a rank-twelve lattice; no open statement is used here. -/
example (R : rf8_SharedFamily) (s : b6t_polydisc mr_base) :
    Nonempty (Module.Basis (Fin 12) ℤ
      (b63l_parameterLattice mr_base R.C R.hC (b6t_polydisc mr_base) (Subset.refl _) s)) :=
  (b63d_lattice_rank mr_base R.C R.hC (b6t_polydisc mr_base) (Subset.refl _) s
    (R.hG s) mr_base_mem_chart R.atlas.f (R.hk s) (R.hsurj s) (R.hgal s)
    (R.hbranch s) (R.hrot s)).1

/-- Filtration rank six on the retained structures, using the checked period transport.
This specializes the proof of `b64c_transported_finrank` on `origin/main` to this datum. -/
example (R : rf8_SharedFamily) (s t : b6t_polydisc mr_base) :
    Module.finrank ℂ (b63e_transportedF mr_base R.C R.hC (b6t_polydisc mr_base)
      (Subset.refl _) R.P s t) = 6 := by
  obtain ⟨E, -, hE⟩ := b63e_lattice_period_transport mr_base R.C R.hC
    (b6t_polydisc mr_base) (Subset.refl _) R.hG R.P R.hP s t
  have hd := (b63d_dim_eq mr_base R.C R.hC (b6t_polydisc mr_base) (Subset.refl _)
    t (R.hG t) mr_base_mem_chart R.atlas.f (R.hk t) (R.hsurj t) (R.hgal t)
    (R.hbranch t) (R.hrot t)).2.2
  let eC := E.baseChange ℤ ℂ
    (b63l_parameterLattice mr_base R.C R.hC (b6t_polydisc mr_base) (Subset.refl _) s)
    (b63l_periodLattice (rf8_fibre R.C t))
  rw [hE]
  change Module.finrank ℂ ↥((b63l_periodF _).comap eC.toLinearMap) = 6
  exact (Submodule.comap_equiv_self_of_inj_of_le (p := b63l_periodF _)
    eC.injective (by rw [LinearMap.range_eq_top.mpr eC.surjective]; exact le_top)).finrank_eq.trans hd


end HodgeLean.Foundations.Program
