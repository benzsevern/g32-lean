import HodgeLean.Foundations.Program.PeriodFunctionIntegratedDefs

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

theorem b64i_projection_aux (R : rf8_SharedFamily) :
    (b64i_rootFamily R).C = R.C ∧ (b64i_rootFamily R).f = R.atlas.f ∧
      (b64i_rootFamily R).P = R.P ∧ (b64i_rootFamily R).Q = R.Q ∧
      (b64i_rootFamily R).A = R.A := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem b64i_transport_aux (R : rf8_SharedFamily) (s : b6t_polydisc mr_base) :
    b64c_transportedFamily mr_base (b64i_rootFamily R).C (b64i_rootFamily R).hC
      (b6t_polydisc mr_base) (Subset.refl _) (b64i_rootFamily R).P s =
        rf8_transportedFamily R s := by
  rfl

theorem b64i_analytic_aux (R : rf8_SharedFamily) (s : b6t_polydisc mr_base)
    (m : (ℚ ⊗[ℤ] b63l_parameterLattice mr_base R.C R.hC (b6t_polydisc mr_base)
      (Subset.refl _) s) ≃ₗ[ℚ] (ℚ ⊗[ℤ] b60_Lattice))
    (hJ : ∀ x, m ((R.A s).baseChange ℚ x) = b60_omega.baseChange ℚ (m x))
    (hpol : ∀ x y, b60_E.baseChange ℚ (m x) (m y) =
      (b63e_singularQ mr_base R.C R.hC (b6t_polydisc mr_base) (Subset.refl _)
        s (R.P s) (R.Q s)).baseChange ℚ x y) :
    AnalyticOnNhd ℂ (b64i_period R s m) (b6t_polydisc mr_base) := by
  obtain ⟨B⟩ := (b63d_lattice_rank mr_base R.C R.hC (b6t_polydisc mr_base)
    (Subset.refl _) s (R.hG s) mr_base_mem_chart R.atlas.f (R.hk s)
    (R.hsurj s) (R.hgal s) (R.hbranch s) (R.hrot s)).1
  apply b64c_geomPeriod_analytic_of_frames mr_base R.C R.hC
    (b6t_polydisc mr_base) (Subset.refl _) (rf5_polydisc_isOpen mr_base)
    R.hG mr_base_mem_chart R.atlas.f R.atlas.hf R.atlas.hsurj R.hk R.hsurj
    R.hgal R.hbranch R.hrot R.Q₀ R.hQ₀ R.Q R.hQ R.P R.hP s
    (R.A s) (R.hA s) m hJ hpol B
  intro t₀ ht₀
  obtain ⟨W, hWo, htW, hWV, c, hc, hspan⟩ :=
    rf8_root_filtration_frame R s B ⟨t₀, ht₀⟩
  refine ⟨W, hWo, htW, hWV, 6, c, hc, ?_⟩
  intro t ht
  simpa only [b64c_transportedFamily, dite_eq_left (hWV ht)] using
    (hspan ⟨t, hWV ht⟩ ht).2

theorem b64i_chart_aux (R : rf8_SharedFamily) (s : b6t_polydisc mr_base)
    (m : (ℚ ⊗[ℤ] b63l_parameterLattice mr_base R.C R.hC (b6t_polydisc mr_base)
      (Subset.refl _) s) ≃ₗ[ℚ] (ℚ ⊗[ℤ] b60_Lattice))
    (hJ : ∀ x, m ((R.A s).baseChange ℚ x) = b60_omega.baseChange ℚ (m x))
    (hpol : ∀ x y, b60_E.baseChange ℚ (m x) (m y) =
      (b63e_singularQ mr_base R.C R.hC (b6t_polydisc mr_base) (Subset.refl _)
        s (R.P s) (R.Q s)).baseChange ℚ x y) :
    ∀ t ∈ b6t_polydisc mr_base, b64i_period R s m t ∈ g32m_Domain ∧
      b60_F (b64i_period R s m t) = b64c_markedF _ m (rf8_transportedFamily R s) t := by
  exact b64c_geomPeriod_chart mr_base R.C R.hC (b6t_polydisc mr_base)
    (Subset.refl _) R.hG mr_base_mem_chart R.atlas.f R.atlas.hf R.atlas.hsurj
    R.hk R.hsurj R.hgal R.hbranch R.hrot R.Q₀ R.hQ₀ R.Q R.hQ R.P R.hP
    s (R.A s) (R.hA s) m hJ hpol

theorem b64i_periodMap_aux (R : rf8_SharedFamily) (s : b6t_polydisc mr_base)
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
      F.V = b6t_polydisc mr_base ∧ F.period = b64i_period R s m := by
  refine ⟨{
    V := b6t_polydisc mr_base
    isOpen_V := rf5_polydisc_isOpen mr_base
    period := b64i_period R s m
    analytic := b64i_analytic_aux R s m hJ hpol
    mapsTo := fun t ht ↦ (b64i_chart_aux R s m hJ hpol t ht).1
    isog := ?_
    curve := curve
    curve_cont := curve_cont
    curve_zero := curve_zero
    jet := jet
    jet_certified := jet_certified
    codiff := codiff }, rfl, rfl⟩
  intro t ht
  refine ⟨j ⟨t, ht⟩, ?_⟩
  rw [hcompare]
  exact hisog ⟨t, ht⟩ _

end HodgeLean.Foundations.Program
