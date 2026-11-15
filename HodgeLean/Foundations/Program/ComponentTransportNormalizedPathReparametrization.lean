import HodgeLean.Foundations.Program.ComponentTransportNormalizedPathProofs
import HodgeLean.Foundations.Program.ComponentTransportNormalizedPathClock

/-! # Every valid subdivision of a chosen path has controlled arcs -/
noncomputable section
open Set Topology
namespace HodgeLean.Foundations.Program

/-- A chart path with endpoint beyond the initial product has a representative whose every
valid uniform subdivision has its cell arcs in convex chart regions.
Source: `b65v_escape_avoidance`; `rtc_suffix_modulus`; the normalized-chart route in spec-chs. -/
theorem b65v_controlled_path {a b : b6_chart} (α : Path a b)
    (hb : ¬ ∀ i, dist (b.val i) (a.val i) ≤ b6t_radius a.val) :
    ∃ γ : Path a b, α.Homotopic γ ∧
      ∀ N : ℕ, 0 < N →
        (∀ k < N, b65y_sample
          ⟨fun t ↦ (γ t).val, continuous_subtype_val.comp γ.continuous⟩ N (k + 1) ∈
            b6t_polydisc (b65y_sample
              ⟨fun t ↦ (γ t).val, continuous_subtype_val.comp γ.continuous⟩ N k)) →
        ∀ k < N, ∃ V : Set (Fin 10 → ℂ), Convex ℝ V ∧ V ⊆ b6_chart ∧
          ∀ t : unitInterval, (k : ℝ) / N ≤ (t : ℝ) →
            (t : ℝ) ≤ ((k : ℝ) + 1) / N → (γ t).val ∈ V := by
  obtain ⟨V, hVo, hV, hVc, q, E, σ, hασ, hEV, _, hσout⟩ :=
    b65v_escape_avoidance α hb
  have hqV : q.val ∈ V := by simpa only [Path.target] using hEV 1
  obtain ⟨d, hd, hmargin⟩ := Metric.isOpen_iff.mp hVo q.val hqV
  let f : C(unitInterval, Fin 10 → ℂ) :=
    ⟨fun t ↦ (σ t).val, continuous_subtype_val.comp σ.continuous⟩
  obtain ⟨r, hr, hradius⟩ := b65v_uniform_radius f (fun t ↦ (σ t).property)
  obtain ⟨u, hu, hu2, hmod⟩ := rtc_suffix_modulus f (min r d) (lt_min hr hd)
  have hu1 : u < 1 := by linarith
  let γ : Path a b := (E.trans σ).reparam (rtc_escape_clock u)
    (rtc_escape_clock_continuous u hu hu1) (rtc_escape_clock_zero u hu)
    (rtc_escape_clock_one u hu1)
  let g : C(unitInterval, Fin 10 → ℂ) :=
    ⟨fun t ↦ (γ t).val, continuous_subtype_val.comp γ.continuous⟩
  have hfirst (t : unitInterval) (ht : (t : ℝ) ≤ u) :
      γ t = E (Set.projIcc 0 1 zero_le_one ((t : ℝ) / u)) :=
    rtc_escape_clock_first E σ u hu hu1 t ht
  have hlast (t : unitInterval) (ht : u ≤ (t : ℝ)) :
      γ t = σ (Set.projIcc 0 1 zero_le_one (((t : ℝ) - u) / (1 - u))) :=
    rtc_escape_clock_last E σ u hu hu1 t ht
  let t₁ : unitInterval := ⟨u, hu.le, hu1.le⟩
  have hγq : g t₁ = q.val := by
    change (γ t₁).val = q.val
    rw [hlast t₁ le_rfl]
    simp only [t₁, sub_self, zero_div, Set.projIcc_left]
    exact congrArg Subtype.val σ.source
  have hescape (t : unitInterval) (ht : (t₁ : ℝ) ≤ t) :
      g t ∉ b6t_polydisc (g 0) := by
    intro hmem
    apply hσout (Set.projIcc 0 1 zero_le_one (((t : ℝ) - u) / (1 - u)))
    intro i
    have hi := (Metric.mem_ball.mp (hmem i)).le
    change dist ((γ t).val i) ((γ 0).val i) ≤ b6t_radius (γ 0).val at hi
    rw [hlast t ht, Path.source] at hi
    exact hi
  have hlocal (s t : unitInterval) (hs : (t₁ : ℝ) ≤ s) (ht : (t₁ : ℝ) ≤ t)
      (hst : |(s : ℝ) - t| < (t₁ : ℝ)) : dist (g s) (g t) < min r d := by
    change dist (γ s).val (γ t).val < _
    rw [hlast s hs, hlast t ht]
    exact hmod s t hs ht hst
  have hrad (t : unitInterval) (ht : (t₁ : ℝ) ≤ t) : r ≤ b6t_radius (g t) := by
    change r ≤ b6t_radius (γ t).val
    rw [hlast t ht]
    exact hradius _
  refine ⟨γ, hασ.trans ⟨Path.Homotopy.reparam _ _ _ _ _⟩, fun N hN hsteps ↦ ?_⟩
  apply b65v_escape_cell_regions_modulus g (fun t ↦ (γ t).property) t₁ r d V hV hVc
    (fun t ht ↦ ?_) (by simpa only [hγq] using hmargin) hescape hlocal hrad N hN hsteps
  change (γ t).val ∈ V
  rw [hfirst t ht]
  exact hEV _

end HodgeLean.Foundations.Program
