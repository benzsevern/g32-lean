import HodgeLean.Foundations.Program.RelativeFrameFamilyFilled

noncomputable section
open Set Manifold Filter Topology
open scoped ContDiff
namespace HodgeLean.Foundations.Program
attribute [local instance] b4cov_sphChartedSpace b4cov_sph_isManifold

theorem rf7_power_chart_analytic {C : Type} [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (f : C → OnePoint ℂ) (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω f)
    (hnc : ∃ x y, f x ≠ f y) (b : Fin 10 → ℂ) (j : Fin 13) (n : ℕ) (hn : 0 < n)
    (u : OpenPartialHomeomorph C ℂ)
    (hpower : ∀ y ∈ u.source, f y = b6a_value b j (u y ^ n)) :
    u ∈ IsManifold.maximalAtlas 𝓘(ℂ, ℂ) ω C := by
  let D : TopologicalSpace.Opens C := ⟨u.source, u.open_source⟩
  let w : D → ℂ := fun y ↦ u y.val
  have hw : Continuous w := continuousOn_iff_continuous_domRestrict.mp u.continuousOn
  have hwi : Function.Injective w := fun y z h ↦ Subtype.ext (u.injOn y.2 z.2 h)
  have hzero : {y : D | w y = 0}.Finite :=
    Set.Finite.preimage hwi.injOn (Set.finite_singleton 0)
  have hfh : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (fun y : D ↦ f y.val) := hf.comp contMDiff_subtype_val
  have hpow : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (fun y : D ↦ w y ^ n) := by
    intro y
    let φ := extChartAt 𝓘(ℂ, ℂ) y
    let g : ℂ → OnePoint ℂ := fun z ↦ f (φ.symm z).val
    have hφ : ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω φ.symm (φ y) :=
      (contMDiffOn_extChartAt_symm y).contMDiffAt ((isOpen_extChartAt_target y).mem_nhds (mem_extChartAt_target y))
    have hG : ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω g (φ y) := by
      have hh := (hfh (φ.symm (φ y))).comp (φ y) hφ
      exact hh
    have hval : g (φ y) = b6a_value b j (w y ^ n) := by
      change f (φ.symm (φ y)).val = _
      rw [show φ.symm (φ y) = y from extChartAt_to_inv y]
      exact hpower y.val y.2
    have hh := b6a_valueCoord_comp_contDiffAt (fun _ : ℂ ↦ b) g (φ y) j (w y ^ n)
      contDiffAt_const hG hval
    have heq : (fun z : ℂ ↦ b6a_valueCoord j (b, g z)) = fun z ↦ w (φ.symm z) ^ n := by
      funext z
      change b6a_valueCoord j (b, f (φ.symm z).val) = _
      rw [hpower (φ.symm z).val (φ.symm z).2, b6a_valueCoord_value]
    rw [heq] at hh
    rw [contMDiffAt_iff]
    refine ⟨(hw.pow n).continuousAt, ?_⟩
    simpa only [φ, Function.comp_def, mfld_simps] using hh.contDiffWithinAt
  have hwHol := rf7_contMDiff_root_of_finite_zero w hw n hn hpow hzero
  have huHol : ContMDiffOn 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω u u.source := by
    intro y hy
    exact (contMDiffAt_subtype_iff.mp (hwHol ⟨y, hy⟩)).contMDiffWithinAt
  let W : TopologicalSpace.Opens ℂ := ⟨u.target, u.open_target⟩
  let inv : W → C := fun z ↦ u.symm z.val
  have hinv : Continuous inv := continuousOn_iff_continuous_domRestrict.mp u.continuousOn_symm
  have hinji : Function.Injective inv := fun z z' h ↦ Subtype.ext (u.symm.injOn z.2 z'.2 h)
  have hsource : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (fun z : W ↦ b6a_value b j (z.val ^ n)) :=
    by
      have hp : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, (Fin 10 → ℂ) × ℂ) ω (fun z : W ↦ (b, z.val)) :=
        ((contDiff_const.prodMk contDiff_id : ContDiff ℂ ω (fun z : ℂ ↦ (b, z))).contMDiff).comp contMDiff_subtype_val
      exact (b6a_value_power_contMDiff j n).comp hp
  have hinvP (z : W) : f (inv z) = b6a_value b j (z.val ^ n) := by
    have hh := hpower (u.symm z.val) (u.map_target z.2)
    rwa [u.right_inv z.2] at hh
  have hinvHol := b6m_contMDiff_of_injective_comp inv hinv hinji
    (fun z : W ↦ b6a_value b j (z.val ^ n)) f hsource hf hnc hinvP
  have huInvHol : ContMDiffOn 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω u.symm u.target := by
    intro z hz
    exact (contMDiffAt_subtype_iff.mp (hinvHol ⟨z, hz⟩)).contMDiffWithinAt
  exact u.mem_maximalAtlas_of_contMDiffOn huHol huInvHol

end HodgeLean.Foundations.Program
