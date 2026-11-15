import HodgeLean.Foundations.Program.RelativeFrameFamilyComponent
import HodgeLean.Foundations.Program.RelativeFrameFamilyRootDegree

noncomputable section
open Set Manifold Filter Topology
open scoped ContDiff
namespace HodgeLean.Foundations.Program
attribute [local instance] b4cov_sphChartedSpace b4cov_sph_isManifold

theorem rf7_base_root_of_covering {b : Fin 10 → ℂ} {G : Type} [Group G] [Finite G] {C : Type}
    [TopologicalSpace C] [ChartedSpace ℂ C] [IsManifold 𝓘(ℂ, ℂ) ω C] [T2Space C]
    [CompactSpace C] [ConnectedSpace C] [MulAction G C]
    [ChartedSpace ((Fin 10 → ℂ) × ℂ) (b6t_polydisc b × C)]
    (P : rf7_HurwitzAtlas b G C) (i : Fin 10) (x : C)
    (hx : P.f x = ((b i : ℂ) : OnePoint ℂ))
    (hcov : IsCoveringMapOn P.f
      (rf7_sphereBall (b i) (3 * b6t_radius b) \ {((b i : ℂ) : OnePoint ℂ)}))
 :
    ∃ u : OpenPartialHomeomorph C ℂ, u ∈ IsManifold.maximalAtlas 𝓘(ℂ, ℂ) ω C ∧
      u.source = rf7_component P.f (b i) (3 * b6t_radius b) x ∧
      u.target = {w : ℂ | ‖w‖ ^ P.n x < 3 * b6t_radius b} ∧ u x = 0 ∧
      ∀ y ∈ rf7_component P.f (b i) (3 * b6t_radius b) x,
        P.f y = ((b i + u y ^ P.n x : ℂ) : OnePoint ℂ) := by
  classical
  let c := b i
  let ρ := 3 * b6t_radius b
  have hr := (b6t_discs b P.hb).1
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  let S := rf7_sphereBall c ρ
  let T := S \ {(c : OnePoint ℂ)}
  have hS : IsOpen S := rf7_sphereBall_isOpen c ρ
  let U : TopologicalSpace.Opens C := ⟨P.f ⁻¹' S, hS.preimage P.hf.continuous⟩
  have hxS : P.f x ∈ S := by rw [hx]; exact ⟨c, Metric.mem_ball_self hρ, rfl⟩
  let x' : U := ⟨x, hxS⟩
  letI : LocallyPathConnectedSpace C := ChartedSpace.locallyPathConnectedSpace ℂ C
  letI : LocallyPathConnectedSpace U := U.isOpen.locallyPathConnectedSpace
  let D : TopologicalSpace.Opens U := ⟨connectedComponent x', isOpen_connectedComponent⟩
  let xD : D := ⟨x', mem_connectedComponent⟩
  letI : Nonempty D := ⟨xD⟩
  letI : ConnectedSpace D := isConnected_iff_connectedSpace.mp isConnected_connectedComponent
  let a : D → C := fun d ↦ d.val.val
  have ha : Continuous a := continuous_subtype_val.comp continuous_subtype_val
  have hai : Function.Injective a := Subtype.val_injective.comp Subtype.val_injective
  let Q : D → S := fun d ↦ ⟨P.f (a d), d.val.2⟩
  have hQ : Continuous Q := (P.hf.continuous.comp ha).subtype_mk _
  have hQcov : IsCoveringMapOn Q ((Subtype.val : S → OnePoint ℂ) ⁻¹' T) :=
    rf7_covering_on_component P.f P.hf.continuous P.hf.continuous.isClosedMap
      (rf7_atlas_finite_fibres P) S T hS hcov x hxS
  let E : Metric.ball c ρ ≃ₜ S :=
    OnePoint.isOpenEmbedding_coe.isEmbedding.homeomorphImage (Metric.ball c ρ)
  let p : D → Metric.ball c ρ := E.symm ∘ Q
  let q : D → ℂ := fun d ↦ (p d).val
  have hp : Continuous p := E.symm.continuous.comp hQ
  have hq : Continuous q := continuous_subtype_val.comp hp
  have hproj (d : D) : P.f (a d) = (q d : OnePoint ℂ) := by
    have hh := congrArg Subtype.val (E.apply_symm_apply (Q d))
    exact hh.symm
  have htarget : E ⁻¹' ((Subtype.val : S → OnePoint ℂ) ⁻¹' T) =
      (Subtype.val : Metric.ball c ρ → ℂ) ⁻¹' (Metric.ball c ρ \ {c}) := by
    ext z
    change ((E z).val ∈ S ∧ (E z).val ≠ (c : OnePoint ℂ)) ↔ z.val ∈ Metric.ball c ρ ∧ z.val ≠ c
    have he : (E z).val = (z.val : OnePoint ℂ) := rfl
    rw [he]
    exact ⟨fun h ↦ ⟨z.2, fun hz ↦ h.2 (congrArg (fun v : ℂ ↦ (v : OnePoint ℂ)) hz)⟩,
      fun h ↦ ⟨(E z).2, fun hz ↦ h.2 (OnePoint.coe_injective hz)⟩⟩
  have hpcov : IsCoveringMapOn p
      ((Subtype.val : Metric.ball c ρ → ℂ) ⁻¹' (Metric.ball c ρ \ {c})) := by
    rw [← htarget]
    exact hQcov.homeomorph_comp E.symm
  have hqcov : IsCoveringMapOn q (Metric.ball c ρ \ {c}) :=
    rf7_covering_comp_subtype (Metric.ball c ρ) (Metric.ball c ρ \ {c})
      (Metric.isOpen_ball.sdiff isClosed_singleton) Set.sdiff_subset p hp hpcov
  have hQclosed : IsClosedMap Q :=
    (P.hf.continuous.isClosedMap.restrictPreimage S).comp
      (isClosed_connectedComponent (x := x')).isClosedEmbedding_subtypeVal.isClosedMap
  have hpclosed : IsClosedMap p := E.symm.isClosedMap.comp hQclosed
  have hadcomp (d : D) : a d ∈ rf7_component P.f (b i) (3 * b6t_radius b) x := by
    rw [rf7_component, connectedComponentIn_eq_image (show x ∈ P.f ⁻¹' S from hxS)]
    exact ⟨d.val, d.2, rfl⟩
  have hsingle (d : D) (hd : q d = c) : d = xD := by
    apply hai
    exact rf7_component_unique_centre P i x hx hcov (a d) (hadcomp d)
      ((hproj d).trans (congrArg (fun w : ℂ ↦ (w : OnePoint ℂ)) hd))
  let t : b6t_polydisc b := ⟨b, (b6t_polydisc_neighbourhood b P.hb).1⟩
  let s := b6a_sliceChart b C P.A P.hparam t x
  have haopen : IsOpenEmbedding a :=
    U.isOpen.isOpenEmbedding_subtypeVal.comp D.isOpen.isOpenEmbedding_subtypeVal
  let e : OpenPartialHomeomorph D ℂ := (haopen.toOpenPartialHomeomorph a).trans s
  have hj : P.f x = b6_branch b (Fin.castAdd 3 i) := by simpa [b6_branch] using hx
  have hmark := P.hmark (t, x) (Fin.castAdd 3 i) hj
  have hxe : xD ∈ e.source := by
    change xD ∈ Set.univ ∧ (t, a xD) ∈ (P.A (t, x)).source
    exact ⟨trivial, (P.hA (t, x)).1⟩
  have he0 : e xD = 0 := by
    change (P.A (t, x) (t, x)).2 = 0
    exact hmark.1
  have hpower (d : D) (hd : d ∈ e.source) : q d = c + e d ^ P.n x := by
    have hd' : (t, a d) ∈ (P.A (t, x)).source := hd.2
    apply OnePoint.coe_injective
    rw [← hproj]
    change P.f (a d) = ((b i + (P.A (t, x) (t, a d)).2 ^ P.n x : ℂ) : OnePoint ℂ)
    have h := hmark.2 (t, a d) hd'
    change b6t_sphere b b (P.f (a d)) =
      b6a_value b (Fin.castAdd 3 i) ((P.A (t, x) (t, a d)).2 ^ P.n x) at h
    rw [b6t_identity] at h
    simpa [b6a_value] using h
  have hdegree := rf7_degree_of_local_power c ρ hρ p hpclosed xD
    (OnePoint.coe_injective ((hproj xD).symm.trans hx)) hsingle e hxe he0 (P.n x) (P.hn x) hpower hqcov
  have hqfin (z : ℂ) : (q ⁻¹' {z}).Finite := by
    have hh : (a ⁻¹' (P.f ⁻¹' {(z : OnePoint ℂ)})).Finite :=
      Set.Finite.preimage hai.injOn (rf7_atlas_finite_fibres P (z : OnePoint ℂ))
    apply hh.subset
    intro d hd
    change P.f (a d) = (z : OnePoint ℂ)
    rw [hproj, show q d = z from hd]
  have hpproper : IsProperMap p := by
    apply isProperMap_iff_isClosedMap_and_compact_fibers.mpr
    refine ⟨hp, hpclosed, fun z ↦ ?_⟩
    apply Set.Finite.isCompact
    apply (hqfin z.val).subset
    intro d hd
    exact congrArg Subtype.val hd
  haveI : ∀ d : D, (𝓝[≠] d).NeBot := rf7_punctured_nhds_neBot
  obtain ⟨d₀, hd₀⟩ := (dense_univ.sdiff_finite (hqfin c)).nonempty
  have hnz : ∃ d : D, q d ≠ c := ⟨d₀, hd₀.2⟩
  obtain ⟨k, hk, v, hv, hvR, hvP⟩ := rf7_disc_cover_coordinate q hq c ρ hρ
    (fun d ↦ (p d).2) hqfin hnz hqcov
  have hk_eq : k = P.n x :=
    (rf7_degree_of_punctured_coordinate q hq c ρ k hk v hv.injective hvR hvP
      (q d₀) (p d₀).2 hd₀.2).symm.trans (hdegree (q d₀) ⟨(p d₀).2, hd₀.2⟩)
  rw [hk_eq] at hvR hvP
  letI : Nonempty (rf7_nonzeroLocus q hq c) := ⟨⟨d₀, hd₀.2⟩⟩
  have hqx : q xD = c := OnePoint.coe_injective ((hproj xD).symm.trans hx)
  obtain ⟨uD, huDS, huDT, huDx, huDP⟩ := rf7_fill_disc_coordinate q hq c ρ hρ p hpproper
    (fun _ ↦ rfl) xD hqx hsingle (P.n x) (P.hn x) v hv hvR hvP
  have haHol : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω a :=
    contMDiff_subtype_val.comp contMDiff_subtype_val
  have hfaHol := P.hf.comp haHol
  have hchart : b4cov_chart0 ∈ IsManifold.maximalAtlas 𝓘(ℂ, ℂ) ω (OnePoint ℂ) := by
    rw [← b4cov_chartAt_coe c]
    exact IsManifold.chart_mem_maximalAtlas _
  have hqHol : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω q := by
    intro d
    have hdsrc : P.f (a d) ∈ b4cov_chart0.source := by
      rw [hproj, b4cov_chart0_source]
      exact ⟨q d, rfl⟩
    have hh := ((contMDiffOn_of_mem_maximalAtlas hchart).contMDiffAt
      (b4cov_chart0.open_source.mem_nhds hdsrc)).comp d (hfaHol d)
    have heq : (fun d : D ↦ b4cov_chart0 (P.f (a d))) = q := by
      funext d
      rw [hproj, b4cov_chart0_coe]
    change ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (fun d : D ↦ b4cov_chart0 (P.f (a d))) d at hh
    rw [heq] at hh
    exact hh
  have huDcont : Continuous uD := by
    rw [← continuousOn_univ, ← huDS]
    exact uD.continuousOn
  have huDzero : {d : D | uD d = 0}.Finite := by
    apply (Set.finite_singleton xD).subset
    intro d hd
    apply hsingle
    rw [huDP d, hd, zero_pow (P.hn x).ne', add_zero]
  have huDpow : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (fun d : D ↦ uD d ^ P.n x) := by
    have heq : (fun d : D ↦ uD d ^ P.n x) = fun d ↦ q d - c := by
      funext d
      rw [huDP d]
      ring
    rw [heq]
    exact hqHol.sub contMDiff_const
  have huDHol := rf7_contMDiff_root_of_finite_zero uD huDcont (P.n x) (P.hn x) huDpow huDzero
  let aE := haopen.toOpenPartialHomeomorph a
  let u : OpenPartialHomeomorph C ℂ := aE.symm.trans uD
  have haR : range a = rf7_component P.f (b i) (3 * b6t_radius b) x := by
    rw [rf7_component, connectedComponentIn_eq_image (show x ∈ P.f ⁻¹' S from hxS)]
    ext y
    exact ⟨fun ⟨d, hd⟩ ↦ ⟨d.val, d.2, hd⟩, fun ⟨d, hd, hy⟩ ↦ ⟨⟨d, hd⟩, hy⟩⟩
  have huS : u.source = rf7_component P.f (b i) (3 * b6t_radius b) x := by
    change aE.target ∩ aE.symm ⁻¹' uD.source = _
    rw [huDS, Set.preimage_univ, Set.inter_univ]
    simpa only [aE, IsOpenEmbedding.toOpenPartialHomeomorph_target] using haR
  have huT : u.target = {z : ℂ | ‖z‖ ^ P.n x < 3 * b6t_radius b} := by
    change uD.target ∩ uD.symm ⁻¹' aE.source = _
    change uD.target ∩ uD.symm ⁻¹' Set.univ = _
    rw [Set.preimage_univ, Set.inter_univ, huDT]
  have hua (d : D) : u (a d) = uD d := by
    change uD (aE.symm (a d)) = uD d
    rw [haopen.toOpenPartialHomeomorph_left_inv]
  have hux : u x = 0 := by
    change u (a xD) = 0
    rw [hua, huDx]
  have huP (y : C) (hy : y ∈ rf7_component P.f (b i) (3 * b6t_radius b) x) :
      P.f y = ((b i + u y ^ P.n x : ℂ) : OnePoint ℂ) := by
    rw [← haR] at hy
    obtain ⟨d, rfl⟩ := hy
    rw [hproj, hua, huDP d]
  have huHol : ContMDiffOn 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω u u.source := by
    have hcomp : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (fun d : D ↦ u (a d)) := by
      have heq : (fun d : D ↦ u (a d)) = uD := funext hua
      rw [heq]
      exact huDHol
    intro y hy
    rw [huS, ← haR] at hy
    obtain ⟨d, rfl⟩ := hy
    have hh : ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (fun v : U ↦ u v.val) d.val :=
      contMDiffAt_subtype_iff.mp (hcomp d)
    exact (contMDiffAt_subtype_iff.mp hh).contMDiffWithinAt
  let W : TopologicalSpace.Opens ℂ := ⟨u.target, u.open_target⟩
  let inv : W → C := fun z ↦ u.symm z.val
  have hinv : Continuous inv := continuousOn_iff_continuous_domRestrict.mp u.continuousOn_symm
  have hinji : Function.Injective inv := fun z z' h ↦ Subtype.ext (u.symm.injOn z.2 z'.2 h)
  have hpowerHol : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω
      (fun z : W ↦ ((c + z.val ^ P.n x : ℂ) : OnePoint ℂ)) :=
    b4cov_coe_contMDiff.comp ((contDiff_const.add (contDiff_id.pow (P.n x))).contMDiff.comp contMDiff_subtype_val)
  have hinvP (z : W) : P.f (inv z) = ((c + z.val ^ P.n x : ℂ) : OnePoint ℂ) := by
    have hh := huP (u.symm z.val) (huS ▸ u.map_target z.2)
    rw [u.right_inv z.2] at hh
    exact hh
  obtain ⟨x₀, hx₀⟩ := P.hsurj ((0 : ℂ) : OnePoint ℂ)
  obtain ⟨x₁, hx₁⟩ := P.hsurj OnePoint.infty
  have hnc : ∃ y z, P.f y ≠ P.f z :=
    ⟨x₀, x₁, by rw [hx₀, hx₁]; exact OnePoint.coe_ne_infty 0⟩
  have hinvHol := b6m_contMDiff_of_injective_comp inv hinv hinji
    (fun z : W ↦ ((c + z.val ^ P.n x : ℂ) : OnePoint ℂ)) P.f hpowerHol P.hf hnc hinvP
  have huInvHol : ContMDiffOn 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω u.symm u.target := by
    intro z hz
    exact (contMDiffAt_subtype_iff.mp (hinvHol ⟨z, hz⟩)).contMDiffWithinAt
  exact ⟨u, u.mem_maximalAtlas_of_contMDiffOn huHol huInvHol, huS, huT, hux, huP⟩

end HodgeLean.Foundations.Program
