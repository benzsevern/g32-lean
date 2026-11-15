import HodgeLean.Foundations.Program.RelativeFrameFamilyOuterCover
import HodgeLean.Foundations.Program.RelativeFrameFamilyOuterCharts
import HodgeLean.Foundations.Program.RelativeFrameFamilyAnnulus

noncomputable section
open Set Metric Manifold Filter Topology
open scoped ContDiff
namespace HodgeLean.Foundations.Program
attribute [local instance] b4cov_sphChartedSpace b4cov_sph_isManifold

/-- Assemble stationary outer charts and the annulus charts of all marked centres.
Source: `rf7_pieceCover_of_compact_closure`, `rf7_annulus_chart`, `rf7_outer_chart_at`. -/
theorem rf7_outer_data_of_coverings {b : Fin 10 → ℂ} {G : Type} [Group G] [Finite G] {C : Type}
    [TopologicalSpace C] [ChartedSpace ℂ C] [IsManifold 𝓘(ℂ, ℂ) ω C] [T2Space C]
    [CompactSpace C] [ConnectedSpace C] [MulAction G C]
    [ChartedSpace ((Fin 10 → ℂ) × ℂ) (b6t_polydisc b × C)]
    (P : rf7_HurwitzAtlas b G C)
    (hcov : ∀ i : Fin 10, IsCoveringMapOn P.f
      (rf7_sphereBall (b i) (3 * b6t_radius b) \ {((b i : ℂ) : OnePoint ℂ)})) :
    ∃ (D : rf4_OuterData C (rf7_outer b P.f))
      (e : Fin D.m ≃ {x : C // ∃ i : Fin 10, P.f x = ((b i : ℂ) : OnePoint ℂ)})
      (idx : Fin D.m → Fin 10),
      D.r = rf7_radius b ∧
      (∀ k, P.f (e k).val = ((b (idx k) : ℂ) : OnePoint ℂ) ∧ D.c k = b (idx k) ∧
        D.deg k = P.n (e k).val) ∧
      (∀ k, (D.P.chart (D.ann k)).source ⊆
          rf7_component P.f (b (idx k)) (3 * b6t_radius b) (e k).val ∧
        ∀ y ∈ (D.P.chart (D.ann k)).source,
          P.f y = ((D.c k + D.P.chart (D.ann k) y ^ D.deg k : ℂ) : OnePoint ℂ)) ∧
      (∀ j, (D.P.chart j).source ⊆ P.f ⁻¹'
        {p | ∀ i, p ∉ ((↑) : ℂ → OnePoint ℂ) '' Metric.closedBall (b i) (b6t_radius b)}) ∧
      ∀ j, ContMDiffOn 𝓘(ℂ, (Fin 10 → ℂ) × ℂ) 𝓘(ℂ, ℂ) ω
        (fun q : b6t_polydisc b × C ↦ D.P.chart j q.2) {q | q.2 ∈ (D.P.chart j).source} := by
  classical
  let Z := {x : C // ∃ i : Fin 10, P.f x = ((b i : ℂ) : OnePoint ℂ)}
  have hfin : {x : C | ∃ i : Fin 10, P.f x = ((b i : ℂ) : OnePoint ℂ)}.Finite := by
    have hh := Set.finite_iUnion (fun i : Fin 10 ↦ rf7_atlas_finite_fibres P ((b i : ℂ) : OnePoint ℂ))
    convert hh using 1
    ext x
    simp
  letI : Fintype Z := hfin.fintype
  let m := Fintype.card Z
  let e : Fin m ≃ Z := (Fintype.equivFin Z).symm
  choose idx hidx using fun k : Fin m ↦ (e k).property
  have hcharts (k : Fin m) : ∃ a : OpenPartialHomeomorph C ℂ,
      a ∈ IsManifold.maximalAtlas 𝓘(ℂ, ℂ) ω C ∧
      a.source ⊆ rf7_component P.f (b (idx k)) (3 * b6t_radius b) (e k).val ∧
      (∀ y ∈ a.source, P.f y = ((b (idx k) + a y ^ P.n (e k).val : ℂ) : OnePoint ℂ)) ∧
      a.source ⊆ P.f ⁻¹' b6a_stationaryOpen b ∧
      closure (b63r_annulus (P.n (e k).val) (rf7_radius b)) ⊆ a.target ∧
      a.symm '' b63r_annulus (P.n (e k).val) (rf7_radius b) ⊆ rf7_outer b P.f ∧
      ContMDiffOn 𝓘(ℂ, (Fin 10 → ℂ) × ℂ) 𝓘(ℂ, ℂ) ω
        (fun q : b6t_polydisc b × C ↦ a q.2) (univ ×ˢ a.source) := by
    obtain ⟨u, hu, hus, hut, -, hp⟩ := rf7_base_root_of_covering P (idx k) (e k).val (hidx k) (hcov (idx k))
    exact rf7_annulus_chart P (idx k) (e k).val u hus
      (by simpa only [norm_pow] using hut) hu (fun y hy ↦ hp y (hus ▸ hy))
  choose a ha has hap hast hat hao hah using hcharts
  choose A hAp hAa hAs hAh using rf7_outer_chart_at P
  obtain ⟨Q, hQ⟩ := rf7_pieceCover_of_compact_closure (rf7_outer b P.f)
    (rf7_outer_open P.f P.hf.continuous) (isClosed_closure.isCompact)
    A (fun p ↦ ⟨hAp p, hAa p⟩)
  let V : Fin m → Set ℂ := fun k ↦ b63r_annulus (P.n (e k).val) (rf7_radius b)
  have hVc (k) : IsCompact (closure (V k)) :=
    (rf4_closedAnnulus_isCompact (P.hn (e k).val) _).closure_of_subset (rf4_annulus_subset_closed _ _)
  let R := rf7_appendPieceCover Q m a V ha (fun k ↦ rf4_annulus_isOpen _ _) hVc hat hao
  let D : rf4_OuterData C (rf7_outer b P.f) :=
    { P := R, r := rf7_radius b, hr := by
        have hr := (b6t_discs b P.hb).1
        unfold rf7_radius
        positivity
      m := m, deg := fun k ↦ P.n (e k).val, hdeg := fun k ↦ P.hn (e k).val,
      c := fun k ↦ b (idx k), ann := Fin.natAdd Q.n,
      hann := fun k ↦ by simp [R, rf7_appendPieceCover, V] }
  refine ⟨D, e, idx, rfl, ?_, ?_, ?_, ?_⟩
  · intro k
    exact ⟨hidx k, rfl, rfl⟩
  · intro k
    simpa [D, R, rf7_appendPieceCover] using And.intro (has k) (hap k)
  · intro j
    have hst : (R.chart j).source ⊆ P.f ⁻¹' b6a_stationaryOpen b := by
      refine Fin.addCases (fun k ↦ ?_) (fun k ↦ ?_) j
      · obtain ⟨p, hp⟩ := hQ k
        simpa [R, rf7_appendPieceCover, hp] using hAs p
      · simpa [R, rf7_appendPieceCover] using hast k
    intro y hy i hi
    exact hst hy (mem_iUnion.mpr ⟨i, hi⟩)
  · intro j
    have hh : ContMDiffOn 𝓘(ℂ, (Fin 10 → ℂ) × ℂ) 𝓘(ℂ, ℂ) ω
        (fun q : b6t_polydisc b × C ↦ R.chart j q.2) (univ ×ˢ (R.chart j).source) := by
      refine Fin.addCases (fun k ↦ ?_) (fun k ↦ ?_) j
      · obtain ⟨p, hp⟩ := hQ k
        simpa [R, rf7_appendPieceCover, hp] using hAh p
      · simpa [R, rf7_appendPieceCover] using hah k
    have heq : (univ ×ˢ (R.chart j).source : Set (b6t_polydisc b × C)) =
        {q | q.2 ∈ (R.chart j).source} := by ext q; simp
    rw [heq] at hh
    exact hh

end HodgeLean.Foundations.Program
