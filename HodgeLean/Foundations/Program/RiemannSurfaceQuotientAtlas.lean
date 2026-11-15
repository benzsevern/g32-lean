import HodgeLean.Foundations.Program.RiemannSurfaceQuotientCharts

noncomputable section

open Manifold
open scoped ContDiff Topology

namespace HodgeLean.Foundations.Program

theorem rsq_extend_open_homeomorph {X Y : Type}
    [TopologicalSpace X] [TopologicalSpace Y]
    (U : Set X) (V : Set Y) (hU : IsOpen U) (hV : IsOpen V)
    (a : U) (h : U ≃ₜ V) :
    ∃ e : OpenPartialHomeomorph X Y,
      e.source = U ∧ e.target = V ∧ ∀ u : U, e u = (h u : Y) := by
  let i := (⟨U, hU⟩ : TopologicalSpace.Opens X).openPartialHomeomorphSubtypeCoe ⟨a⟩
  let j := (⟨V, hV⟩ : TopologicalSpace.Opens Y).openPartialHomeomorphSubtypeCoe ⟨h a⟩
  let e := i.symm.trans (h.toOpenPartialHomeomorph.trans j)
  have hs : e.source = U := by
    simp [e, OpenPartialHomeomorph.trans_source, i, j]
  have ht : e.target = V := by
    simp [e, OpenPartialHomeomorph.trans_target, i, j]
  refine ⟨e, hs, ht, ?_⟩
  intro u
  change j (h (i.symm (u : X))) = (h u : Y)
  have hi : i.symm (u : X) = u := i.left_inv (by simp [i])
  rw [hi]
  rfl

theorem rsq_orbit_localChart {H X : Type} [Group H] [Finite H] [MulAction H X]
    [TopologicalSpace X] (hc : ∀ g : H, Continuous (fun y : X ↦ g • y))
    (x : X) (χ : MulAction.stabilizer H x →* ℂˣ) (hinj : Function.Injective χ)
    (u : X → ℂ)
    (hu : ∀ g : MulAction.stabilizer H x, ∀ y : X, u (g • y) = (χ g : ℂ) * u y)
    (e : OpenPartialHomeomorph X ℂ) (hxe : x ∈ e.source) (heu : Set.EqOn e u e.source)
    (hest : ∀ g : MulAction.stabilizer H x, Set.MapsTo (fun y : X ↦ g • y) e.source e.source)
    (hsep : ∀ y ∈ e.source, ∀ g : H, g • y ∈ e.source → g • x = x) :
    ∃ c : OpenPartialHomeomorph (rsq_Quot H X) ℂ,
      c.source = rsq_proj H X '' e.source ∧
      c.target = (fun z : ℂ ↦ z ^ Nat.card (MulAction.stabilizer H x)) '' e.target ∧
      ∀ y ∈ e.source, c (rsq_proj H X y) = e y ^ Nat.card (MulAction.stabilizer H x) := by
  classical
  have : ContinuousConstSMul H X := ⟨hc⟩
  letI := Fintype.ofFinite (MulAction.stabilizer H x)
  let n := Nat.card (MulAction.stabilizer H x)
  have hn : 0 < n := Nat.card_pos
  letI : NeZero n := ⟨hn.ne'⟩
  let f : e.source → rsq_Quot H X := fun y ↦ rsq_proj H X y
  let g : e.source → ℂ := fun y ↦ e y ^ n
  have hfc : Continuous f := continuous_quotient_mk'.comp continuous_subtype_val
  have hfo : IsOpenMap f := isOpenMap_quotient_mk'_mul.domRestrict e.open_source
  have hec : Continuous (fun y : e.source ↦ e y) := e.continuousOn.restrict
  have heo : IsOpenMap (fun y : e.source ↦ e y) :=
    e.open_target.isOpenMap_subtype_val.comp e.toHomeomorphSourceTarget.isOpenMap
  have hgc : Continuous g := hec.pow n
  have hgo : IsOpenMap g := (Complex.isOpenQuotientMap_pow n).isOpenMap.comp heo
  let F : e.source → Set.range f := Set.rangeFactorization f
  let G : e.source → Set.range g := Set.rangeFactorization g
  have hF : Topology.IsQuotientMap F :=
    (hfo.codRestrict _).isQuotientMap (hfc.codRestrict _) (Set.rangeFactorization_surjective (f := f))
  have hG : Topology.IsQuotientMap G :=
    (hgo.codRestrict _).isQuotientMap (hgc.codRestrict _) (Set.rangeFactorization_surjective (f := g))
  have hpow : ∀ z w : ℂ, z ^ n = w ^ n ↔ ∃ a, (χ a : ℂ) * z = w := by
    intro z w
    simpa only [n, Nat.card_eq_fintype_card] using rsq_character_pow_eq_iff χ hinj z w
  have hfib : ∀ y y' : e.source, F y = F y' ↔ G y = G y' := by
    intro y y'
    rw [Subtype.ext_iff, Subtype.ext_iff]
    change rsq_proj H X y = rsq_proj H X y' ↔ e y ^ n = e y' ^ n
    constructor
    · intro h
      obtain ⟨a, ha⟩ := MulAction.mem_orbit_iff.1 (Quotient.exact h)
      have has : a • x = x := hsep y' y'.property a (ha ▸ y.property)
      let b : MulAction.stabilizer H x := ⟨a, has⟩
      apply Eq.symm
      apply (hpow _ _).2
      refine ⟨b, ?_⟩
      rw [heu y.property, heu y'.property, ← hu b y']
      exact congrArg u ha
    · intro h
      obtain ⟨a, ha⟩ := (hpow _ _).1 h
      have hy := hest a y.property
      have heq : e (a • (y : X)) = e y' := by
        rw [heu hy, hu, ← heu y.property]
        exact ha
      have hy' : a • (y : X) = y' := e.injOn hy y'.property heq
      exact (rsq_proj_isGaloisCover H X).1 a y ▸ congrArg (rsq_proj H X) hy'
  obtain ⟨h, hh⟩ := rsq_homeomorph_of_quotientMaps F G hF hG hfib
  obtain ⟨c, hcs, hct, hcc⟩ := rsq_extend_open_homeomorph
    (Set.range f) (Set.range g) hfo.isOpen_range hgo.isOpen_range (F ⟨x, hxe⟩) h
  refine ⟨c, ?_, ?_, ?_⟩
  · rw [hcs]
    ext q
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨y, y.property, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨y, hy⟩, rfl⟩
  · rw [hct]
    ext w
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨e y, e.map_source y.property, rfl⟩
    · rintro ⟨z, hz, rfl⟩
      exact ⟨⟨e.symm z, e.map_target hz⟩, by
        change e (e.symm z) ^ n = z ^ n
        rw [e.right_inv hz]⟩
  · intro y hy
    have ht := hcc (F ⟨y, hy⟩)
    rw [hh] at ht
    exact ht

theorem rsq_contMDiffAt_orbit_chart_composite
    {E X H : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [TopologicalSpace X] [ChartedSpace E X] [IsManifold 𝓘(ℂ, E) ω X]
    [Group H] [MulAction H X]
    (hH : ∀ g : H, ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E) ω (fun y : X ↦ g • y))
    (e : OpenPartialHomeomorph X ℂ)
    (he : ContMDiffOn 𝓘(ℂ, E) 𝓘(ℂ, ℂ) ω e e.source)
    (c : rsq_Quot H X → ℂ) (n : ℕ)
    (hce : ∀ y ∈ e.source, c (rsq_proj H X y) = e y ^ n)
    (y : X) (hy : rsq_proj H X y ∈ rsq_proj H X '' e.source) :
    ContMDiffAt 𝓘(ℂ, E) 𝓘(ℂ, ℂ) ω (c ∘ rsq_proj H X) y := by
  obtain ⟨z, hz, hzy⟩ := hy
  obtain ⟨a, ha⟩ := MulAction.mem_orbit_iff.1 (Quotient.exact hzy)
  have hay : a • y ∈ e.source := ha.symm ▸ hz
  have hloc : ∀ᶠ t in 𝓝 y, a • t ∈ e.source :=
    (hH a).continuous.continuousAt.preimage_mem_nhds (e.open_source.mem_nhds hay)
  have heq : (c ∘ rsq_proj H X) =ᶠ[𝓝 y] (fun t ↦ e (a • t) ^ n) := by
    filter_upwards [hloc] with t ht
    change c (rsq_proj H X t) = _
    rw [← (rsq_proj_isGaloisCover H X).1 a t]
    exact hce _ ht
  have ht := ((he.contMDiffAt (e.open_source.mem_nhds hay)).comp y ((hH a) y)).pow n
  exact (Filter.EventuallyEq.contMDiffAt_iff heq).2 ht

theorem rsq_orbitChart_transition_analytic
    {E X H : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [TopologicalSpace X] [ChartedSpace E X] [IsManifold 𝓘(ℂ, E) ω X]
    [Group H] [MulAction H X]
    (hH : ∀ g : H, ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E) ω (fun y : X ↦ g • y))
    (ea eb : OpenPartialHomeomorph X ℂ) (ca cb : OpenPartialHomeomorph (rsq_Quot H X) ℂ)
    (na nb : ℕ) (hna : 0 < na) (r : ℝ)
    (heat : ea.target = Metric.ball 0 r)
    (hcas : ca.source = rsq_proj H X '' ea.source)
    (hcat : ca.target = (fun z : ℂ ↦ z ^ na) '' ea.target)
    (hcbs : cb.source = rsq_proj H X '' eb.source)
    (hca : ∀ y ∈ ea.source, ca (rsq_proj H X y) = ea y ^ na)
    (hcb : ∀ y ∈ eb.source, cb (rsq_proj H X y) = eb y ^ nb)
    (heai : ContMDiffOn 𝓘(ℂ, ℂ) 𝓘(ℂ, E) ω ea.symm ea.target)
    (heb : ContMDiffOn 𝓘(ℂ, E) 𝓘(ℂ, ℂ) ω eb eb.source) :
    ContDiffOn ℂ ω (ca.symm.trans cb) (ca.symm.trans cb).source := by
  have hinv : ∀ t ∈ ea.target, ca.symm (t ^ na) = rsq_proj H X (ea.symm t) := by
    intro t ht
    have hy := ea.map_target ht
    have hq : rsq_proj H X (ea.symm t) ∈ ca.source := by
      rw [hcas]
      exact ⟨ea.symm t, hy, rfl⟩
    have hac : ca (rsq_proj H X (ea.symm t)) = t ^ na := by
      rw [hca _ hy, ea.right_inv ht]
    rw [← hac]
    exact ca.left_inv hq
  apply (rsq_analyticOnNhd_of_comp_pow hna (ca.symm.trans cb).open_source
    (ca.symm.trans cb).continuousOn ?_).contDiffOn_of_completeSpace
  intro z hz
  have hz' : z ^ na ∈ ca.target ∧ ca.symm (z ^ na) ∈ cb.source := by
    simpa only [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source,
      Set.mem_inter_iff, Set.mem_preimage] using hz
  obtain ⟨w, hw, hwz⟩ := hcat ▸ hz'.1
  change w ^ na = z ^ na at hwz
  have hnorm : ‖z‖ = ‖w‖ := (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) hna.ne').1
    (by rw [← norm_pow, ← norm_pow, hwz])
  have hze : z ∈ ea.target := by
    rw [heat, mem_ball_zero_iff, hnorm]
    exact mem_ball_zero_iff.1 (heat ▸ hw)
  have hy : ea.symm z ∈ ea.source := ea.map_target hze
  have hqb : rsq_proj H X (ea.symm z) ∈ rsq_proj H X '' eb.source := by
    rw [← hcbs, ← hinv z hze]
    exact hz'.2
  have hbπ := rsq_contMDiffAt_orbit_chart_composite hH eb heb cb nb hcb (ea.symm z) hqb
  have haInv := heai.contMDiffAt (ea.open_target.mem_nhds hze)
  have han := (hbπ.comp z haInv).contDiffAt.analyticAt
  have heq : (fun t : ℂ ↦ (ca.symm.trans cb) (t ^ na)) =ᶠ[𝓝 z]
      ((cb ∘ rsq_proj H X) ∘ ea.symm) := by
    filter_upwards [ea.open_target.mem_nhds hze] with t ht
    change cb (ca.symm (t ^ na)) = cb (rsq_proj H X (ea.symm t))
    rw [hinv t ht]
  exact han.congr heq.symm

end HodgeLean.Foundations.Program
