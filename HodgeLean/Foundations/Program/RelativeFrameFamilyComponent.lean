import HodgeLean.Foundations.Program.RelativeFrameFamilyCentre
import HodgeLean.Foundations.Program.RelativeFrameFamilyDegree

noncomputable section
open Set Manifold Filter Topology
open scoped ContDiff
namespace HodgeLean.Foundations.Program
attribute [local instance] b4cov_sphChartedSpace b4cov_sph_isManifold

theorem rf7_component_unique_centre {b : Fin 10 → ℂ} {G : Type} [Group G] [Finite G] {C : Type}
    [TopologicalSpace C] [ChartedSpace ℂ C] [IsManifold 𝓘(ℂ, ℂ) ω C] [T2Space C]
    [CompactSpace C] [ConnectedSpace C] [MulAction G C]
    [ChartedSpace ((Fin 10 → ℂ) × ℂ) (b6t_polydisc b × C)]
    (P : rf7_HurwitzAtlas b G C) (i : Fin 10) (x : C)
    (hx : P.f x = ((b i : ℂ) : OnePoint ℂ))
    (hcov : IsCoveringMapOn P.f
      (rf7_sphereBall (b i) (3 * b6t_radius b) \ {((b i : ℂ) : OnePoint ℂ)}))
    (y : C) (hy : y ∈ rf7_component P.f (b i) (3 * b6t_radius b) x)
    (hfy : P.f y = ((b i : ℂ) : OnePoint ℂ)) : y = x := by
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
  have hqfin (z : ℂ) : (q ⁻¹' {z}).Finite := by
    have hh : (a ⁻¹' (P.f ⁻¹' {(z : OnePoint ℂ)})).Finite :=
      Set.Finite.preimage hai.injOn (rf7_atlas_finite_fibres P (z : OnePoint ℂ))
    apply hh.subset
    intro d hd
    change P.f (a d) = (z : OnePoint ℂ)
    rw [hproj, show q d = z from hd]
  haveI : ∀ d : D, (𝓝[≠] d).NeBot := rf7_punctured_nhds_neBot
  have hnz : ∃ d : D, q d ≠ c := by
    obtain ⟨d, hd⟩ := (dense_univ.sdiff_finite (hqfin c)).nonempty
    exact ⟨d, hd.2⟩
  obtain ⟨k, hk, v, hv, hvR, hvP⟩ := rf7_disc_cover_coordinate q hq c ρ hρ
    (fun d ↦ (p d).2) hqfin hnz hqcov
  letI : Nonempty (rf7_nonzeroLocus q hq c) := by
    obtain ⟨d, hd⟩ := hnz
    exact ⟨⟨d, hd⟩⟩
  have hqx : q xD = c := OnePoint.coe_injective ((hproj xD).symm.trans hx)
  have heq (d : D) (hd : P.f (a d) = (c : OnePoint ℂ)) : a d = x := by
    have hqd : q d = c := OnePoint.coe_injective ((hproj d).symm.trans hd)
    have hh := rf7_unique_centre_of_coordinate a ha hai q hq P.f P.hf.continuous c
      (rf7_atlas_finite_fibres P (c : OnePoint ℂ)) hproj ρ hρ k hk v hv hvR hvP d xD hqd hqx
    exact congrArg a hh
  rw [rf7_component, connectedComponentIn_eq_image (show x ∈ P.f ⁻¹' S from hxS)] at hy
  obtain ⟨u, hu, huy⟩ := hy
  have hh := heq ⟨u, hu⟩ (by change P.f u.val = _; rw [huy]; exact hfy)
  exact huy.symm.trans hh

theorem rf7_component_fibre_degree {b : Fin 10 → ℂ} {G : Type} [Group G] [Finite G] {C : Type}
    [TopologicalSpace C] [ChartedSpace ℂ C] [IsManifold 𝓘(ℂ, ℂ) ω C] [T2Space C]
    [CompactSpace C] [ConnectedSpace C] [MulAction G C]
    [ChartedSpace ((Fin 10 → ℂ) × ℂ) (b6t_polydisc b × C)]
    (P : rf7_HurwitzAtlas b G C) (i : Fin 10) (x : C)
    (hx : P.f x = ((b i : ℂ) : OnePoint ℂ))
    (hcov : IsCoveringMapOn P.f
      (rf7_sphereBall (b i) (3 * b6t_radius b) \ {((b i : ℂ) : OnePoint ℂ)}))
    (z : ℂ) (hz : z ∈ Metric.ball (b i) (3 * b6t_radius b)) (hnz : z ≠ b i) :
    Nat.card ↥(rf7_component P.f (b i) (3 * b6t_radius b) x ∩
      P.f ⁻¹' {(z : OnePoint ℂ)}) = P.n x := by
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
  let F : (q ⁻¹' {z}) → ↥(rf7_component P.f (b i) (3 * b6t_radius b) x ∩
      P.f ⁻¹' {(z : OnePoint ℂ)}) := fun d ↦
    ⟨a d.val, hadcomp d.val, by
      change P.f (a d.val) = (z : OnePoint ℂ)
      rw [hproj, show q d.val = z from d.2]⟩
  have hFi : Function.Injective F := by
    intro d d' h
    apply Subtype.ext
    apply hai
    have hh : (F d).val = (F d').val := congrArg Subtype.val h
    exact hh
  have hFs : Function.Surjective F := by
    rintro ⟨y, hy, hfy⟩
    rw [rf7_component, connectedComponentIn_eq_image (show x ∈ P.f ⁻¹' S from hxS)] at hy
    obtain ⟨u, hu, huy⟩ := hy
    let d : D := ⟨u, hu⟩
    have hqd : q d = z := by
      apply OnePoint.coe_injective
      rw [← hproj]
      change P.f u.val = (z : OnePoint ℂ)
      rw [huy]
      exact hfy
    exact ⟨⟨d, hqd⟩, Subtype.ext huy⟩
  exact (Nat.card_congr (Equiv.ofBijective F ⟨hFi, hFs⟩)).symm.trans
    (hdegree z ⟨hz, hnz⟩)

end HodgeLean.Foundations.Program
