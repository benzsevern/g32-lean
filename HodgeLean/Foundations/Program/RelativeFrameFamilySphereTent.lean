import HodgeLean.Foundations.Program.RelativeFrameFamilyTent

noncomputable section
open Set Manifold Filter Topology
open scoped ContDiff
namespace HodgeLean.Foundations.Program

theorem rf7_sphere_tent_preimage (b : Fin 10 → ℂ) (hb : b ∈ b6_chart)
    (t : Fin 10 → ℂ) (ht : t ∈ b6t_polydisc b) (i : Fin 10) (s : ℝ)
    (hs : b6t_radius b < s) (hs' : s ≤ 3 * b6t_radius b) :
    b6t_sphere b t ⁻¹' rf7_sphereBall (b i) s = rf7_sphereBall (b i) s := by
  have hp := (rf7_tent_preimage b hb t ht).2 i |>.2.2 s hs hs'
  ext p
  induction p using OnePoint.rec with
  | infty => simp [b6t_sphere, rf7_sphereBall]
  | coe z =>
    have hm (z : ℂ) : (z : OnePoint ℂ) ∈ rf7_sphereBall (b i) s ↔ z ∈ Metric.ball (b i) s := by
      constructor
      · rintro ⟨w, hw, hwz⟩
        exact OnePoint.coe_injective hwz ▸ hw
      · intro hz
        exact ⟨z, hz, rfl⟩
    change ((b6t_plane b t z : ℂ) : OnePoint ℂ) ∈ rf7_sphereBall (b i) s ↔
      (z : OnePoint ℂ) ∈ rf7_sphereBall (b i) s
    rw [hm, hm]
    exact Iff.of_eq (congrArg (fun S : Set ℂ ↦ z ∈ S) hp)


theorem rf7_transport_component_surj {b : Fin 10 → ℂ} {G : Type} [Group G] [Finite G] {C : Type}
    [TopologicalSpace C] [ChartedSpace ℂ C] [IsManifold 𝓘(ℂ, ℂ) ω C] [T2Space C]
    [CompactSpace C] [ConnectedSpace C] [MulAction G C]
    [ChartedSpace ((Fin 10 → ℂ) × ℂ) (b6t_polydisc b × C)]
    (P : rf7_HurwitzAtlas b G C) (i : Fin 10) (x : C)
    (hx : P.f x = ((b i : ℂ) : OnePoint ℂ)) (t : b6t_polydisc b)
    (z : ℂ) (hz : z ∈ Metric.ball (b i) (3 * b6t_radius b)) :
    ∃ y ∈ rf7_component P.f (b i) (3 * b6t_radius b) x,
      b6a_map b P.f (t, y) = (z : OnePoint ℂ) := by
  have hr := (b6t_discs b P.hb).1
  obtain ⟨E, hE⟩ := b6t_homeomorph b P.hb t.val t.2
  obtain ⟨p, hp⟩ := E.surjective (z : OnePoint ℂ)
  induction p using OnePoint.rec with
  | infty =>
    have hh : (OnePoint.infty : OnePoint ℂ) = (z : OnePoint ℂ) := by
      simpa only [hE, b6t_sphere, OnePoint.map_infty] using hp
    exact False.elim (OnePoint.coe_ne_infty z hh.symm)
  | coe a =>
    have hpa : b6t_plane b t.val a = z :=
      OnePoint.coe_injective ((hE (a : OnePoint ℂ)).symm.trans hp)
    have hpre := (rf7_tent_preimage b P.hb t.val t.2).2 i |>.2.2
      (3 * b6t_radius b) (by linarith) le_rfl
    have ha : a ∈ Metric.ball (b i) (3 * b6t_radius b) := by
      rw [← hpre]
      change b6t_plane b t.val a ∈ Metric.ball (b i) (3 * b6t_radius b)
      rw [hpa]
      exact hz
    have hbi : P.f x ∈ rf7_sphereBall (b i) (3 * b6t_radius b) := by
      rw [hx]
      exact ⟨b i, Metric.mem_ball_self (by positivity), rfl⟩
    have hm : (a : OnePoint ℂ) ∈ P.f '' rf7_component P.f (b i) (3 * b6t_radius b) x :=
      (rf7_component_onto P i x hbi).symm ▸ (show (a : OnePoint ℂ) ∈ rf7_sphereBall (b i) (3 * b6t_radius b) from ⟨a, ha, rfl⟩)
    obtain ⟨y, hy, hfy⟩ := hm
    refine ⟨y, hy, ?_⟩
    change b6t_sphere b t.val (P.f y) = _
    rw [hfy]
    exact congrArg (fun w : ℂ ↦ (w : OnePoint ℂ)) hpa

end HodgeLean.Foundations.Program
