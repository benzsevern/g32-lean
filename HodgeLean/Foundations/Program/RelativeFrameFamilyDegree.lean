import HodgeLean.Foundations.Program.RelativeFrameFamilyCovering

noncomputable section
open Set Filter Topology
namespace HodgeLean.Foundations.Program

theorem rf7_degree_of_local_power {X : Type} [TopologicalSpace X]
    (c : ℂ) (ρ : ℝ) (hρ : 0 < ρ) (p : X → Metric.ball c ρ)
    (hc : IsClosedMap p) (x : X) (hx : (p x).val = c)
    (hsingle : ∀ y, (p y).val = c → y = x)
    (e : OpenPartialHomeomorph X ℂ) (hxe : x ∈ e.source) (he0 : e x = 0)
    (n : ℕ) (hn : 0 < n)
    (hpower : ∀ y ∈ e.source, (p y).val = c + e y ^ n)
    (hcov : IsCoveringMapOn (fun y ↦ (p y).val) (Metric.ball c ρ \ {c})) :
    ∀ z ∈ Metric.ball c ρ \ {c}, Nat.card ((fun y ↦ (p y).val) ⁻¹' {z}) = n := by
  classical
  let q : X → ℂ := fun y ↦ (p y).val
  let V : Set (Metric.ball c ρ) := (p '' e.sourceᶜ)ᶜ
  have hV : IsOpen V := (hc _ e.open_source.isClosed_compl).isOpen_compl
  have hxV : p x ∈ V := by
    rintro ⟨y, hy, hpy⟩
    have hyx : y = x := hsingle y ((congrArg Subtype.val hpy).trans hx)
    exact hy (hyx ▸ hxe)
  have hW : IsOpen ((Subtype.val : Metric.ball c ρ → ℂ) '' V) :=
    Metric.isOpen_ball.isOpenEmbedding_subtypeVal.isOpenMap _ hV
  have hcW : c ∈ (Subtype.val : Metric.ball c ρ → ℂ) '' V := ⟨p x, hxV, hx⟩
  obtain ⟨ε, hε, hεW⟩ := Metric.isOpen_iff.mp hW c hcW
  have h0T : (0 : ℂ) ∈ e.target := he0 ▸ e.map_source hxe
  obtain ⟨δ, hδ, hδT⟩ := Metric.isOpen_iff.mp e.open_target 0 h0T
  let r := min ε (δ ^ n) / 2
  have hr : 0 < r := div_pos (lt_min hε (pow_pos hδ n)) (by norm_num)
  have hrε : r < ε := by dsimp [r]; linarith [min_le_left ε (δ ^ n)]
  have hrδ : r < δ ^ n := by dsimp [r]; linarith [min_le_right ε (δ ^ n), pow_pos hδ n]
  let z : ℂ := c + (r : ℂ)
  have hzε : z ∈ Metric.ball c ε := by
    simpa only [z, Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, Complex.norm_real,
      Real.norm_of_nonneg hr.le] using hrε
  obtain ⟨z', hz'V, hz'z⟩ := hεW hzε
  have hzS : z ∈ Metric.ball c ρ \ {c} := by
    refine ⟨hz'z ▸ z'.2, ?_⟩
    change c + (r : ℂ) ≠ c
    simpa only [ne_eq, add_eq_left, Complex.ofReal_eq_zero] using hr.ne'
  have hsource (y : X) (hy : q y = z) : y ∈ e.source := by
    by_contra hye
    apply hz'V
    refine ⟨y, hye, Subtype.ext ?_⟩
    exact hy.trans hz'z.symm
  have hrootT (w : ℂ) (hw : w ^ n = (r : ℂ)) : w ∈ e.target := by
    have hnorm : ‖w‖ ^ n = r := by
      rw [← norm_pow, hw, Complex.norm_real, Real.norm_of_nonneg hr.le]
    have hwδ : ‖w‖ < δ := lt_of_pow_lt_pow_left₀ n hδ.le (hnorm ▸ hrδ)
    exact hδT (by simpa only [Metric.mem_ball, dist_zero_right] using hwδ)
  let E : (q ⁻¹' {z}) ≃ {w : ℂ // w ^ n = (r : ℂ)} :=
    { toFun := fun y ↦ ⟨e y.val, by
        have h := hpower y.val (hsource y.val y.2)
        rw [show (p y.val).val = z from y.2] at h
        exact add_left_cancel h.symm⟩
      invFun := fun w ↦ ⟨e.symm w.val, by
        change (p (e.symm w.val)).val = z
        rw [hpower _ (e.map_target (hrootT w.val w.2)), e.right_inv (hrootT w.val w.2), w.2]⟩
      left_inv := fun y ↦ Subtype.ext (e.left_inv (hsource y.val y.2))
      right_inv := fun w ↦ Subtype.ext (e.right_inv (hrootT w.val w.2)) }
  have hzcard : Nat.card (q ⁻¹' {z}) = n :=
    (Nat.card_congr E).trans (rf7_power_fibre_card n hn (r : ℂ)
      (by simpa only [ne_eq, Complex.ofReal_eq_zero] using hr.ne'))
  let S := Metric.ball c ρ \ {c}
  let Q : q ⁻¹' S → S := S.restrictPreimage q
  have hQ : IsCoveringMap Q := hcov.isCoveringMap_restrictPreimage
  letI : PathConnectedSpace S := rf7_puncturedDisc_pathConnected c c ρ (by simpa using hρ)
  intro w hw
  let w' : S := ⟨w, hw⟩
  let z'' : S := ⟨z, hzS⟩
  let γ := Path.Homotopic.Quotient.mk (PathConnectedSpace.somePath w' z'')
  let F := Equiv.ofBijective (hQ.monodromy γ) (hQ.monodromy_bijective γ)
  calc
    Nat.card (q ⁻¹' {w}) = Nat.card (Q ⁻¹' {w'}) := (rf7_restrict_fibre_card q S w').symm
    _ = Nat.card (Q ⁻¹' {z''}) := Nat.card_congr F
    _ = Nat.card (q ⁻¹' {z}) := rf7_restrict_fibre_card q S z''
    _ = n := hzcard

end HodgeLean.Foundations.Program
