import HodgeLean.Foundations.Program.PrymParabolicIntersectionStepWindows

set_option linter.unusedSectionVars false

noncomputable section
open Set Filter
open scoped Topology ContDiff Manifold
namespace HodgeLean.Foundations.Program

attribute [local instance] b3Forms_isManifold_real

/-! ## Cell facts of a realization -/

/-- **Cell facts** of a realization of `X̃(g)`: the images of the open triangles are open and avoid
the edges, and an interior point of an edge determines the edge and the parameter.
Source: `hg8_tri_attach`, `hg8_skel_cells`, `hg8_edge_embed`; Hatcher, *Algebraic Topology*, §2.1
(open simplices of a Δ-complex). -/
structure hga_Cells {G : Type} [Group G] {g : Fin 13 → G} {T : Type} [TopologicalSpace T]
    (D : hg8_DeltaMap g T) : Prop where
  tri_open : ∀ τ, IsOpen (D.tri τ '' {a | ∀ k, 0 < Convexity.StdSimplex.weights a k})
  tri_edge : ∀ τ a, (∀ k, 0 < Convexity.StdSimplex.weights a k) → ∀ ε θ, D.tri τ a ≠ D.edge ε θ
  edge_inj : ∀ ε ε' (θ θ' : unitInterval), (θ : ℝ) ∈ Ioo (0 : ℝ) 1 →
    D.edge ε θ = D.edge ε' θ' → ε = ε' ∧ θ = θ'

section Directed

variable {G : Type} [Group G] {g : Fin 13 → G} {T : Type} [TopologicalSpace T]
variable (D : hg8_DeltaMap g T)

theorem hga_W_s_mem (ε : hg2_Edge G 13) : (hga_W ε).s ∈ Ioo (0 : ℝ) 1 :=
  ⟨by linarith [(hga_W ε).hδ, (hga_W ε).hs0], by linarith [(hga_W ε).hδ, (hga_W ε).hs1]⟩

theorem hga_W_win_mem (ε : hg2_Edge G 13) {θ : ℝ}
    (hθ : θ ∈ Icc ((hga_W ε).s - (hga_W ε).δ) ((hga_W ε).s + (hga_W ε).δ)) :
    θ ∈ Ioo (0 : ℝ) 1 :=
  ⟨by linarith [(hga_W ε).hs0, hθ.1], by linarith [(hga_W ε).hs1, hθ.2]⟩

/-- Every point of a directed dual window is the crossing point of its edge or an interior point
of a realized triangle. -/
theorem hga_dWinDir_cases (st : hg2_Edge G 13 × Bool) (x : ℝ) :
    hga_dWinDir D st x = D.edge st.1 (Set.projIcc 0 1 zero_le_one (hga_W st.1).s) ∨
      ∃ τ a, (∀ j, 0 < Convexity.StdSimplex.weights a j) ∧ hga_dWinDir D st x = D.tri τ a := by
  have key : ∀ y, hga_dualWin (hga_W st.1) D (hga_triOut g st.1) (hga_triIn st.1) y =
        D.edge st.1 (Set.projIcc 0 1 zero_le_one (hga_W st.1).s) ∨
      ∃ τ a, (∀ j, 0 < Convexity.StdSimplex.weights a j) ∧
        hga_dualWin (hga_W st.1) D (hga_triOut g st.1) (hga_triIn st.1) y = D.tri τ a := by
    intro y
    rcases hga_dualWin_cases (hga_W_fo D st.1) (hga_W_fi D st.1) y with h | ⟨a, ha, h⟩ | ⟨a, ha, h⟩
    · exact Or.inl h
    · exact Or.inr ⟨_, a, ha, h⟩
    · exact Or.inr ⟨_, a, ha, h⟩
  rcases st with ⟨ε, b⟩
  cases b
  · exact key (1 - x)
  · exact key x

/-- Every point of a directed primal window lies on its edge, in the window of parameters. -/
theorem hga_pWinDir_pts (st : hg2_Edge G 13 × Bool) (x : ℝ) :
    ∃ θ : unitInterval,
      (θ : ℝ) ∈ Icc ((hga_W st.1).s - (hga_W st.1).δ) ((hga_W st.1).s + (hga_W st.1).δ) ∧
        hga_pWinDir D st x = D.edge st.1 θ := by
  have key : ∀ y, ∃ θ : unitInterval,
      (θ : ℝ) ∈ Icc ((hga_W st.1).s - (hga_W st.1).δ) ((hga_W st.1).s + (hga_W st.1).δ) ∧
        hga_primWin (hga_W st.1) D st.1 y = D.edge st.1 θ := by
    intro y
    have hm := (hga_W st.1).primParam_mem y
    refine ⟨Set.projIcc 0 1 zero_le_one ((hga_W st.1).primParam y), ?_, rfl⟩
    rw [hga_projIcc_val (Ioo_subset_Icc_self (hga_W_win_mem st.1 hm))]
    exact hm
  rcases st with ⟨ε, b⟩
  cases b
  · exact key (1 - x)
  · exact key x

variable {D}

/-- A point of a directed dual window on an edge is the crossing point of its own edge. -/
theorem hga_dWinDir_edge (hC : hga_Cells D) (st : hg2_Edge G 13 × Bool) (x : ℝ)
    (ε' : hg2_Edge G 13) (θ' : unitInterval) (h : hga_dWinDir D st x = D.edge ε' θ') :
    ε' = st.1 ∧ (θ' : ℝ) = (hga_W st.1).s := by
  have hs := hga_W_s_mem st.1
  rcases hga_dWinDir_cases D st x with h1 | ⟨τ, a, ha, h1⟩
  · rw [h1] at h
    obtain ⟨e1, e2⟩ := hC.edge_inj _ _ _ _ (by rw [hga_projIcc_val (Ioo_subset_Icc_self hs)]; exact hs) h
    exact ⟨e1.symm, by rw [← e2, hga_projIcc_val (Ioo_subset_Icc_self hs)]⟩
  · exact absurd (h1.symm.trans h) (hC.tri_edge τ a ha ε' θ')

/-- **Directed windows cross only on the same edge, at their middles.** -/
theorem hga_dir_cross (hC : hga_Cells D)
    (hcross : ∀ (ε : hg2_Edge G 13) (x y : ℝ),
      hga_dualWin (hga_W ε) D (hga_triOut g ε) (hga_triIn ε) x = hga_primWin (hga_W ε) D ε y →
        x = 1 / 2 ∧ y = 1 / 2)
    (a b : hg2_Edge G 13 × Bool) (x y : ℝ) (h : hga_dWinDir D a x = hga_pWinDir D b y) :
    a.1 = b.1 ∧ x = 1 / 2 ∧ y = 1 / 2 := by
  obtain ⟨θ, -, hy⟩ := hga_pWinDir_pts D b y
  obtain ⟨e1, -⟩ := hga_dWinDir_edge hC a x _ _ (h.trans hy)
  refine ⟨e1.symm, ?_⟩
  rcases a with ⟨ε, ba⟩
  rcases b with ⟨ε', bb⟩
  simp only at e1
  subst e1
  cases ba <;> cases bb
  · have := hcross ε' (1 - x) (1 - y) h
    constructor <;> linarith [this.1, this.2]
  · have := hcross ε' (1 - x) y h
    constructor <;> linarith [this.1, this.2]
  · have := hcross ε' x (1 - y) h
    constructor <;> linarith [this.1, this.2]
  · exact hcross ε' x y h

variable (D)

theorem hga_dWinDir_half (st : hg2_Edge G 13 × Bool) :
    hga_dWinDir D st (1 / 2) = D.edge st.1 (Set.projIcc 0 1 zero_le_one (hga_W st.1).s) := by
  have h := (hga_windows_meet (hga_W_fo D st.1) (hga_W_fi D st.1)).1
  rcases st with ⟨ε, b⟩
  cases b
  · change hga_dualWin (hga_W ε) D (hga_triOut g ε) (hga_triIn ε) (1 - 1 / 2) = _
    rw [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num]
    exact h
  · exact h

theorem hga_pWinDir_half (st : hg2_Edge G 13 × Bool) :
    hga_pWinDir D st (1 / 2) = D.edge st.1 (Set.projIcc 0 1 zero_le_one (hga_W st.1).s) := by
  have h := (hga_windows_meet (D := D) (ε := st.1) (τo := hga_triOut g st.1) (τi := hga_triIn st.1)
    (hga_W_fo D st.1) (hga_W_fi D st.1)).2
  rcases st with ⟨ε, b⟩
  cases b
  · change hga_primWin (hga_W ε) D ε (1 - 1 / 2) = _
    rw [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num]
    exact h
  · exact h

end Directed

section DirectedSmooth

variable {G : Type} [Group G] {g : Fin 13 → G} {T : Type} [TopologicalSpace T]
  [ChartedSpace ℂ T] [IsManifold 𝓘(ℂ, ℂ) ω T]
variable (D : hg8_DeltaMap g T)

/-- The sign `±1` of a step direction as a real number. -/
def hga_sgnR (b : Bool) : ℝ := if b then 1 else -1

theorem hga_dWinDir_good
    (hdg : ∀ ε : hg2_Edge G 13, b3A_IsGoodPath (E := ℂ)
      (hga_dualWin (hga_W ε) D (hga_triOut g ε) (hga_triIn ε))
      (D.tri (hga_triOut g ε) ((hga_W ε).Mo 1)) (D.tri (hga_triIn ε) ((hga_W ε).Mi 1)))
    (st : hg2_Edge G 13 × Bool) :
    b3A_IsGoodPath (E := ℂ) (hga_dWinDir D st) (D.tri (hga_dStart g st) (hga_dStartPt st))
      (D.tri (hga_dEnd g st) (hga_dEndPt st)) := by
  rcases st with ⟨ε, b⟩
  cases b
  · exact (hdg ε).symm
  · exact hdg ε

theorem hga_pWinDir_good
    (hpg : ∀ ε : hg2_Edge G 13, b3A_IsGoodPath (E := ℂ) (hga_primWin (hga_W ε) D ε)
      (D.edge ε (Set.projIcc 0 1 zero_le_one ((hga_W ε).s - (hga_W ε).δ)))
      (D.edge ε (Set.projIcc 0 1 zero_le_one ((hga_W ε).s + (hga_W ε).δ))))
    (st : hg2_Edge G 13 × Bool) :
    b3A_IsGoodPath (E := ℂ) (hga_pWinDir D st) (D.edge st.1 (hga_pStartPar st))
      (D.edge st.1 (hga_pEndPar st)) := by
  rcases st with ⟨ε, b⟩
  cases b
  · exact (hpg ε).symm
  · exact hpg ε

theorem hga_dir_velocity {γ : ℝ → T} (hγ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) 1 γ) (b : Bool) :
    b3_velocity ℂ T (if b then γ else fun τ ↦ γ (1 - τ)) (1 / 2) =
      hga_sgnR b • b3_velocity ℂ T γ (1 / 2) := by
  cases b
  · change b3_velocity ℂ T (fun τ ↦ γ (1 - τ)) (1 / 2) = (-1 : ℝ) • _
    rw [hga_reverse_velocity hγ, show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num]
  · change b3_velocity ℂ T γ (1 / 2) = (1 : ℝ) • _
    rw [one_smul]

/-- **Sign of the crossing of directed windows**: the product of the directions. -/
theorem hga_dir_sign
    (hdg : ∀ ε : hg2_Edge G 13, ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) 1
      (hga_dualWin (hga_W ε) D (hga_triOut g ε) (hga_triIn ε)))
    (hpg : ∀ ε : hg2_Edge G 13, ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) 1 (hga_primWin (hga_W ε) D ε))
    (hsign : ∀ ε : hg2_Edge G 13, SignType.sign (b3_orient ℂ
      (b3_velocity ℂ T (hga_dualWin (hga_W ε) D (hga_triOut g ε) (hga_triIn ε)) (1 / 2))
      (b3_velocity ℂ T (hga_primWin (hga_W ε) D ε) (1 / 2))) = 1)
    (a b : hg2_Edge G 13 × Bool) (hab : a.1 = b.1) (c : ℝ) (hc : 0 < c) :
    ((SignType.sign (b3_orient ℂ (c • b3_velocity ℂ T (hga_dWinDir D a) (1 / 2))
        (c • b3_velocity ℂ T (hga_pWinDir D b) (1 / 2))) : SignType) : ℤ) =
      hga_sgn a.2 * hga_sgn b.2 := by
  rcases a with ⟨ε, ba⟩
  rcases b with ⟨ε', bb⟩
  simp only at hab
  subst hab
  have hv1 := hga_dir_velocity (hdg ε) ba
  have hv2 := hga_dir_velocity (hpg ε) bb
  have e1 : hga_dWinDir D (ε, ba) = if ba then hga_dualWin (hga_W ε) D (hga_triOut g ε) (hga_triIn ε)
      else fun τ ↦ hga_dualWin (hga_W ε) D (hga_triOut g ε) (hga_triIn ε) (1 - τ) := rfl
  have e2 : hga_pWinDir D (ε, bb) = if bb then hga_primWin (hga_W ε) D ε
      else fun τ ↦ hga_primWin (hga_W ε) D ε (1 - τ) := rfl
  rw [e1, e2]
  have ho : 0 < b3_orient ℂ
      (b3_velocity ℂ T (hga_dualWin (hga_W ε) D (hga_triOut g ε) (hga_triIn ε)) (1 / 2))
      (b3_velocity ℂ T (hga_primWin (hga_W ε) D ε) (1 / 2)) := sign_eq_one_iff.mp (hsign ε)
  have hc2 : 0 < c * c := mul_pos hc hc
  have H : ∀ x y X Y : ℂ, 0 < b3_orient ℂ X Y → x = hga_sgnR ba • X → y = hga_sgnR bb • Y →
      ((SignType.sign (b3_orient ℂ (c • x) (c • y)) : SignType) : ℤ) =
        hga_sgn ba * hga_sgn bb := by
    intro x y X Y hXY hx hy
    rw [hx, hy, smul_smul, smul_smul, hga_orient_smul_real]
    cases ba <;> cases bb <;> simp only [hga_sgnR, hga_sgn, Bool.false_eq_true, if_false, if_true]
    · rw [sign_pos (by nlinarith)]; rfl
    · rw [sign_neg (by nlinarith)]; rfl
    · rw [sign_neg (by nlinarith)]; rfl
    · rw [sign_pos (by nlinarith)]; rfl
  exact H _ _ _ _ ho hv1 hv2

end DirectedSmooth

/-! ## Connecting paths -/

section Connectors

variable {G : Type} [Group G] {g : Fin 13 → G} {T : Type} [TopologicalSpace T]
  [ChartedSpace ℂ T] [IsManifold 𝓘(ℂ, ℂ) ω T]
variable {D : hg8_DeltaMap g T}

/-- **Connecting paths inside an open triangle**: two interior points of a realized triangle are
joined by a good path through interior points, with the path chain of the triangle. -/
theorem hga_tri_connector (hC : hga_Cells D) (τ : hg2_Tri G 13)
    (a b : Convexity.StdSimplex ℝ (Fin 3)) (ha : ∀ j, 0 < a.weights j)
    (hb : ∀ j, 0 < b.weights j) :
    ∃ q : ℝ → T, b3A_IsGoodPath (E := ℂ) q (D.tri τ a) (D.tri τ b) ∧
      (∀ s, ∃ c : Convexity.StdSimplex ℝ (Fin 3), (∀ j, 0 < c.weights j) ∧ q s = D.tri τ c) ∧
      ∃ hq : Continuous q, b6m_pathChain (hga_unitPath q hq) = hga_TL (D.tri τ) a b := by
  obtain ⟨q, hq, hW, hc, hch⟩ := hga_exists_goodPath_approx
    (D.tri τ '' {a | ∀ k, 0 < Convexity.StdSimplex.weights a k}) (hC.tri_open τ)
    ((D.tri τ).comp (hga_segΔ a b)) (fun t ↦ ⟨_, fun k ↦ hga_segΔ_pos a b ha hb t k, rfl⟩)
  have h0 : ((D.tri τ).comp (hga_segΔ a b)) 0 = D.tri τ a := by
    rw [ContinuousMap.comp_apply, hga_segΔ_zero]
  have h1 : ((D.tri τ).comp (hga_segΔ a b)) 1 = D.tri τ b := by
    rw [ContinuousMap.comp_apply, hga_segΔ_one]
  rw [h0, h1] at hq
  refine ⟨q, hq, fun s ↦ ?_, hc, ?_⟩
  · obtain ⟨c, hc', e⟩ := hW s
    exact ⟨c, hc', e.symm⟩
  · rw [hch, hga_TL_eq, hga_segΔ_zero, hga_segΔ_one]

end Connectors

end HodgeLean.Foundations.Program
