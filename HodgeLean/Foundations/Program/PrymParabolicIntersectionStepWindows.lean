import HodgeLean.Foundations.Program.PrymParabolicIntersectionCyclic

set_option linter.unusedSectionVars false

noncomputable section
open Set Filter
open scoped Topology ContDiff Manifold
namespace HodgeLean.Foundations.Program

attribute [local instance] b3Forms_isManifold_real

/-! ## Windows attached to signed steps -/

section Steps

variable {G : Type} [Group G] {g : Fin 13 → G} {T : Type} [TopologicalSpace T]
variable (D : hg8_DeltaMap g T)

/-- The window data of a lifted edge.
Source: `hga_baseSpec`, `hga_edgeBase`. -/
abbrev hga_W (ε : hg2_Edge G 13) : hga_WindowSpec := hga_baseSpec (hga_edgeBase ε)

theorem hga_W_fo (ε : hg2_Edge G 13) :
    hg5_face (D.tri (hga_triOut g ε)) (hga_W ε).ko = D.edge ε := by
  rw [(hga_spec_faces ε).1, hga_face_tri, hga_faceEdge_out]

theorem hga_W_fi (ε : hg2_Edge G 13) :
    hg5_face (D.tri (hga_triIn ε)) (hga_W ε).ki = D.edge ε := by
  rw [(hga_spec_faces ε).2.1, hga_face_tri, hga_faceEdge_in]

theorem hga_W_fe (ε : hg2_Edge G 13) :
    hg5_face (D.tri (hga_triArc ε)) (hga_W ε).ke = D.edge ε := by
  rw [(hga_spec_faces ε).2.2, hga_face_tri, hga_faceEdge_arc]

/-- The dual window of a signed step, in its direction.
Source: `hga_dualWin`. -/
def hga_dWinDir (st : hg2_Edge G 13 × Bool) : ℝ → T :=
  if st.2 then hga_dualWin (hga_W st.1) D (hga_triOut g st.1) (hga_triIn st.1)
  else fun τ ↦ hga_dualWin (hga_W st.1) D (hga_triOut g st.1) (hga_triIn st.1) (1 - τ)

/-- The primal window of a signed step, in its direction.
Source: `hga_primWin`. -/
def hga_pWinDir (st : hg2_Edge G 13 × Bool) : ℝ → T :=
  if st.2 then hga_primWin (hga_W st.1) D st.1
  else fun τ ↦ hga_primWin (hga_W st.1) D st.1 (1 - τ)

/-- The model point where the dual window of a signed step starts.
Source: `hga_WindowSpec.Mo`, `hga_WindowSpec.Mi`. -/
def hga_dStartPt (st : hg2_Edge G 13 × Bool) : Convexity.StdSimplex ℝ (Fin 3) :=
  if st.2 then (hga_W st.1).Mo 1 else (hga_W st.1).Mi 1

/-- The model point where the dual window of a signed step ends.
Source: `hga_WindowSpec.Mo`, `hga_WindowSpec.Mi`. -/
def hga_dEndPt (st : hg2_Edge G 13 × Bool) : Convexity.StdSimplex ℝ (Fin 3) :=
  if st.2 then (hga_W st.1).Mi 1 else (hga_W st.1).Mo 1

theorem hga_dStartPt_pos (st : hg2_Edge G 13 × Bool) (j : Fin 3) :
    0 < (hga_dStartPt st).weights j := by
  unfold hga_dStartPt
  split
  · exact (hga_W st.1).Mo_pos 1 (by norm_num) j
  · exact (hga_W st.1).Mi_pos 1 (by norm_num) j

theorem hga_dEndPt_pos (st : hg2_Edge G 13 × Bool) (j : Fin 3) :
    0 < (hga_dEndPt st).weights j := by
  unfold hga_dEndPt
  split
  · exact (hga_W st.1).Mi_pos 1 (by norm_num) j
  · exact (hga_W st.1).Mo_pos 1 (by norm_num) j

theorem hga_dWinDir_continuous (st : hg2_Edge G 13 × Bool) : Continuous (hga_dWinDir D st) := by
  unfold hga_dWinDir
  split
  · exact hga_dualWin_continuous (hga_W_fo D st.1) (hga_W_fi D st.1)
  · exact hga_reverse_continuous (hga_dualWin_continuous (hga_W_fo D st.1) (hga_W_fi D st.1))

theorem hga_pWinDir_continuous (st : hg2_Edge G 13 × Bool) : Continuous (hga_pWinDir D st) := by
  unfold hga_pWinDir
  split
  · exact hga_primWin_continuous
  · exact hga_reverse_continuous hga_primWin_continuous

/-- The model segment between two points of the standard simplex.
Source: convexity of the simplex. -/
def hga_segΔ (a b : Convexity.StdSimplex ℝ (Fin 3)) : C(unitInterval, Convexity.StdSimplex ℝ (Fin 3)) :=
  hga_simplexPath (fun x j ↦ (1 - (x : ℝ)) * a.weights j + (x : ℝ) * b.weights j)
    (fun j ↦ by fun_prop)
    (fun x j ↦ add_nonneg (mul_nonneg (by linarith [x.2.2]) (a.weights_nonneg j))
      (mul_nonneg x.2.1 (b.weights_nonneg j)))
    (fun x ↦ by
      have ha := hg5_sum3 a
      have hb := hg5_sum3 b
      linear_combination (1 - (x : ℝ)) * ha + (x : ℝ) * hb)

theorem hga_segΔ_zero (a b : Convexity.StdSimplex ℝ (Fin 3)) : hga_segΔ a b 0 = a := by
  apply hg5_simplex_ext <;> simp [hga_segΔ, hga_simplexPath_weights]

theorem hga_segΔ_one (a b : Convexity.StdSimplex ℝ (Fin 3)) : hga_segΔ a b 1 = b := by
  apply hg5_simplex_ext <;> simp [hga_segΔ, hga_simplexPath_weights]

theorem hga_segΔ_pos (a b : Convexity.StdSimplex ℝ (Fin 3)) (ha : ∀ j, 0 < a.weights j)
    (hb : ∀ j, 0 < b.weights j) (x : unitInterval) (j : Fin 3) :
    0 < (hga_segΔ a b x).weights j := by
  rw [hga_segΔ, hga_simplexPath_weights]
  rcases eq_or_lt_of_le x.2.2 with h | h
  · rw [h]; simp [hb j]
  · have := ha j
    have := hb j
    have := x.2.1
    nlinarith

end Steps

section StepFacts

variable {G : Type} [Group G] {g : Fin 13 → G} {T : Type} [TopologicalSpace T]
variable (D : hg8_DeltaMap g T)

theorem hga_restr_reverse (γ : C(unitInterval, T)) (a b : unitInterval) :
    b6m_pathChain (b3Rest2_restr γ b a) = -b6m_pathChain (b3Rest2_restr γ a b) := by
  have h := b6m_pathChain_subdiv γ a b a
  have e : b3Rest2_restr γ a a = ContinuousMap.const unitInterval (γ a) := by
    ext t
    simp only [b3Rest2_restr_apply, ContinuousMap.const_apply]
    congr 1
    apply Subtype.ext
    simp [b3Rest2_affI]
  rw [e, b6m_pathChain_const] at h
  exact eq_neg_of_add_eq_zero_right h.symm

/-- The path chain between two face points of a realized triangle is the path chain of the edge
between the two parameters. -/
theorem hga_TL_face (τ : hg2_Tri G 13) (k : Fin 3) (ε : hg2_Edge G 13)
    (hf : hg5_face (D.tri τ) k = D.edge ε) (a b : ℝ) :
    hga_TL (D.tri τ) (hga_facePt k a) (hga_facePt k b) =
      b6m_pathChain (b3Rest2_restr (D.edge ε) (Set.projIcc 0 1 zero_le_one a)
        (Set.projIcc 0 1 zero_le_one b)) := by
  let m : C(unitInterval, Convexity.StdSimplex ℝ (Fin 3)) :=
    ⟨fun t ↦ Convexity.StdSimplex.map k.succAbove (Convexity.StdSimplex.homeomorphI.symm
      (b3Rest2_affI (Set.projIcc 0 1 zero_le_one a) (Set.projIcc 0 1 zero_le_one b) t)),
      (Convexity.StdSimplex.continuous_map (R := ℝ) _).comp
        (Convexity.StdSimplex.homeomorphI.symm.continuous.comp (b3Rest2_continuous_affI _ _))⟩
  have h := hga_TL_eq (D.tri τ) m
  have h0 : m 0 = hga_facePt k a := by
    change Convexity.StdSimplex.map k.succAbove (Convexity.StdSimplex.homeomorphI.symm
      (b3Rest2_affI _ _ 0)) = _
    rw [hga_affI_zero]; rfl
  have h1 : m 1 = hga_facePt k b := by
    change Convexity.StdSimplex.map k.succAbove (Convexity.StdSimplex.homeomorphI.symm
      (b3Rest2_affI _ _ 1)) = _
    rw [hga_affI_one]; rfl
  rw [h0, h1] at h
  rw [← h, ← hf]
  rfl

/-- The midpoint of the face `k` is the starting point of the spoke `k`. -/
theorem hga_facePt_half (k : Fin 3) : hga_facePt k (1 / 2) = hga_dualPoint k 0 := by
  rw [hga_dualPoint_midpoint, hga_facePt_of_wedge k ⟨by norm_num, by norm_num⟩]

/-- The chain of a spoke as a path chain between the midpoint and the barycentre. -/
theorem hga_spoke_TL (τ : hg2_Tri G 13) (k : Fin 3) :
    b6m_chainQuotientMap _ (hga_spokeChain D τ k) =
      hga_TL (D.tri τ) (hga_facePt k (1 / 2)) (hga_triangleRetraction 0) := by
  have h := hga_TL_eq (D.tri τ) ⟨hga_dualPoint k, hga_dualPoint_continuous k⟩
  change b6m_pathChain _ = _ at h
  rw [hga_facePt_half, ← hga_dualPoint_barycentre k]
  exact h

theorem hga_dWinDir_pathChain (st : hg2_Edge G 13 × Bool) :
    b6m_pathChain (hga_unitPath (hga_dWinDir D st) (hga_dWinDir_continuous D st)) =
      hga_TL (D.tri (hga_dStart g st)) (hga_dStartPt st)
          (hga_facePt (hga_faceIdx st.1) (hga_W st.1).s) +
        hga_TL (D.tri (hga_dEnd g st)) (hga_facePt (hga_faceIdx st.1) (hga_W st.1).s)
          (hga_dEndPt st) := by
  have hMo0 : (hga_W st.1).Mo 0 = hga_facePt (hga_faceIdx st.1) (hga_W st.1).s := by
    rw [(hga_W st.1).Mo0, (hga_spec_faces st.1).1]
  have hMi0 : (hga_W st.1).Mi 0 = hga_facePt (hga_faceIdx st.1) (hga_W st.1).s := by
    rw [(hga_W st.1).Mi0, (hga_spec_faces st.1).2.1]
  have hfw := hga_dualWin_pathChain (W := hga_W st.1) (D := D) (hga_W_fo D st.1) (hga_W_fi D st.1)
  rcases st with ⟨ε, b⟩
  cases b
  · have e : hga_unitPath (hga_dWinDir D (ε, false)) (hga_dWinDir_continuous D (ε, false)) =
        hga_unitPath (fun τ ↦ hga_dualWin (hga_W ε) D (hga_triOut g ε) (hga_triIn ε) (1 - τ))
          (hga_reverse_continuous (hga_dualWin_continuous (hga_W_fo D ε) (hga_W_fi D ε))) := rfl
    rw [e, hga_reverse_pathChain (hga_dualWin_continuous (hga_W_fo D ε) (hga_W_fi D ε)), hfw]
    simp only [hga_dStart, hga_dEnd, hga_dStartPt, hga_dEndPt, Bool.false_eq_true, if_false]
    rw [hga_TL_symm, hga_TL_symm (D.tri (hga_triIn ε)), hMo0, hMi0]
    abel
  · have e : hga_unitPath (hga_dWinDir D (ε, true)) (hga_dWinDir_continuous D (ε, true)) =
        hga_unitPath (hga_dualWin (hga_W ε) D (hga_triOut g ε) (hga_triIn ε))
          (hga_dualWin_continuous (hga_W_fo D ε) (hga_W_fi D ε)) := rfl
    rw [e, hfw]
    simp only [hga_dStart, hga_dEnd, hga_dStartPt, hga_dEndPt, if_true]
    rw [hMo0, hMi0]

/-- The start and end parameters of the primal window of a signed step on its edge. -/
def hga_pStartPar (st : hg2_Edge G 13 × Bool) : unitInterval :=
  Set.projIcc 0 1 zero_le_one
    (if st.2 then (hga_W st.1).s - (hga_W st.1).δ else (hga_W st.1).s + (hga_W st.1).δ)

/-- See `hga_pStartPar`. -/
def hga_pEndPar (st : hg2_Edge G 13 × Bool) : unitInterval :=
  Set.projIcc 0 1 zero_le_one
    (if st.2 then (hga_W st.1).s + (hga_W st.1).δ else (hga_W st.1).s - (hga_W st.1).δ)

theorem hga_pWinDir_pathChain (st : hg2_Edge G 13 × Bool) :
    b6m_pathChain (hga_unitPath (hga_pWinDir D st) (hga_pWinDir_continuous D st)) =
      b6m_pathChain (b3Rest2_restr (D.edge st.1) (hga_pStartPar st) (hga_pEndPar st)) := by
  rcases st with ⟨ε, b⟩
  cases b
  · have e : hga_unitPath (hga_pWinDir D (ε, false)) (hga_pWinDir_continuous D (ε, false)) =
        hga_unitPath (fun τ ↦ hga_primWin (hga_W ε) D ε (1 - τ))
          (hga_reverse_continuous hga_primWin_continuous) := rfl
    rw [e, hga_reverse_pathChain hga_primWin_continuous, hga_primWin_pathChain]
    simp only [hga_pStartPar, hga_pEndPar, Bool.false_eq_true, if_false]
    rw [hga_restr_reverse, neg_neg]
  · exact hga_primWin_pathChain

end StepFacts

end HodgeLean.Foundations.Program
