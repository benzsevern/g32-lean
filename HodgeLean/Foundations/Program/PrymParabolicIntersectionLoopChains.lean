import HodgeLean.Foundations.Program.PrymParabolicIntersectionCells

set_option linter.unusedSectionVars false

noncomputable section
open Set Filter
open scoped Topology ContDiff Manifold
namespace HodgeLean.Foundations.Program

/-! ## Paths along the skeleton between primal windows -/

section Skeleton

variable {G : Type} [Group G] {g : Fin 13 → G} {T : Type} [TopologicalSpace T]
variable (D : hg8_DeltaMap g T)

/-- The parameter of the end vertex of a signed step on its edge.
Source: `hg2_src`, `hg2_tgt`. -/
def hga_endV (st : hg2_Edge G 13 × Bool) : unitInterval := if st.2 then 1 else 0

/-- The parameter of the start vertex of a signed step on its edge.
Source: `hg2_src`, `hg2_tgt`. -/
def hga_startV (st : hg2_Edge G 13 × Bool) : unitInterval := if st.2 then 0 else 1

theorem hga_edge_endV (st : hg2_Edge G 13 × Bool) :
    D.edge st.1 (hga_endV st) = D.vert (hga_pEnd g st) := by
  rcases st with ⟨ε, b⟩
  cases b
  · exact (D.ends ε).1
  · exact (D.ends ε).2

theorem hga_edge_startV (st : hg2_Edge G 13 × Bool) :
    D.edge st.1 (hga_startV st) = D.vert (hga_pStart g st) := by
  rcases st with ⟨ε, b⟩
  cases b
  · exact (D.ends ε).2
  · exact (D.ends ε).1

/-- A path on `[0, 1]` extended to `ℝ`, constant outside.
Source: Mathlib `Set.projIcc`. -/
def hga_ext (c : C(unitInterval, T)) : ℝ → T := fun x ↦ c (Set.projIcc 0 1 zero_le_one x)

theorem hga_ext_continuous (c : C(unitInterval, T)) : Continuous (hga_ext c) :=
  c.continuous.comp continuous_projIcc

theorem hga_ext_unitPath (c : C(unitInterval, T)) (h : Continuous (hga_ext c)) :
    hga_unitPath (hga_ext c) h = c := by
  ext t
  simp only [hga_unitPath, ContinuousMap.coe_mk, hga_ext, Set.projIcc_val]

theorem hga_ext_zero (c : C(unitInterval, T)) : hga_ext c 0 = c 0 := by
  show c _ = c _
  congr 1
  apply Subtype.ext
  simp

theorem hga_ext_one (c : C(unitInterval, T)) : hga_ext c 1 = c 1 := by
  show c _ = c _
  congr 1
  apply Subtype.ext
  simp

theorem hga_affI_val (a b t : unitInterval) :
    (b3Rest2_affI a b t : ℝ) = a + t * (b - a) := rfl

/-- The edge piece after the primal window of a step, up to the end vertex. -/
def hga_tailPiece (a : hg2_Edge G 13 × Bool) : C(unitInterval, T) :=
  b3Rest2_restr (D.edge a.1) (hga_pEndPar a) (hga_endV a)

/-- The edge piece from the start vertex of a step up to its primal window. -/
def hga_headPiece (b : hg2_Edge G 13 × Bool) : C(unitInterval, T) :=
  b3Rest2_restr (D.edge b.1) (hga_startV b) (hga_pStartPar b)

/-- **The skeleton path** from the end of the primal window of `a` to the start of the primal
window of `b`, through the common vertex.
Source: `hga_concat`; edge walks. -/
def hga_skelPath (a b : hg2_Edge G 13 × Bool) : ℝ → T :=
  hga_concat (hga_ext (hga_tailPiece D a)) (hga_ext (hga_headPiece D b))

variable {D}

theorem hga_skelPath_match {a b : hg2_Edge G 13 × Bool} (hab : hga_pEnd g a = hga_pStart g b) :
    hga_ext (hga_tailPiece D a) 1 = hga_ext (hga_headPiece D b) 0 := by
  rw [hga_ext_one, hga_ext_zero, hga_tailPiece, hga_headPiece, b3Rest2_restr_apply,
    b3Rest2_restr_apply, hga_affI_one, hga_affI_zero, hga_edge_endV, hga_edge_startV, hab]

theorem hga_skelPath_continuous {a b : hg2_Edge G 13 × Bool}
    (hab : hga_pEnd g a = hga_pStart g b) : Continuous (hga_skelPath D a b) :=
  hga_concat_continuous (hga_ext_continuous _) (hga_ext_continuous _) (hga_skelPath_match hab)

theorem hga_skelPath_pathChain {a b : hg2_Edge G 13 × Bool}
    (hab : hga_pEnd g a = hga_pStart g b) :
    b6m_pathChain (hga_unitPath (hga_skelPath D a b) (hga_skelPath_continuous hab)) =
      b6m_pathChain (hga_tailPiece D a) + b6m_pathChain (hga_headPiece D b) := by
  have h := hga_concat_pathChain (hga_ext_continuous (hga_tailPiece D a))
    (hga_ext_continuous (hga_headPiece D b)) (hga_skelPath_match hab)
  rw [hga_ext_unitPath, hga_ext_unitPath] at h
  exact h

theorem hga_skelPath_zero (a b : hg2_Edge G 13 × Bool) :
    hga_skelPath D a b 0 = D.edge a.1 (hga_pEndPar a) := by
  rw [hga_skelPath, hga_concat_left _ _ (by norm_num), mul_zero, hga_ext_zero, hga_tailPiece,
    b3Rest2_restr_apply, hga_affI_zero]

theorem hga_skelPath_one (a b : hg2_Edge G 13 × Bool) :
    hga_skelPath D a b 1 = D.edge b.1 (hga_pStartPar b) := by
  rw [hga_skelPath, hga_concat_right _ _ (by norm_num), show (2 : ℝ) * 1 - 1 = 1 by norm_num,
    hga_ext_one, hga_headPiece, b3Rest2_restr_apply, hga_affI_one]

theorem hga_pEndPar_val (st : hg2_Edge G 13 × Bool) :
    (hga_pEndPar st : ℝ) =
      if st.2 then (hga_W st.1).s + (hga_W st.1).δ else (hga_W st.1).s - (hga_W st.1).δ := by
  have h1 := (hga_W st.1).hδ
  have h2 := (hga_W st.1).hs0
  have h3 := (hga_W st.1).hs1
  unfold hga_pEndPar
  split_ifs
  · exact hga_projIcc_val ⟨by linarith, by linarith⟩
  · exact hga_projIcc_val ⟨by linarith, by linarith⟩

theorem hga_pStartPar_val (st : hg2_Edge G 13 × Bool) :
    (hga_pStartPar st : ℝ) =
      if st.2 then (hga_W st.1).s - (hga_W st.1).δ else (hga_W st.1).s + (hga_W st.1).δ := by
  have h1 := (hga_W st.1).hδ
  have h2 := (hga_W st.1).hs0
  have h3 := (hga_W st.1).hs1
  unfold hga_pStartPar
  split_ifs
  · exact hga_projIcc_val ⟨by linarith, by linarith⟩
  · exact hga_projIcc_val ⟨by linarith, by linarith⟩

/-- The skeleton path stays on edges away from their crossing points. -/
theorem hga_skelPath_pts (a b : hg2_Edge G 13 × Bool) (x : ℝ) :
    ∃ ε θ, hga_skelPath D a b x = D.edge ε θ ∧ (θ : ℝ) ≠ (hga_W ε).s := by
  unfold hga_skelPath hga_concat
  split_ifs
  · set t := Set.projIcc (0 : ℝ) 1 zero_le_one (2 * x)
    refine ⟨a.1, b3Rest2_affI (hga_pEndPar a) (hga_endV a) t, rfl, ?_⟩
    have ht := t.2
    have h1 := (hga_W a.1).hδ
    have h2 := (hga_W a.1).hs0
    have h3 := (hga_W a.1).hs1
    rw [hga_affI_val, hga_pEndPar_val]
    rcases a with ⟨ε, bo⟩
    cases bo
    · simp only [hga_endV, Bool.false_eq_true, if_false, Set.Icc.coe_zero]
      intro h
      nlinarith [ht.1, ht.2]
    · simp only [hga_endV, if_true, Set.Icc.coe_one]
      intro h
      nlinarith [ht.1, ht.2]
  · set t := Set.projIcc (0 : ℝ) 1 zero_le_one (2 * x - 1)
    refine ⟨b.1, b3Rest2_affI (hga_startV b) (hga_pStartPar b) t, rfl, ?_⟩
    have ht := t.2
    have h1 := (hga_W b.1).hδ
    have h2 := (hga_W b.1).hs0
    have h3 := (hga_W b.1).hs1
    rw [hga_affI_val, hga_pStartPar_val]
    rcases b with ⟨ε, bo⟩
    cases bo
    · simp only [hga_startV, Bool.false_eq_true, if_false, Set.Icc.coe_one]
      intro h
      nlinarith [ht.1, ht.2]
    · simp only [hga_startV, if_true, Set.Icc.coe_zero]
      intro h
      nlinarith [ht.1, ht.2]

end Skeleton

/-! ## Telescoping the chains of the glued loops -/

section ChainSums

open Classical

variable {G : Type} [Group G] [Fintype G] {g : Fin 13 → G} {T : Type} [TopologicalSpace T]
variable (D : hg8_DeltaMap g T)

theorem hga_coef_smul_sum {M : Type} [AddCommGroup M] (L : List (hg2_Edge G 13 × Bool))
    (F : hg2_Edge G 13 → M) :
    ∑ ε, hga_coef L ε • F ε = ∑ j : Fin L.length, hga_sgn L[j.1].2 • F L[j.1].1 := by
  simp only [hga_coef_eq_sum, Finset.sum_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  simp only [ite_smul, zero_smul]
  rw [Finset.sum_ite_eq]
  exact if_pos (Finset.mem_univ _)

theorem hga_coef_mul_sum (L L' : List (hg2_Edge G 13 × Bool)) :
    ∑ ε, hga_coef L ε * hga_coef L' ε = ∑ j : Fin L.length, ∑ l : Fin L'.length,
      if L[j.1].1 = L'[l.1].1 then hga_sgn L[j.1].2 * hga_sgn L'[l.1].2 else 0 := by
  have h := hga_coef_smul_sum L (fun ε ↦ hga_coef L' ε)
  simp only [smul_eq_mul] at h
  rw [h]
  apply Finset.sum_congr rfl
  intro j _
  rw [hga_coef_eq_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l _
  by_cases hjl : L[j.1].1 = L'[l.1].1
  · rw [if_pos hjl.symm, if_pos hjl]
  · rw [if_neg (Ne.symm hjl), if_neg hjl, mul_zero]

theorem hga_TL_pot (σ : C(Convexity.StdSimplex ℝ (Fin 3), T))
    (o a b : Convexity.StdSimplex ℝ (Fin 3)) : hga_TL σ a b = hga_TL σ o b - hga_TL σ o a := by
  rw [← hga_TL_trans σ a o b, hga_TL_symm σ o a]
  abel

theorem hga_face_dStart (st : hg2_Edge G 13 × Bool) :
    hg5_face (D.tri (hga_dStart g st)) (hga_faceIdx st.1) = D.edge st.1 := by
  rw [hga_face_tri]
  unfold hga_dStart
  split
  · rw [hga_faceEdge_out]
  · rw [hga_faceEdge_in]

theorem hga_face_dEnd (st : hg2_Edge G 13 × Bool) :
    hg5_face (D.tri (hga_dEnd g st)) (hga_faceIdx st.1) = D.edge st.1 := by
  rw [hga_face_tri]
  unfold hga_dEnd
  split
  · rw [hga_faceEdge_in]
  · rw [hga_faceEdge_out]

/-- The barycentre of the standard simplex. -/
abbrev hga_bary : Convexity.StdSimplex ℝ (Fin 3) := hga_triangleRetraction 0

/-- The chain of a spoke of a realized triangle, as a path chain. -/
def hga_Sp (τ : hg2_Tri G 13) (k : Fin 3) :
    b6m_chainQuotient (CategoryTheory.Functor.obj TopCat.toSSet (TopCat.of T)) :=
  hga_TL (D.tri τ) (hga_facePt k (1 / 2)) hga_bary

/-- The chain of a directed dual window, through the barycentres. -/
theorem hga_dWinDir_chain_bary (st : hg2_Edge G 13 × Bool) :
    b6m_pathChain (hga_unitPath (hga_dWinDir D st) (hga_dWinDir_continuous D st)) =
      hga_TL (D.tri (hga_dStart g st)) (hga_dStartPt st) hga_bary -
        hga_Sp D (hga_dStart g st) (hga_faceIdx st.1) + hga_Sp D (hga_dEnd g st) (hga_faceIdx st.1) +
        hga_TL (D.tri (hga_dEnd g st)) hga_bary (hga_dEndPt st) := by
  rw [hga_dWinDir_pathChain]
  have hA := hga_TL_face D (hga_dStart g st) (hga_faceIdx st.1) st.1 (hga_face_dStart D st)
    (1 / 2) (hga_W st.1).s
  have hB := hga_TL_face D (hga_dEnd g st) (hga_faceIdx st.1) st.1 (hga_face_dEnd D st)
    (hga_W st.1).s (1 / 2)
  rw [hga_restr_reverse] at hB
  rw [← hga_TL_trans _ _ (hga_facePt (hga_faceIdx st.1) (1 / 2)), hA,
    ← hga_TL_trans (D.tri (hga_dEnd g st)) _ (hga_facePt (hga_faceIdx st.1) (1 / 2)), hB]
  unfold hga_Sp
  rw [← hga_TL_trans (D.tri (hga_dStart g st)) (hga_dStartPt st) hga_bary,
    ← hga_TL_trans (D.tri (hga_dEnd g st)) (hga_facePt (hga_faceIdx st.1) (1 / 2)) hga_bary,
    hga_TL_symm (D.tri (hga_dStart g st)) _ hga_bary]
  abel

theorem hga_dualEdge_cq (ε : hg2_Edge G 13) :
    b6m_chainQuotientMap _ (hga_dualEdgeChain D ε) =
      hga_Sp D (hga_triIn ε) (hga_faceIdx ε) - hga_Sp D (hga_triOut g ε) (hga_faceIdx ε) := by
  rw [hga_dualEdgeChain, map_sub, hga_spoke_TL, hga_spoke_TL]
  rfl

theorem hga_sgn_dualEdge (st : hg2_Edge G 13 × Bool) :
    hga_sgn st.2 • b6m_chainQuotientMap _ (hga_dualEdgeChain D st.1) =
      hga_Sp D (hga_dEnd g st) (hga_faceIdx st.1) - hga_Sp D (hga_dStart g st) (hga_faceIdx st.1) := by
  rw [hga_dualEdge_cq]
  rcases st with ⟨ε, b⟩
  cases b
  · simp only [hga_sgn, hga_dEnd, hga_dStart, Bool.false_eq_true, if_false, neg_smul, one_smul]
    abel
  · simp only [hga_sgn, hga_dEnd, hga_dStart, if_true, one_smul]

theorem hga_dWalkChain_cq (L : List (hg2_Edge G 13 × Bool)) :
    b6m_chainQuotientMap _ (hga_dWalkChain D L) = ∑ j : Fin L.length,
      (hga_Sp D (hga_dEnd g L[j.1]) (hga_faceIdx L[j.1].1) -
        hga_Sp D (hga_dStart g L[j.1]) (hga_faceIdx L[j.1].1)) := by
  rw [hga_dWalkChain, map_sum]
  simp only [map_zsmul]
  rw [hga_coef_smul_sum L (fun ε ↦ b6m_chainQuotientMap _ (hga_dualEdgeChain D ε))]
  apply Finset.sum_congr rfl
  intro j _
  exact hga_sgn_dualEdge D L[j.1]

/-- **The chain of the dual loop**: windows and connecting paths telescope to the chain of the
dual walk. -/
theorem hga_dual_chain_sum (τ₀ : hg2_Tri G 13) (L : List (hg2_Edge G 13 × Bool))
    (hL : hga_DChain g τ₀ L τ₀) (hn : 0 < L.length) :
    ∑ j : Fin L.length,
      (b6m_pathChain (hga_unitPath (hga_dWinDir D L[j.1]) (hga_dWinDir_continuous D _)) +
        hga_TL (D.tri (hga_dEnd g L[j.1])) (hga_dEndPt L[j.1])
          (hga_dStartPt L[(hga_finSucc L.length hn j).1])) =
      b6m_chainQuotientMap _ (hga_dWalkChain D L) := by
  rw [hga_dWalkChain_cq]
  let X : Fin L.length → b6m_chainQuotient (CategoryTheory.Functor.obj TopCat.toSSet (TopCat.of T)) :=
    fun j ↦ hga_TL (D.tri (hga_dStart g L[j.1])) (hga_dStartPt L[j.1]) hga_bary
  have hj : ∀ j : Fin L.length,
      b6m_pathChain (hga_unitPath (hga_dWinDir D L[j.1]) (hga_dWinDir_continuous D _)) +
        hga_TL (D.tri (hga_dEnd g L[j.1])) (hga_dEndPt L[j.1])
          (hga_dStartPt L[(hga_finSucc L.length hn j).1]) =
      (hga_Sp D (hga_dEnd g L[j.1]) (hga_faceIdx L[j.1].1) -
        hga_Sp D (hga_dStart g L[j.1]) (hga_faceIdx L[j.1].1)) + (X j - X (hga_finSucc L.length hn j)) := by
    intro j
    rw [hga_dWinDir_chain_bary]
    have hc := hga_DChain_cyclic g hL hn j
    simp only [X]
    rw [← hc, hga_TL_pot (D.tri (hga_dEnd g L[j.1])) hga_bary (hga_dEndPt L[j.1])
        (hga_dStartPt L[(hga_finSucc L.length hn j).1]),
      hga_TL_symm (D.tri (hga_dEnd g L[j.1])) (hga_dStartPt L[(hga_finSucc L.length hn j).1])
        hga_bary]
    abel
  have hX : ∑ j, (X j - X (hga_finSucc L.length hn j)) = 0 := by
    rw [Finset.sum_sub_distrib, hga_sum_finSucc L.length hn X, sub_self]
  rw [Finset.sum_congr rfl (fun j _ ↦ hj j), Finset.sum_add_distrib, hX, add_zero]

theorem hga_restr_sgn (st : hg2_Edge G 13 × Bool) :
    b6m_pathChain (b3Rest2_restr (D.edge st.1) (hga_startV st) (hga_endV st)) =
      hga_sgn st.2 • b6m_pathChain (D.edge st.1) := by
  rcases st with ⟨ε, b⟩
  cases b
  · simp only [hga_startV, hga_endV, hga_sgn, Bool.false_eq_true, if_false, neg_smul, one_smul]
    exact b6m_pathChain_reverse _
  · simp only [hga_startV, hga_endV, hga_sgn, if_true, one_smul]
    rw [b3Rest2_restr_zero_one]

theorem hga_pWalkChain_cq (L : List (hg2_Edge G 13 × Bool)) :
    b6m_chainQuotientMap _ (hga_pWalkChain D L) =
      ∑ j : Fin L.length, hga_sgn L[j.1].2 • b6m_pathChain (D.edge L[j.1].1) := by
  rw [hga_pWalkChain, map_sum]
  simp only [map_zsmul]
  exact hga_coef_smul_sum L (fun ε ↦ b6m_pathChain (D.edge ε))

/-- **The chain of the primal loop**: windows and skeleton paths telescope to the chain of the
edge walk. -/
theorem hga_prim_chain_sum (L : List (hg2_Edge G 13 × Bool)) (hn : 0 < L.length) :
    ∑ j : Fin L.length,
      (b6m_pathChain (hga_unitPath (hga_pWinDir D L[j.1]) (hga_pWinDir_continuous D _)) +
        (b6m_pathChain (hga_tailPiece D L[j.1]) +
          b6m_pathChain (hga_headPiece D L[(hga_finSucc L.length hn j).1]))) =
      b6m_chainQuotientMap _ (hga_pWalkChain D L) := by
  rw [hga_pWalkChain_cq]
  let Y : Fin L.length → b6m_chainQuotient (CategoryTheory.Functor.obj TopCat.toSSet (TopCat.of T)) :=
    fun j ↦ b6m_pathChain (hga_headPiece D L[j.1])
  have hj : ∀ j : Fin L.length,
      b6m_pathChain (hga_unitPath (hga_pWinDir D L[j.1]) (hga_pWinDir_continuous D _)) +
        (b6m_pathChain (hga_tailPiece D L[j.1]) +
          b6m_pathChain (hga_headPiece D L[(hga_finSucc L.length hn j).1])) =
      hga_sgn L[j.1].2 • b6m_pathChain (D.edge L[j.1].1) + (Y (hga_finSucc L.length hn j) - Y j) := by
    intro j
    rw [hga_pWinDir_pathChain, ← hga_restr_sgn]
    simp only [Y, hga_tailPiece, hga_headPiece]
    rw [b6m_pathChain_subdiv (D.edge L[j.1].1) (hga_startV L[j.1]) (hga_pStartPar L[j.1])
        (hga_endV L[j.1]),
      b6m_pathChain_subdiv (D.edge L[j.1].1) (hga_pStartPar L[j.1]) (hga_pEndPar L[j.1])
        (hga_endV L[j.1])]
    abel
  have hY : ∑ j, (Y (hga_finSucc L.length hn j) - Y j) = 0 := by
    rw [Finset.sum_sub_distrib, hga_sum_finSucc L.length hn Y, sub_self]
  rw [Finset.sum_congr rfl (fun j _ ↦ hj j), Finset.sum_add_distrib, hY, add_zero]

end ChainSums

end HodgeLean.Foundations.Program
