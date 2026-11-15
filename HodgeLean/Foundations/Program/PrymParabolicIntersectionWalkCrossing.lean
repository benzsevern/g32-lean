import HodgeLean.Foundations.Program.PrymParabolicIntersectionLoopChains

set_option linter.unusedSectionVars false

noncomputable section
open Set Filter
open scoped Topology ContDiff Manifold
namespace HodgeLean.Foundations.Program

attribute [local instance] b3Forms_isManifold_real

/-! ## Facts about the windows of a realization -/

/-- **Window facts** of a realization in a Riemann surface: the cell facts, the dual and primal
windows of every edge are good paths, cross once at their middles, with positive sign.
Source: `hga_dualWin_good`, `hga_primWin_good`, `hga_windows_cross`, `hga_windows_sign`;
Guillemin–Pollack, *Differential Topology*, Ch. 3 §3 (oriented crossing counts). -/
structure hga_WinFacts {G : Type} [Group G] {g : Fin 13 → G} {T : Type} [TopologicalSpace T]
    [ChartedSpace ℂ T] (D : hg8_DeltaMap g T) : Prop where
  cells : hga_Cells D
  dgood : ∀ ε : hg2_Edge G 13, b3A_IsGoodPath (E := ℂ)
    (hga_dualWin (hga_W ε) D (hga_triOut g ε) (hga_triIn ε))
    (D.tri (hga_triOut g ε) ((hga_W ε).Mo 1)) (D.tri (hga_triIn ε) ((hga_W ε).Mi 1))
  pgood : ∀ ε : hg2_Edge G 13, b3A_IsGoodPath (E := ℂ) (hga_primWin (hga_W ε) D ε)
    (D.edge ε (Set.projIcc 0 1 zero_le_one ((hga_W ε).s - (hga_W ε).δ)))
    (D.edge ε (Set.projIcc 0 1 zero_le_one ((hga_W ε).s + (hga_W ε).δ)))
  cross : ∀ (ε : hg2_Edge G 13) (x y : ℝ),
    hga_dualWin (hga_W ε) D (hga_triOut g ε) (hga_triIn ε) x = hga_primWin (hga_W ε) D ε y →
      x = 1 / 2 ∧ y = 1 / 2
  sign : ∀ ε : hg2_Edge G 13, SignType.sign (b3_orient ℂ
    (b3_velocity ℂ T (hga_dualWin (hga_W ε) D (hga_triOut g ε) (hga_triIn ε)) (1 / 2))
    (b3_velocity ℂ T (hga_primWin (hga_W ε) D ε) (1 / 2))) = 1

section Quarter

variable {T : Type} [TopologicalSpace T] [ChartedSpace ℂ T] [IsManifold 𝓘(ℂ, ℂ) ω T]

theorem hga_concat_vel_quarter {γ δ : ℝ → T} (hγ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) 1 γ) :
    b3Forms_velocity (E := ℂ) (hga_concat γ δ) (1 / 4) =
      (2 : ℝ) • b3Forms_velocity (E := ℂ) γ (1 / 2) := by
  have h := hga_concat_velocity_left (δ := δ) hγ (t := 1 / 4) (by norm_num)
  rw [b3Forms_velocity_eq_b3, b3Forms_velocity_eq_b3] at h
  rw [h, show (2 : ℝ) * (1 / 4) = 1 / 2 by norm_num]
  rfl

end Quarter

/-! ## Chains of the glued loops and the crossing sum -/

section LoopChains

open Classical

variable {G : Type} [Group G] [Fintype G] {g : Fin 13 → G} {T : Type} [TopologicalSpace T]
  [ChartedSpace ℂ T] [IsManifold 𝓘(ℂ, ℂ) ω T]
variable (D : hg8_DeltaMap g T)

theorem hga_dualLoop_chain (τ₀ : hg2_Tri G 13) (u : List (hg2_Edge G 13 × Bool))
    (hu : hga_DChain g τ₀ u τ₀) (hun : 0 < u.length) (q : Fin u.length → ℝ → T)
    (hqc : ∀ j, Continuous (q j)) (hm : ∀ j, hga_dWinDir D u[j.1] 1 = q j 0)
    (hqch : ∀ j, b6m_pathChain (hga_unitPath (q j) (hqc j)) =
      hga_TL (D.tri (hga_dEnd g u[j.1])) (hga_dEndPt u[j.1])
        (hga_dStartPt u[(hga_finSucc u.length hun j).1]))
    (z : Fin u.length → T)
    (hP : ∀ j, b3A_IsGoodPath (E := ℂ) (hga_concat (hga_dWinDir D u[j.1]) (q j)) (z j)
      (z (hga_finSucc u.length hun j))) :
    b6m_pathChain (hga_unitPath (hga_Pieces.ofFin u.length hun _ z hP).loop
        (hga_Pieces.ofFin u.length hun _ z hP).loop_contMDiff.continuous) =
      b6m_chainQuotientMap _ (hga_dWalkChain D u) := by
  rw [hga_Pieces.ofFin_pathChain, ← hga_dual_chain_sum D τ₀ u hu hun]
  apply Finset.sum_congr rfl
  intro j _
  rw [← hqch j]
  exact hga_concat_pathChain (hga_dWinDir_continuous D u[j.1]) (hqc j) (hm j)

theorem hga_primLoop_chain (w : List (hg2_Edge G 13 × Bool)) (hwn : 0 < w.length)
    (r : Fin w.length → ℝ → T)
    (hrc : ∀ l, Continuous (r l)) (hm : ∀ l, hga_pWinDir D w[l.1] 1 = r l 0)
    (hrch : ∀ l, b6m_pathChain (hga_unitPath (r l) (hrc l)) =
      b6m_pathChain (hga_tailPiece D w[l.1]) +
        b6m_pathChain (hga_headPiece D w[(hga_finSucc w.length hwn l).1]))
    (z : Fin w.length → T)
    (hP : ∀ l, b3A_IsGoodPath (E := ℂ) (hga_concat (hga_pWinDir D w[l.1]) (r l)) (z l)
      (z (hga_finSucc w.length hwn l))) :
    b6m_pathChain (hga_unitPath (hga_Pieces.ofFin w.length hwn _ z hP).loop
        (hga_Pieces.ofFin w.length hwn _ z hP).loop_contMDiff.continuous) =
      b6m_chainQuotientMap _ (hga_pWalkChain D w) := by
  rw [hga_Pieces.ofFin_pathChain, ← hga_prim_chain_sum D w hwn]
  apply Finset.sum_congr rfl
  intro l _
  rw [← hrch l]
  exact hga_concat_pathChain (hga_pWinDir_continuous D w[l.1]) (hrc l) (hm l)

variable {D} in
theorem hga_dWinDir_one (hW : hga_WinFacts D) (st : hg2_Edge G 13 × Bool) (q : ℝ → T) {z : T}
    (hq : b3A_IsGoodPath (E := ℂ) q (D.tri (hga_dEnd g st) (hga_dEndPt st)) z) :
    hga_dWinDir D st 1 = q 0 :=
  ((hga_dWinDir_good D hW.dgood st).apply_one).trans hq.apply_zero.symm

variable {D} in
theorem hga_pWinDir_one (hW : hga_WinFacts D) (st : hg2_Edge G 13 × Bool) (r : ℝ → T) {z : T}
    (hr : b3A_IsGoodPath (E := ℂ) r (D.edge st.1 (hga_pEndPar st)) z) :
    hga_pWinDir D st 1 = r 0 :=
  ((hga_pWinDir_good D hW.pgood st).apply_one).trans hr.apply_zero.symm

omit [ChartedSpace ℂ T] [IsManifold 𝓘(ℂ, ℂ) ω T] in
theorem hga_crossing_sum (u w : List (hg2_Edge G 13 × Bool)) :
    ∑ p ∈ Finset.univ.filter (fun p : Fin u.length × Fin w.length ↦ u[p.1.1].1 = w[p.2.1].1),
      hga_sgn u[p.1.1].2 * hga_sgn w[p.2.1].2 = ∑ ε, hga_coef u ε * hga_coef w ε := by
  rw [Finset.sum_filter, hga_coef_mul_sum, Fintype.sum_prod_type]

end LoopChains

/-! ## The glued loops of a cyclic dual walk and a cyclic edge walk -/

section Crossing

open Classical

variable {G : Type} [Group G] [Fintype G] {g : Fin 13 → G} {T : Type} [TopologicalSpace T]
  [ChartedSpace ℂ T] [IsManifold 𝓘(ℂ, ℂ) ω T] [T2Space T]
variable {D : hg8_DeltaMap g T}

/-- **Crossing count for cyclic walks.** For a cyclic dual walk `u` and a cyclic edge walk `w`
there are glued `C¹` loops with the path chains of the two walks, transverse to each other, whose
intersection number is `Σ_ε c_u(ε) c_w(ε)`. -/
theorem hga_walk_crossing (hW : hga_WinFacts D) (τ₀ : hg2_Tri G 13)
    (u : List (hg2_Edge G 13 × Bool)) (hu : hga_DChain g τ₀ u τ₀) (hun : 0 < u.length)
    (v₀ : hg2_Vert g) (w : List (hg2_Edge G 13 × Bool)) (hw : hga_PChain g v₀ w v₀)
    (hwn : 0 < w.length) :
    ∃ A B : hga_Pieces T,
      b6m_pathChain (hga_unitPath A.loop A.loop_contMDiff.continuous) =
          b6m_chainQuotientMap _ (hga_dWalkChain D u) ∧
        b6m_pathChain (hga_unitPath B.loop B.loop_contMDiff.continuous) =
          b6m_chainQuotientMap _ (hga_pWalkChain D w) ∧
        b3_Transverse ℂ A.smoothLoop B.smoothLoop ∧
        b3_intersection ℂ A.smoothLoop B.smoothLoop = ∑ ε, hga_coef u ε * hga_coef w ε := by
  -- the connecting paths of the dual loop, inside open triangles
  have hcon : ∀ j : Fin u.length, ∃ q : ℝ → T,
      b3A_IsGoodPath (E := ℂ) q (D.tri (hga_dEnd g (u.get j)) (hga_dEndPt (u.get j)))
        (D.tri (hga_dStart g (u.get (hga_finSucc u.length hun j)))
          (hga_dStartPt (u.get (hga_finSucc u.length hun j)))) ∧
      (∀ s, ∃ τ c, (∀ k, 0 < Convexity.StdSimplex.weights c k) ∧ q s = D.tri τ c) ∧
      ∃ hq : Continuous q, b6m_pathChain (hga_unitPath q hq) =
        hga_TL (D.tri (hga_dEnd g (u.get j))) (hga_dEndPt (u.get j))
          (hga_dStartPt (u.get (hga_finSucc u.length hun j))) := by
    intro j
    obtain ⟨q, hq, hpts, hc, hch⟩ := hga_tri_connector hW.cells (hga_dEnd g (u.get j))
      _ _ (hga_dEndPt_pos (u.get j)) (hga_dStartPt_pos (u.get (hga_finSucc u.length hun j)))
    have e : hga_dEnd g (u.get j) = hga_dStart g (u.get (hga_finSucc u.length hun j)) :=
      hga_DChain_cyclic g hu hun j
    refine ⟨q, by rw [← e]; exact hq, fun s ↦ ?_, hc, hch⟩
    obtain ⟨c, hc', hs⟩ := hpts s
    exact ⟨_, c, hc', hs⟩
  choose q hq hqpts hqc hqch using hcon
  let PA : Fin u.length → ℝ → T := fun j ↦ hga_concat (hga_dWinDir D (u.get j)) (q j)
  let zA : Fin u.length → T := fun j ↦ D.tri (hga_dStart g (u.get j)) (hga_dStartPt (u.get j))
  have hPA : ∀ j, b3A_IsGoodPath (E := ℂ) (PA j) (zA j) (zA (hga_finSucc u.length hun j)) :=
    fun j ↦ (hga_dWinDir_good D hW.dgood (u.get j)).trans (hq j)
  let K : Set T := ⋃ j, PA j '' Icc 0 1
  have hK : IsClosed K := isClosed_iUnion_of_finite fun j ↦
    (isCompact_Icc.image (hPA j).1.continuous).isClosed
  have hPA_left : ∀ j s, s ≤ 1 / 2 → PA j s = hga_dWinDir D (u.get j) (2 * s) :=
    fun j s h ↦ hga_concat_left _ _ h
  have hPA_right : ∀ j s, 1 / 2 < s → ∃ τ c, (∀ k, 0 < Convexity.StdSimplex.weights c k) ∧
      PA j s = D.tri τ c := fun j s h ↦ by
    rw [show PA j s = q j (2 * s - 1) from hga_concat_right _ _ h]
    exact hqpts j _
  have hKpts : ∀ x ∈ K, ∀ ε θ, x = D.edge ε θ → (θ : ℝ) = (hga_W ε).s := by
    intro x hx ε θ hxe
    obtain ⟨j, hj⟩ := Set.mem_iUnion.1 hx
    obtain ⟨s, -, rfl⟩ := hj
    rcases le_or_gt s (1 / 2) with h | h
    · rw [hPA_left j s h] at hxe
      obtain ⟨e1, e2⟩ := hga_dWinDir_edge hW.cells _ _ _ _ hxe
      rw [e1]; exact e2
    · obtain ⟨τ, c, hc, e⟩ := hPA_right j s h
      exact absurd (e.symm.trans hxe) (hW.cells.tri_edge τ c hc ε θ)
  -- the connecting paths of the primal loop, along the skeleton and off the dual loop
  have hpcon : ∀ l : Fin w.length, ∃ r : ℝ → T,
      b3A_IsGoodPath (E := ℂ) r (D.edge (w.get l).1 (hga_pEndPar (w.get l)))
        (D.edge (w.get (hga_finSucc w.length hwn l)).1 (hga_pStartPar (w.get (hga_finSucc w.length hwn l)))) ∧
      (∀ s, r s ∈ Kᶜ) ∧
      ∃ hr : Continuous r, b6m_pathChain (hga_unitPath r hr) =
        b6m_pathChain (hga_tailPiece D (w.get l)) +
          b6m_pathChain (hga_headPiece D (w.get (hga_finSucc w.length hwn l))) := by
    intro l
    have hab : hga_pEnd g (w.get l) = hga_pStart g (w.get (hga_finSucc w.length hwn l)) :=
      hga_PChain_cyclic g hw hwn l
    obtain ⟨r, hr, hrK, hrc, hrch⟩ := hga_exists_goodPath_approx Kᶜ hK.isOpen_compl
      (hga_unitPath (hga_skelPath D (w.get l) (w.get (hga_finSucc w.length hwn l)))
        (hga_skelPath_continuous hab)) (fun t ht ↦ by
          obtain ⟨ε, θ, he, hne⟩ := hga_skelPath_pts (D := D) (w.get l)
            (w.get (hga_finSucc w.length hwn l)) t
          exact hne (hKpts _ ht ε θ he))
    refine ⟨r, ?_, hrK, hrc, hrch.trans (hga_skelPath_pathChain hab)⟩
    have e0 := hga_skelPath_zero (D := D) (w.get l) (w.get (hga_finSucc w.length hwn l))
    have e1 := hga_skelPath_one (D := D) (w.get l) (w.get (hga_finSucc w.length hwn l))
    change b3A_IsGoodPath (E := ℂ) r (hga_skelPath D _ _ 0) (hga_skelPath D _ _ 1) at hr
    rw [e0, e1] at hr
    exact hr
  choose r hr hrK hrc hrch using hpcon
  let PB : Fin w.length → ℝ → T := fun l ↦ hga_concat (hga_pWinDir D (w.get l)) (r l)
  let zB : Fin w.length → T := fun l ↦ D.edge (w.get l).1 (hga_pStartPar (w.get l))
  have hPB : ∀ l, b3A_IsGoodPath (E := ℂ) (PB l) (zB l) (zB (hga_finSucc w.length hwn l)) :=
    fun l ↦ (hga_pWinDir_good D hW.pgood (w.get l)).trans (hr l)
  have hPB_left : ∀ l t, t ≤ 1 / 2 → PB l t = hga_pWinDir D (w.get l) (2 * t) :=
    fun l t h ↦ hga_concat_left _ _ h
  have hPB_right : ∀ l t, 1 / 2 < t → PB l t ∈ Kᶜ := fun l t h ↦ by
    rw [show PB l t = r l (2 * t - 1) from hga_concat_right _ _ h]
    exact hrK l _
  -- meeting points of the pieces
  have hmeet : ∀ j l, ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, PA j s = PB l t →
      (u.get j).1 = (w.get l).1 ∧ s = 1 / 4 ∧ t = 1 / 4 := by
    intro j l s hs t ht h
    rcases le_or_gt t (1 / 2) with htl | htr
    · rcases le_or_gt s (1 / 2) with hsl | hsr
      · rw [hPA_left j s hsl, hPB_left l t htl] at h
        obtain ⟨e, h1, h2⟩ := hga_dir_cross hW.cells hW.cross _ _ _ _ h
        exact ⟨e, by linarith, by linarith⟩
      · obtain ⟨τ, c, hc, e⟩ := hPA_right j s hsr
        obtain ⟨θ, -, hθ⟩ := hga_pWinDir_pts D (w.get l) (2 * t)
        rw [hPB_left l t htl, hθ] at h
        exact absurd (e.symm.trans h) (hW.cells.tri_edge τ c hc _ _)
    · exact absurd (show PB l t ∈ K from Set.mem_iUnion.2 ⟨j, s, hs, h⟩) (hPB_right l t htr)
  let A := hga_Pieces.ofFin u.length hun PA zA hPA
  let B := hga_Pieces.ofFin w.length hwn PB zB hPB
  let S : Finset (Fin u.length × Fin w.length) :=
    Finset.univ.filter fun p ↦ (u.get p.1).1 = (w.get p.2).1
  have hsign : ∀ p ∈ S, ((SignType.sign (b3_orient ℂ (b3_velocity ℂ T (PA p.1) (1 / 4))
      (b3_velocity ℂ T (PB p.2) (1 / 4)))) : ℤ) = hga_sgn (u.get p.1).2 * hga_sgn (w.get p.2).2 := by
    intro p hp
    have hab : (u.get p.1).1 = (w.get p.2).1 := (Finset.mem_filter.1 hp).2
    have key := hga_dir_sign D (fun ε ↦ (hW.dgood ε).1) (fun ε ↦ (hW.pgood ε).1) hW.sign
      (u.get p.1) (w.get p.2) hab 2 two_pos
    rw [b3Forms_velocity_eq_b3, b3Forms_velocity_eq_b3] at key
    rw [b3Forms_velocity_eq_b3, b3Forms_velocity_eq_b3,
      hga_concat_vel_quarter (hga_dWinDir_good D hW.dgood (u.get p.1)).1,
      hga_concat_vel_quarter (hga_pWinDir_good D hW.pgood (w.get p.2)).1]
    exact key
  have hcross : ∀ p ∈ S, (fun _ ↦ (1 / 4 : ℝ)) p ∈ Ioo (0 : ℝ) 1 ∧ (fun _ ↦ (1 / 4 : ℝ)) p ∈ Ioo (0 : ℝ) 1 ∧
      PA p.1 ((fun _ ↦ (1 / 4 : ℝ)) p) = PB p.2 ((fun _ ↦ (1 / 4 : ℝ)) p) ∧
      (∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, PA p.1 s = PB p.2 t →
        s = (fun _ ↦ (1 / 4 : ℝ)) p ∧ t = (fun _ ↦ (1 / 4 : ℝ)) p) ∧
      b3_orient ℂ (b3_velocity ℂ T (PA p.1) ((fun _ ↦ (1 / 4 : ℝ)) p))
        (b3_velocity ℂ T (PB p.2) ((fun _ ↦ (1 / 4 : ℝ)) p)) ≠ 0 := by
    intro p hp
    have hab : (u.get p.1).1 = (w.get p.2).1 := (Finset.mem_filter.1 hp).2
    have hq4 : (1 / 4 : ℝ) ∈ Ioo (0 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
    refine ⟨hq4, hq4, ?_, fun s hs t ht h ↦ ?_, ?_⟩
    · change PA p.1 (1 / 4) = PB p.2 (1 / 4)
      rw [hPA_left _ _ (by norm_num), hPB_left _ _ (by norm_num),
        show (2 : ℝ) * (1 / 4) = 1 / 2 by norm_num, hga_dWinDir_half, hga_pWinDir_half, hab]
    · obtain ⟨-, h1, h2⟩ := hmeet p.1 p.2 s hs t ht h
      exact ⟨h1, h2⟩
    · intro h0
      have := hsign p hp
      rw [h0, sign_zero] at this
      revert this
      rcases (u.get p.1).2 <;> rcases (w.get p.2).2 <;> simp [hga_sgn]
  have hdisj : ∀ p, p ∉ S → ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, PA p.1 s ≠ PB p.2 t := by
    intro p hp s hs t ht h
    exact hp (Finset.mem_filter.2 ⟨Finset.mem_univ _, (hmeet p.1 p.2 s hs t ht h).1⟩)
  obtain ⟨htr, hint⟩ := hga_glued_crossing_fin u.length w.length hun hwn PA zA hPA PB zB hPB S
    (fun _ ↦ 1 / 4) (fun _ ↦ 1 / 4) hcross hdisj
  have hmA := fun j ↦ hga_dWinDir_one hW _ (q j) (hq j)
  have hmB := fun l ↦ hga_pWinDir_one hW _ (r l) (hr l)
  have c1 := hga_dualLoop_chain D τ₀ u hu hun q hqc hmA hqch zA hPA
  have c2 := hga_primLoop_chain D w hwn r hrc hmB hrch zB hPB
  refine ⟨A, B, c1, c2, htr, hint.trans ?_⟩
  rw [Finset.sum_congr rfl hsign]
  exact hga_crossing_sum u w

end Crossing

end HodgeLean.Foundations.Program
