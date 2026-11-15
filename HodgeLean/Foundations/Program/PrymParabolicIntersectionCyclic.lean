import HodgeLean.Foundations.Program.PrymParabolicIntersectionDecomp

set_option linter.unusedSectionVars false

noncomputable section
open Set Filter Manifold
open scoped Topology ContDiff
namespace HodgeLean.Foundations.Program

attribute [local instance] b3Forms_isManifold_real

/-! ## Concatenation and reversal of paths -/

section Concat

variable {T : Type} [TopologicalSpace T]

/-- The concatenation of two paths `ℝ → T` at `1/2`.
Source: `b3A_IsGoodPath.trans`. -/
def hga_concat (γ δ : ℝ → T) (t : ℝ) : T := if t ≤ 1 / 2 then γ (2 * t) else δ (2 * t - 1)

theorem hga_concat_left (γ δ : ℝ → T) {t : ℝ} (ht : t ≤ 1 / 2) : hga_concat γ δ t = γ (2 * t) :=
  if_pos ht

theorem hga_concat_right (γ δ : ℝ → T) {t : ℝ} (ht : 1 / 2 < t) :
    hga_concat γ δ t = δ (2 * t - 1) :=
  if_neg (not_le.mpr ht)

theorem hga_concat_right' (γ δ : ℝ → T) (h : γ 1 = δ 0) {t : ℝ} (ht : 1 / 2 ≤ t) :
    hga_concat γ δ t = δ (2 * t - 1) := by
  rcases eq_or_lt_of_le ht with h' | h'
  · rw [← h', hga_concat_left γ δ le_rfl]
    norm_num
    exact h
  · exact hga_concat_right γ δ h'

theorem hga_concat_continuous {γ δ : ℝ → T} (hγ : Continuous γ) (hδ : Continuous δ)
    (h : γ 1 = δ 0) : Continuous (hga_concat γ δ) := by
  apply Continuous.if_le (hγ.comp (continuous_const.mul continuous_id))
    (hδ.comp ((continuous_const.mul continuous_id).sub continuous_const)) continuous_id
    continuous_const
  intro t ht
  change γ (2 * t) = δ (2 * t - 1)
  have ht' : t = 1 / 2 := ht
  subst ht'
  norm_num
  exact h

theorem hga_concat_pathChain {γ δ : ℝ → T} (hγ : Continuous γ) (hδ : Continuous δ)
    (h : γ 1 = δ 0) :
    b6m_pathChain (hga_unitPath (hga_concat γ δ) (hga_concat_continuous hγ hδ h)) =
      b6m_pathChain (hga_unitPath γ hγ) + b6m_pathChain (hga_unitPath δ hδ) := by
  have hsub := b6m_pathChain_subdiv (hga_unitPath (hga_concat γ δ) (hga_concat_continuous hγ hδ h))
    0 hga_halfI 1
  rw [b3Rest2_restr_zero_one] at hsub
  rw [hsub]
  congr 1
  · apply hga_pathChain_congr
    intro t
    change hga_concat γ δ ((0 : ℝ) + (t : ℝ) * (1 / 2 - 0)) = γ t
    rw [hga_concat_left γ δ (by nlinarith [t.2.1, t.2.2])]
    congr 1
    ring
  · apply hga_pathChain_congr
    intro t
    change hga_concat γ δ (1 / 2 + (t : ℝ) * (1 - 1 / 2)) = δ t
    rw [hga_concat_right' γ δ h (by nlinarith [t.2.1, t.2.2])]
    congr 1
    ring

theorem hga_reverse_continuous {γ : ℝ → T} (hγ : Continuous γ) :
    Continuous (fun t ↦ γ (1 - t)) := hγ.comp (continuous_const.sub continuous_id)

theorem hga_reverse_pathChain {γ : ℝ → T} (hγ : Continuous γ) :
    b6m_pathChain (hga_unitPath (fun t ↦ γ (1 - t)) (hga_reverse_continuous hγ)) =
      -b6m_pathChain (hga_unitPath γ hγ) := by
  rw [← b6m_pathChain_reverse]
  apply hga_pathChain_congr
  intro t
  change γ (1 - (t : ℝ)) = γ ((1 : ℝ) + (t : ℝ) * (0 - 1))
  congr 1
  ring

end Concat

section ConcatSmooth

variable {T : Type} [TopologicalSpace T] [ChartedSpace ℂ T] [IsManifold 𝓘(ℂ, ℂ) ω T]

theorem hga_concat_velocity_left {γ δ : ℝ → T} (hγ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) 1 γ) {t : ℝ}
    (ht : t < 1 / 2) :
    b3_velocity ℂ T (hga_concat γ δ) t = (2 : ℝ) • b3_velocity ℂ T γ (2 * t) := by
  have heq : hga_concat γ δ =ᶠ[𝓝 t] γ ∘ (fun s ↦ 2 * s + 0) := by
    filter_upwards [Iio_mem_nhds ht] with s hs
    rw [hga_concat_left γ δ (le_of_lt hs)]
    simp
  rw [b3Forms_velocity_eq_b3, b3Forms_velocity_eq_b3, b3Forms_velocity_congr heq,
    b3Forms_velocity_comp_affine hγ, add_zero]
  rfl

theorem hga_reverse_velocity {γ : ℝ → T} (hγ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) 1 γ) (t : ℝ) :
    b3_velocity ℂ T (fun s ↦ γ (1 - s)) t = (-1 : ℝ) • b3_velocity ℂ T γ (1 - t) := by
  have h := b3Forms_velocity_comp_affine (E := ℂ) hγ (-1) 1 t
  have e : (γ ∘ fun s ↦ -1 * s + 1) = fun s ↦ γ (1 - s) := by
    funext s; simp only [Function.comp_apply]; congr 1; ring
  rw [e] at h
  rw [b3Forms_velocity_eq_b3, h, b3Forms_velocity_eq_b3]
  congr 2
  ring

end ConcatSmooth

/-! ## Cyclic families indexed by `Fin n` -/

/-- The residue of an integer modulo `n` as an element of `Fin n`.
Source: `Int.emod`. -/
def hga_finOfInt (n : ℕ) (hn : 0 < n) (k : ℤ) : Fin n :=
  ⟨(k % n).toNat, by
    have h1 := Int.emod_nonneg k (by exact_mod_cast hn.ne' : (n : ℤ) ≠ 0)
    have h2 := Int.emod_lt_of_pos k (by exact_mod_cast hn : (0 : ℤ) < n)
    omega⟩

theorem hga_finOfInt_add (n : ℕ) (hn : 0 < n) (k : ℤ) :
    hga_finOfInt n hn (k + n) = hga_finOfInt n hn k := by
  simp [hga_finOfInt]

theorem hga_finOfInt_val (n : ℕ) (hn : 0 < n) (j : Fin n) :
    hga_finOfInt n hn (j.val : ℤ) = j := by
  apply Fin.ext
  simp only [hga_finOfInt]
  rw [Int.emod_eq_of_lt (by positivity) (by exact_mod_cast j.isLt)]
  simp

/-- The cyclic successor in `Fin n`.
Source: `hga_finOfInt`. -/
def hga_finSucc (n : ℕ) (hn : 0 < n) (j : Fin n) : Fin n := hga_finOfInt n hn ((j.val : ℤ) + 1)

theorem hga_finOfInt_succ (n : ℕ) (hn : 0 < n) (k : ℤ) :
    hga_finOfInt n hn (k + 1) = hga_finSucc n hn (hga_finOfInt n hn k) := by
  apply Fin.ext
  simp only [hga_finSucc, hga_finOfInt]
  have hn' : (n : ℤ) ≠ 0 := by exact_mod_cast hn.ne'
  have h1 := Int.emod_nonneg k hn'
  rw [Int.toNat_of_nonneg h1, Int.emod_add_emod]

theorem hga_finSucc_bijective (n : ℕ) (hn : 0 < n) : Function.Bijective (hga_finSucc n hn) := by
  apply Finite.injective_iff_bijective.mp
  intro a b h
  have h' := congrArg (fun x : Fin n ↦ hga_finOfInt n hn ((x.val : ℤ) + (n - 1))) h
  simp only [hga_finSucc] at h'
  have e : ∀ c : Fin n, hga_finOfInt n hn (((hga_finOfInt n hn ((c.val : ℤ) + 1)).val : ℤ) + (n - 1)) = c := by
    intro c
    apply Fin.ext
    simp only [hga_finOfInt]
    have hn' : (n : ℤ) ≠ 0 := by exact_mod_cast hn.ne'
    have hpos : (0 : ℤ) < n := by exact_mod_cast hn
    rw [Int.toNat_of_nonneg (Int.emod_nonneg _ hn'), Int.emod_add_emod]
    rw [show (c.val : ℤ) + 1 + (n - 1) = c.val + n by ring, Int.add_emod_right,
      Int.emod_eq_of_lt (by positivity) (by exact_mod_cast c.isLt)]
    simp
  rw [e, e] at h'
  exact h'

theorem hga_sum_finSucc {M : Type} [AddCommMonoid M] (n : ℕ) (hn : 0 < n) (f : Fin n → M) :
    ∑ j, f (hga_finSucc n hn j) = ∑ j, f j :=
  Fintype.sum_bijective _ (hga_finSucc_bijective n hn) _ _ (fun _ ↦ rfl)

variable {T : Type} [TopologicalSpace T] [ChartedSpace ℂ T]

/-- A cyclic family of good paths indexed by `Fin n`.
Source: `hga_Pieces`. -/
def hga_Pieces.ofFin (n : ℕ) (hn : 0 < n) (P : Fin n → ℝ → T) (z : Fin n → T)
    (hP : ∀ j, b3A_IsGoodPath (E := ℂ) (P j) (z j) (z (hga_finSucc n hn j))) : hga_Pieces T where
  N := n
  pos := hn
  γ := fun k ↦ P (hga_finOfInt n hn k)
  z := fun k ↦ z (hga_finOfInt n hn k)
  γ_add := fun k ↦ by simp only [hga_finOfInt_add]
  z_add := fun k ↦ by simp only [hga_finOfInt_add]
  good := fun k ↦ by
    simp only [hga_finOfInt_succ]
    exact hP _

variable [IsManifold 𝓘(ℂ, ℂ) ω T]

namespace hga_Pieces

theorem ofFin_loop (n : ℕ) (hn : 0 < n) (P : Fin n → ℝ → T) (z : Fin n → T)
    (hP : ∀ j, b3A_IsGoodPath (E := ℂ) (P j) (z j) (z (hga_finSucc n hn j))) (j : Fin n)
    {σ : ℝ} (hσ : σ ∈ Icc (0 : ℝ) 1) :
    (ofFin n hn P z hP).loop (((j.val : ℤ) + σ) / n) = P j σ := by
  have := (ofFin n hn P z hP).loop_apply (j.val : ℤ) hσ
  change (ofFin n hn P z hP).loop (((j.val : ℤ) + σ) / (ofFin n hn P z hP).N) = _
  rw [this]
  change P (hga_finOfInt n hn (j.val : ℤ)) σ = P j σ
  rw [hga_finOfInt_val]

theorem ofFin_pathChain (n : ℕ) (hn : 0 < n) (P : Fin n → ℝ → T) (z : Fin n → T)
    (hP : ∀ j, b3A_IsGoodPath (E := ℂ) (P j) (z j) (z (hga_finSucc n hn j))) :
    b6m_pathChain (hga_unitPath (ofFin n hn P z hP).loop
        (ofFin n hn P z hP).loop_contMDiff.continuous) =
      ∑ j, b6m_pathChain (hga_unitPath (P j) (hP j).1.continuous) := by
  rw [pathChain_loop]
  change ∑ k ∈ Finset.range n, _ = _
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro j _
  apply hga_pathChain_congr
  intro t
  change P (hga_finOfInt n hn ((j.val : ℕ) : ℤ)) t = P j t
  rw [hga_finOfInt_val]

end hga_Pieces

/-- **Crossings of cyclic families** indexed by `Fin n`. -/
theorem hga_glued_crossing_fin (nA nB : ℕ) (hA : 0 < nA) (hB : 0 < nB)
    (PA : Fin nA → ℝ → T) (zA : Fin nA → T)
    (hPA : ∀ j, b3A_IsGoodPath (E := ℂ) (PA j) (zA j) (zA (hga_finSucc nA hA j)))
    (PB : Fin nB → ℝ → T) (zB : Fin nB → T)
    (hPB : ∀ j, b3A_IsGoodPath (E := ℂ) (PB j) (zB j) (zB (hga_finSucc nB hB j)))
    (S : Finset (Fin nA × Fin nB)) (σ θ : Fin nA × Fin nB → ℝ)
    (hcross : ∀ p ∈ S, σ p ∈ Ioo (0 : ℝ) 1 ∧ θ p ∈ Ioo (0 : ℝ) 1 ∧
      PA p.1 (σ p) = PB p.2 (θ p) ∧
      (∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, PA p.1 s = PB p.2 t → s = σ p ∧ t = θ p) ∧
      b3_orient ℂ (b3_velocity ℂ T (PA p.1) (σ p)) (b3_velocity ℂ T (PB p.2) (θ p)) ≠ 0)
    (hdisj : ∀ p, p ∉ S → ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, PA p.1 s ≠ PB p.2 t) :
    b3_Transverse ℂ (hga_Pieces.ofFin nA hA PA zA hPA).smoothLoop
        (hga_Pieces.ofFin nB hB PB zB hPB).smoothLoop ∧
      b3_intersection ℂ (hga_Pieces.ofFin nA hA PA zA hPA).smoothLoop
          (hga_Pieces.ofFin nB hB PB zB hPB).smoothLoop =
        ∑ p ∈ S, ((SignType.sign (b3_orient ℂ (b3_velocity ℂ T (PA p.1) (σ p))
          (b3_velocity ℂ T (PB p.2) (θ p))) : SignType) : ℤ) := by
  classical
  obtain ⟨e, he⟩ : ∃ e : Fin nA × Fin nB ↪ ℤ × ℤ, ∀ p, e p = ((p.1.val : ℤ), (p.2.val : ℤ)) :=
    ⟨⟨fun p ↦ ((p.1.val : ℤ), (p.2.val : ℤ)), fun p q h ↦ by
      simp only [Prod.mk.injEq, Nat.cast_inj] at h
      exact Prod.ext (Fin.ext h.1) (Fin.ext h.2)⟩, fun _ ↦ rfl⟩
  let back : ℤ × ℤ → Fin nA × Fin nB := fun k ↦ (hga_finOfInt nA hA k.1, hga_finOfInt nB hB k.2)
  have hback' : ∀ p : Fin nA × Fin nB, back ((p.1.val : ℤ), (p.2.val : ℤ)) = p := fun p ↦ by
    simp only [back, hga_finOfInt_val]
  have hNA : (hga_Pieces.ofFin nA hA PA zA hPA).N = nA := rfl
  have hNB : (hga_Pieces.ofFin nB hB PB zB hPB).N = nB := rfl
  have hγA : ∀ k, (hga_Pieces.ofFin nA hA PA zA hPA).γ k = PA (hga_finOfInt nA hA k) := fun _ ↦ rfl
  have hγB : ∀ k, (hga_Pieces.ofFin nB hB PB zB hPB).γ k = PB (hga_finOfInt nB hB k) := fun _ ↦ rfl
  have h := hga_glued_crossing (hga_Pieces.ofFin nA hA PA zA hPA) (hga_Pieces.ofFin nB hB PB zB hPB)
    (S.map e) (fun k ↦ σ (back k)) (fun k ↦ θ (back k)) ?_ ?_ ?_
  · refine ⟨h.1, ?_⟩
    rw [h.2, Finset.sum_map]
    apply Finset.sum_congr rfl
    intro p _
    have hFA : (hga_Pieces.ofFin nA hA PA zA hPA).γ (e p).1 = PA p.1 := by
      rw [hγA, he]; simp only [hga_finOfInt_val]
    have hFB : (hga_Pieces.ofFin nB hB PB zB hPB).γ (e p).2 = PB p.2 := by
      rw [hγB, he]; simp only [hga_finOfInt_val]
    have hb : back (e p) = p := by rw [he]; exact hback' p
    rw [hFA, hFB, hb]
  · intro k hk
    obtain ⟨p, hp, rfl⟩ := Finset.mem_map.mp hk
    rw [he, hNA, hNB]
    dsimp only
    exact ⟨⟨by positivity, by exact_mod_cast p.1.isLt⟩, ⟨by positivity, by exact_mod_cast p.2.isLt⟩⟩
  · intro k hk
    obtain ⟨p, hp, rfl⟩ := Finset.mem_map.mp hk
    have hFA : (hga_Pieces.ofFin nA hA PA zA hPA).γ (e p).1 = PA p.1 := by
      rw [hγA, he]; simp only [hga_finOfInt_val]
    have hFB : (hga_Pieces.ofFin nB hB PB zB hPB).γ (e p).2 = PB p.2 := by
      rw [hγB, he]; simp only [hga_finOfInt_val]
    have hb : back (e p) = p := by rw [he]; exact hback' p
    rw [hFA, hFB, hb]
    exact hcross p hp
  · intro k l hk0 hk1 hl0 hl1 hkl
    rw [hNA] at hk1
    rw [hNB] at hl1
    have hpk : (hga_finOfInt nA hA k, hga_finOfInt nB hB l) ∉ S := by
      intro hmem
      apply hkl
      apply Finset.mem_map.mpr
      refine ⟨_, hmem, ?_⟩
      rw [he, Prod.mk.injEq]
      constructor
      · simp only [hga_finOfInt]
        rw [Int.emod_eq_of_lt hk0 hk1, Int.toNat_of_nonneg hk0]
      · simp only [hga_finOfInt]
        rw [Int.emod_eq_of_lt hl0 hl1, Int.toNat_of_nonneg hl0]
    intro s hs t ht
    rw [hγA, hγB]
    exact hdisj _ hpk s hs t ht

/-! ## Cyclic walks -/

section WalkLists

variable {G : Type} [Group G] (g : Fin 13 → G)

open Classical in
theorem hga_coef_eq_sum (L : List (hg2_Edge G 13 × Bool)) (ε : hg2_Edge G 13) :
    hga_coef L ε = ∑ i : Fin L.length, (if L[i.1].1 = ε then hga_sgn L[i.1].2 else 0) := by
  rw [Fin.sum_univ_fun_getElem L (fun st ↦ if st.1 = ε then hga_sgn st.2 else 0)]
  rfl

theorem hga_DChain_succ {τ τ' : hg2_Tri G 13} {L : List (hg2_Edge G 13 × Bool)}
    (h : hga_DChain g τ L τ') :
    (∀ i (hi : i + 1 < L.length), hga_dEnd g L[i] = hga_dStart g L[i + 1]) ∧
      (∀ (h0 : 0 < L.length), hga_dStart g L[0] = τ ∧ hga_dEnd g L[L.length - 1] = τ') := by
  induction L generalizing τ with
  | nil => exact ⟨fun i hi ↦ by simp at hi, fun h0 ↦ by simp at h0⟩
  | cons st L ih =>
    obtain ⟨h1, h2⟩ := h
    obtain ⟨ih1, ih2⟩ := ih h2
    refine ⟨fun i hi ↦ ?_, fun _ ↦ ⟨h1, ?_⟩⟩
    · rcases i with _ | i
      · simp only [List.getElem_cons_zero, List.getElem_cons_succ]
        rcases L with _ | ⟨st', L'⟩
        · simp at hi
        · exact ((ih2 (by simp)).1).symm
      · simp only [List.getElem_cons_succ]
        exact ih1 i (by simp at hi; omega)
    · rcases L with _ | ⟨st', L'⟩
      · simpa [hga_DChain] using h2
      · simp only [List.length_cons, Nat.add_sub_cancel, List.getElem_cons_succ]
        have := (ih2 (by simp)).2
        simpa using this

theorem hga_PChain_succ {v v' : hg2_Vert g} {L : List (hg2_Edge G 13 × Bool)}
    (h : hga_PChain g v L v') :
    (∀ i (hi : i + 1 < L.length), hga_pEnd g L[i] = hga_pStart g L[i + 1]) ∧
      (∀ (h0 : 0 < L.length), hga_pStart g L[0] = v ∧ hga_pEnd g L[L.length - 1] = v') := by
  induction L generalizing v with
  | nil => exact ⟨fun i hi ↦ by simp at hi, fun h0 ↦ by simp at h0⟩
  | cons st L ih =>
    obtain ⟨h1, h2⟩ := h
    obtain ⟨ih1, ih2⟩ := ih h2
    refine ⟨fun i hi ↦ ?_, fun _ ↦ ⟨h1, ?_⟩⟩
    · rcases i with _ | i
      · simp only [List.getElem_cons_zero, List.getElem_cons_succ]
        rcases L with _ | ⟨st', L'⟩
        · simp at hi
        · exact ((ih2 (by simp)).1).symm
      · simp only [List.getElem_cons_succ]
        exact ih1 i (by simp at hi; omega)
    · rcases L with _ | ⟨st', L'⟩
      · simpa [hga_PChain] using h2
      · simp only [List.length_cons, Nat.add_sub_cancel, List.getElem_cons_succ]
        have := (ih2 (by simp)).2
        simpa using this

theorem hga_finSucc_val (n : ℕ) (hn : 0 < n) (j : Fin n) :
    (hga_finSucc n hn j).val = if j.val + 1 < n then j.val + 1 else 0 := by
  simp only [hga_finSucc, hga_finOfInt]
  split_ifs with h
  · rw [Int.emod_eq_of_lt (by positivity) (by exact_mod_cast h)]; simp
  · have : j.val + 1 = n := by have := j.isLt; omega
    rw [show (j.val : ℤ) + 1 = n by exact_mod_cast this, Int.emod_self]; simp

theorem hga_DChain_cyclic {τ : hg2_Tri G 13} {L : List (hg2_Edge G 13 × Bool)}
    (h : hga_DChain g τ L τ) (hn : 0 < L.length) (j : Fin L.length) :
    hga_dEnd g L[j.1] = hga_dStart g L[(hga_finSucc L.length hn j).1] := by
  obtain ⟨h1, h2⟩ := hga_DChain_succ g h
  have hv := hga_finSucc_val L.length hn j
  split_ifs at hv with hj
  · simp only [hv]
    exact h1 j.1 hj
  · simp only [hv]
    have : j.1 = L.length - 1 := by have := j.isLt; omega
    simp only [this]
    rw [(h2 hn).2, (h2 hn).1]

theorem hga_PChain_cyclic {v : hg2_Vert g} {L : List (hg2_Edge G 13 × Bool)}
    (h : hga_PChain g v L v) (hn : 0 < L.length) (j : Fin L.length) :
    hga_pEnd g L[j.1] = hga_pStart g L[(hga_finSucc L.length hn j).1] := by
  obtain ⟨h1, h2⟩ := hga_PChain_succ g h
  have hv := hga_finSucc_val L.length hn j
  split_ifs at hv with hj
  · simp only [hv]
    exact h1 j.1 hj
  · simp only [hv]
    have : j.1 = L.length - 1 := by have := j.isLt; omega
    simp only [this]
    rw [(h2 hn).2, (h2 hn).1]

end WalkLists

end HodgeLean.Foundations.Program
