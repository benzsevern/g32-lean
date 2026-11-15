import HodgeLean.Foundations.Program.RadialTransportIsotopy

/-! # Relative endpoint comparison over configuration homotopies

Finite normalized labels lift to a sphere family over the square. Endpoint
comparison preserves every label throughout, including infinity.
HC no distance; AV milestone no distance.
-/

noncomputable section
namespace HodgeLean.Foundations.Program

def rtc_fixed_homotopy {X J : Type} [TopologicalSpace X]
    (f g : C(X, X)) (p q : J → X)
    (K : C(unitInterval × X, X))
    (hbij : ∀ t, Function.Bijective (fun z ↦ K (t, z)))
    (h0 : ∀ z, K (0, z) = f z) (h1 : ∀ z, K (1, z) = g z)
    (hm : ∀ t j, K (t, p j) = q j) :
    ContinuousMap.HomotopyWith f g
      (fun k ↦ Function.Bijective k ∧ ∀ j, k (p j) = q j) where
  toContinuousMap := K
  map_zero_left := h0
  map_one_left := h1
  prop' := fun t ↦ ⟨hbij t, hm t⟩

theorem rtc_finite_branch (c : Fin 10 → ℂ) (i : Fin 12) :
    ((Fin.append c ![0, 1]) i : OnePoint ℂ) = b6_branch c i.castSucc := by
  fin_cases i <;> rfl

theorem rtc_chart_square (Q : C(unitInterval × unitInterval, b6_chart)) :
    ∃ F : C((unitInterval × unitInterval) × OnePoint ℂ, OnePoint ℂ),
      (∀ s t, Function.Bijective (fun z ↦ F ((s, t), z))) ∧
      (∀ s z, F ((s, 0), z) = z) ∧
      ∀ s t j, F ((s, t), b6_branch (Q (s, 0)).val j) =
        b6_branch (Q (s, t)).val j := by
  let P : unitInterval × unitInterval → Fin 12 → ℂ :=
    fun q ↦ Fin.append (Q q).val ![0, 1]
  have hP : Continuous P := by
    apply continuous_pi
    intro j
    fin_cases j <;>
      simp [P, Fin.append, Fin.addCases] <;>
      first | exact continuous_const |
        exact (continuous_apply _).comp (continuous_subtype_val.comp Q.continuous)
  have hinj (q : unitInterval × unitInterval) : Function.Injective (P q) := by
    intro i j hij
    have h := congrArg ((↑) : ℂ → OnePoint ℂ) hij
    rw [rtc_finite_branch, rtc_finite_branch] at h
    exact Fin.castSucc_injective _ ((Q q).property h)
  obtain ⟨F, hb, h0, hm, hi⟩ := rtc_square_sphere P hP hinj
  refine ⟨F, hb, h0, ?_⟩
  intro s t j
  refine Fin.lastCases ?_ (fun i ↦ ?_) j
  · simpa only [mr_branch_last] using hi s t
  · simpa only [← rtc_finite_branch] using hm s t i

theorem rtc_square_end_comparison {X J : Type}
    [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (F : C((unitInterval × unitInterval) × X, X))
    (hf : ∀ s t, Function.Bijective (fun z ↦ F ((s, t), z)))
    (hf0 : ∀ s z, F ((s, 0), z) = z)
    (H G : C(unitInterval × X, X))
    (hH : ∀ t, Function.Bijective (fun z ↦ H (t, z)))
    (hG : ∀ t, Function.Bijective (fun z ↦ G (t, z)))
    (hH0 : ∀ z, H (0, z) = z) (hG0 : ∀ z, G (0, z) = z)
    (p q : J → X)
    (hmH : ∀ t j, H (t, p j) = F ((0, t), p j))
    (hmG : ∀ t j, G (t, p j) = F ((1, t), p j))
    (hmF : ∀ s j, F ((s, 1), p j) = q j) :
    ∃ K : C(unitInterval × X, X),
      (∀ t, Function.Bijective (fun z ↦ K (t, z))) ∧
      (∀ z, K (0, z) = H (1, z)) ∧
      (∀ z, K (1, z) = G (1, z)) ∧
      (∀ t j, K (t, p j) = q j) := by
  let F0 : C(unitInterval × X, X) :=
    ⟨fun w ↦ F ((0, w.1), w.2),
      F.continuous.comp ((continuous_const.prodMk continuous_fst).prodMk continuous_snd)⟩
  let F1 : C(unitInterval × X, X) :=
    ⟨fun w ↦ F ((1, w.1), w.2),
      F.continuous.comp ((continuous_const.prodMk continuous_fst).prodMk continuous_snd)⟩
  let M : C(unitInterval × X, X) :=
    ⟨fun w ↦ F ((w.1, 1), w.2),
      F.continuous.comp ((continuous_fst.prodMk continuous_const).prodMk continuous_snd)⟩
  obtain ⟨K0, hb0, hz0, ho0, hm0⟩ := rtc_same_tracks H F0 hH (hf 0) hH0
    (hf0 0) p (fun t j ↦ F ((0, t), p j)) hmH (fun _ _ ↦ rfl)
  obtain ⟨K1, hb1, hz1, ho1, hm1⟩ := rtc_same_tracks F1 G (hf 1) hG
    (hf0 1) hG0 p (fun t j ↦ F ((1, t), p j)) (fun _ _ ↦ rfl) hmG
  let h := rtc_fixed_homotopy (H.curry 1) (F0.curry 1) p q K0 hb0 hz0 ho0
    (fun t j ↦ (hm0 t j).trans (hmF 0 j))
  let m := rtc_fixed_homotopy (F0.curry 1) (F1.curry 1) p q M (fun s ↦ hf s 1)
    (fun _ ↦ rfl) (fun _ ↦ rfl) hmF
  let g := rtc_fixed_homotopy (F1.curry 1) (G.curry 1) p q K1 hb1 hz1 ho1
    (fun t j ↦ (hm1 t j).trans (hmF 1 j))
  let k := (h.trans m).trans g
  exact ⟨k.toContinuousMap, fun t ↦ (k.prop t).1,
    k.map_zero_left, k.map_one_left, fun t ↦ (k.prop t).2⟩

theorem rtc_configuration_comparison {a b : b6_chart}
    (α α' : Path a b) (hα : α.Homotopic α')
    (H G : C(unitInterval × OnePoint ℂ, OnePoint ℂ))
    (hH : ∀ t, Function.Bijective (fun z ↦ H (t, z)))
    (hG : ∀ t, Function.Bijective (fun z ↦ G (t, z)))
    (hH0 : ∀ z, H (0, z) = z) (hG0 : ∀ z, G (0, z) = z)
    (hHm : ∀ t j, H (t, b6_branch a.val j) = b6_branch (α t).val j)
    (hGm : ∀ t j, G (t, b6_branch a.val j) = b6_branch (α' t).val j) :
    ∃ K : C(unitInterval × OnePoint ℂ, OnePoint ℂ),
      (∀ t, Function.Bijective (fun z ↦ K (t, z))) ∧
      (∀ z, K (0, z) = H (1, z)) ∧
      (∀ z, K (1, z) = G (1, z)) ∧
      (∀ t j, K (t, b6_branch a.val j) = b6_branch b.val j) := by
  obtain ⟨D⟩ := hα
  obtain ⟨F, hb, hz, hm⟩ := rtc_chart_square D.toContinuousMap
  have hmark (s t : unitInterval) (j : Fin 13) :
      F ((s, t), b6_branch a.val j) = b6_branch (D (s, t)).val j := by
    have h := hm s t j
    change F ((s, t), b6_branch (D (s, 0)).val j) =
      b6_branch (D (s, t)).val j at h
    rw [D.source] at h
    exact h
  exact rtc_square_end_comparison F hb hz H G
    hH hG hH0 hG0 (b6_branch a.val) (b6_branch b.val)
    (fun t j ↦ by
      have hd : D (0, t) = α t := D.map_zero_left t
      rw [hmark, hd]
      exact hHm t j)
    (fun t j ↦ by
      have hd : D (1, t) = α' t := D.map_one_left t
      rw [hmark, hd]
      exact hGm t j)
    (fun s j ↦ by rw [hmark, D.target])

end HodgeLean.Foundations.Program
