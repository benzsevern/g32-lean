import HodgeLean.Foundations.Program.PullbackMonodromyDefs

/-! # Pullback monodromy statements

Implication from the printed rational pullback to its surjective group representation,
and from finite signed words to Hurwitz-orbit certificates. The selected-component
comparison requires further geometric word data. HC no distance; AV milestone no distance.
-/

noncomputable section
open Polynomial HodgeLean.Papers
namespace HodgeLean.Foundations.Program

/-- The fibre polynomial `P_ε` as a polynomial.
Source: G32 v0.16, §5.2, P₅ and P₋₇; `b65r_P`. -/
def b65s_poly (ε : ℂ) : ℂ[X] := X ^ 2 * (X - C 3) ^ 4 - C ε * (X - C 1) ^ 3 * (X + C 2) ^ 3

theorem b65s_poly_eval (ε z : ℂ) : (b65s_poly ε).eval z = b65r_P ε z := by
  simp [b65s_poly, b65r_P]

theorem b65s_poly_deriv_eval (ε z : ℂ) : (derivative (b65s_poly ε)).eval z =
    2 * z * (z - 3) ^ 4 + 4 * z ^ 2 * (z - 3) ^ 3 -
      ε * (3 * (z - 1) ^ 2 * (z + 2) ^ 3 + 3 * (z - 1) ^ 3 * (z + 2) ^ 2) := by
  simp [b65s_poly, derivative_mul, derivative_pow]
  ring

theorem b65s_poly_natDegree (ε : ℂ) (hε : ε ≠ 1) : (b65s_poly ε).natDegree = 6 := by
  unfold b65s_poly
  have : (1 : ℂ) - ε ≠ 0 := sub_ne_zero.mpr hε.symm
  compute_degree!

theorem b65s_poly_ne_zero (ε : ℂ) (hε : ε ≠ 1) : b65s_poly ε ≠ 0 := by
  intro h
  have := b65s_poly_natDegree ε hε
  rw [h, natDegree_zero] at this
  exact absurd this (by norm_num)

theorem b65s_P5_simple (t : ℂ) (h1 : b65r_P 5 t = 0)
    (h2 : 2 * t * (t - 3) ^ 4 + 4 * t ^ 2 * (t - 3) ^ 3 -
      5 * (3 * (t - 1) ^ 2 * (t + 2) ^ 3 + 3 * (t - 1) ^ 3 * (t + 2) ^ 2) = 0) : False := by
  unfold b65r_P at h1
  have : (1 : ℂ) = 0 := by
    linear_combination
      ((495343/12437500) + (1159377/62187500)*t + (2103241/49750000)*t^2 +
        (-4103273/124375000)*t^3 + (-81697/15546875)*t^4) * h1 +
      ((122937/12437500) + (-263533/24875000)*t + (-604787/746250000)*t^2 +
        (-8535893/746250000)*t^3 + (2419273/373125000)*t^4 + (81697/93281250)*t^5) * h2
  exact one_ne_zero this

theorem b65s_Pneg7_simple (t : ℂ) (h1 : b65r_P (-7) t = 0)
    (h2 : 2 * t * (t - 3) ^ 4 + 4 * t ^ 2 * (t - 3) ^ 3 -
      (-7) * (3 * (t - 1) ^ 2 * (t + 2) ^ 3 + 3 * (t - 1) ^ 3 * (t + 2) ^ 2) = 0) : False := by
  unfold b65r_P at h1
  have : (1 : ℂ) = 0 := by
    linear_combination
      ((29115197/5823912500) + (72012381/831987500)*t + (-360360229/23295650000)*t^2 +
        (-80859047/11647825000)*t^3 + (-9671938/1455978125)*t^4) * h1 +
      ((12677489/831987500) + (94108113/11647825000)*t + (-1898963657/69886950000)*t^2 +
        (288131341/69886950000)*t^3 + (47683477/34943475000)*t^4 +
        (4835969/4367934375)*t^5) * h2
  exact one_ne_zero this

theorem b65s_roots_card (ε : ℂ) (hε : ε ≠ 1)
    (hs : ∀ t : ℂ, b65r_P ε t = 0 → (derivative (b65s_poly ε)).eval t = 0 → False) :
    (b65s_poly ε).roots.toFinset.card = 6 := by
  classical
  have hnd : (b65s_poly ε).roots.Nodup := by
    rw [Multiset.nodup_iff_count_le_one]
    intro a
    rw [count_roots]
    by_contra hlt
    obtain ⟨h1, h2⟩ := (one_lt_rootMultiplicity_iff_isRoot (b65s_poly_ne_zero ε hε)).mp (lt_of_not_ge hlt)
    exact hs a (by rw [← b65s_poly_eval]; exact h1) h2
  rw [Multiset.toFinset_card_of_nodup hnd, IsAlgClosed.card_roots_eq_natDegree,
    b65s_poly_natDegree ε hε]

theorem b65s_mem_roots (ε z : ℂ) (hε : ε ≠ 1) :
    z ∈ (b65s_poly ε).roots.toFinset ↔ b65r_P ε z = 0 := by
  rw [Multiset.mem_toFinset, mem_roots (b65s_poly_ne_zero ε hε), IsRoot, b65s_poly_eval]

theorem b65s_card5 : (b65s_poly 5).roots.toFinset.card = 6 :=
  b65s_roots_card 5 (by norm_num) fun t h1 h2 ↦
    b65s_P5_simple t h1 (by rw [b65s_poly_deriv_eval] at h2; exact h2)

theorem b65s_cardneg7 : (b65s_poly (-7)).roots.toFinset.card = 6 :=
  b65s_roots_card (-7) (by norm_num) fun t h1 h2 ↦
    b65s_Pneg7_simple t h1 (by rw [b65s_poly_deriv_eval] at h2; exact h2)

theorem b65s_fibres_disjoint (t : ℂ) (h5 : b65r_P 5 t = 0) (h7 : b65r_P (-7) t = 0) : False := by
  unfold b65r_P at h5 h7
  have hD : (t - 1) ^ 3 * (t + 2) ^ 3 = 0 := by linear_combination (h7 - h5) / 12
  have hN : t ^ 2 * (t - 3) ^ 4 = 0 := by linear_combination h5 + 5 * hD
  rcases mul_eq_zero.mp hD with h | h <;> rcases mul_eq_zero.mp hN with k | k
  all_goals
    have h' := pow_eq_zero_iff (by norm_num) |>.mp h
    have k' := pow_eq_zero_iff (by norm_num) |>.mp k
    first
    | (rw [sub_eq_zero] at h'; rw [h'] at k'; norm_num at k')
    | (rw [add_eq_zero_iff_eq_neg] at h'; rw [h'] at k'; norm_num at k')

theorem b65s_fibre_ne_zero (ε : ℂ) (hε : ε ≠ 0) : b65r_P ε 0 ≠ 0 := by
  simp [b65r_P]
  exact hε

/-- The thirteen finite branch points as a finite set.
Source: G32 v0.16, §5.2, Lemma surj; `b65s_branch`. -/
def b65s_branchFinset : Finset ℂ :=
  insert 0 ((b65s_poly 5).roots.toFinset ∪ (b65s_poly (-7)).roots.toFinset)

theorem b65s_mem_branchFinset (z : ℂ) :
    z ∈ b65s_branchFinset ↔ z = 0 ∨ b65r_P 5 z = 0 ∨ b65r_P (-7) z = 0 := by
  rw [b65s_branchFinset, Finset.mem_insert, Finset.mem_union,
    b65s_mem_roots 5 z (by norm_num), b65s_mem_roots (-7) z (by norm_num)]

theorem b65s_branchFinset_card : b65s_branchFinset.card = 13 := by
  classical
  rw [b65s_branchFinset, Finset.card_insert_of_notMem, Finset.card_union_of_disjoint,
    b65s_card5, b65s_cardneg7]
  · rw [Finset.disjoint_left]
    intro z h5 h7
    exact b65s_fibres_disjoint z ((b65s_mem_roots 5 z (by norm_num)).mp h5)
      ((b65s_mem_roots (-7) z (by norm_num)).mp h7)
  · rw [Finset.mem_union, b65s_mem_roots 5 0 (by norm_num), b65s_mem_roots (-7) 0 (by norm_num)]
    rintro (h | h)
    · exact b65s_fibre_ne_zero 5 (by norm_num) h
    · exact b65s_fibre_ne_zero (-7) (by norm_num) h

theorem b65s_branch_eq : b65s_branch = (fun z : ℂ ↦ (z : OnePoint ℂ)) '' ↑b65s_branchFinset := by
  ext p
  simp only [b65s_branch, Set.mem_ofPred_eq, Set.mem_image, Finset.mem_coe, b65s_mem_branchFinset]
  constructor
  · rintro ⟨z, rfl, hz⟩; exact ⟨z, hz, rfl⟩
  · rintro ⟨z, hz, rfl⟩; exact ⟨z, rfl, hz⟩

theorem b65s_branch_count_aux  :
    Nat.card ↥b65s_branch = 13 := by
  rw [b65s_branch_eq, Nat.card_image_of_injective OnePoint.coe_injective, Nat.card_coe_set_eq,
    Set.ncard_coe_finset, b65s_branchFinset_card]

/-- Group element of a positive word in the printed generators.
Source: G32 v0.16, Appendix A; `b4b_generators`. -/
def b65s_gw (w : List (Fin 4)) : b4b_Group := (w.map b4b_generators).prod

/-- Integral matrix of a positive word, in the lattice basis of the order certificate.
Source: `HurwitzPrymRex_g32SOne`; `HurwitzPrymRex_g32_G_eq`. -/
def b65s_ew (w : List (Fin 4)) : HurwitzPrymRex_Mat :=
  w.foldr (fun i M ↦ HurwitzPrymRex_mmul (HurwitzPrymRex_nth HurwitzPrymRex_g32SOne i) M)
    HurwitzPrymRex_mone

theorem b65s_gw_append (u v : List (Fin 4)) : b65s_gw (u ++ v) = b65s_gw u * b65s_gw v := by
  simp [b65s_gw]

theorem b65s_gw_matrix (w : List (Fin 4)) :
    b4b_toMatrix (b65s_gw w) =
      HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega (b65s_ew w)) := by
  induction w with
  | nil =>
      simp [b65s_gw, b65s_ew, HurwitzPrymRex_evM_mone]
  | cons i w ih =>
      have hi : b4b_toMatrix (b4b_generators i) =
          HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega
            (HurwitzPrymRex_nth HurwitzPrymRex_g32SOne i)) := by
        fin_cases i
        · exact HurwitzPrymRex_g32_conj0.symm
        · exact HurwitzPrymRex_g32_conj1.symm
        · exact HurwitzPrymRex_g32_conj2.symm
        · exact HurwitzPrymRex_g32_conj3.symm
      have hw : b65s_gw (i :: w) = b4b_generators i * b65s_gw w := by simp [b65s_gw]
      rw [hw, map_mul, ih, hi, ← map_mul, ← HurwitzPrymRex_evM_mmul g32h_omega_sq_add]
      rfl

theorem b65s_gw_eq {u v : List (Fin 4)}
    (h : HurwitzPrymRex_mbeq (b65s_ew u) (b65s_ew v) = true) : b65s_gw u = b65s_gw v := by
  apply Subtype.val_injective
  change b4b_toMatrix (b65s_gw u) = b4b_toMatrix (b65s_gw v)
  rw [b65s_gw_matrix, b65s_gw_matrix, HurwitzPrymRex_mbeq_sound h]

/-- An element of order nine: `r₁ r₁ y x`.
Source: computed in the integral realization of `HurwitzPrymRex_g32SOne`. -/
def b65s_nineWord : List (Fin 4) := [0, 0, 3, 2]

/-- The cube of the order-nine word.
Source: `b65s_nineWord`. -/
def b65s_cubeWord : List (Fin 4) := b65s_nineWord ++ b65s_nineWord ++ b65s_nineWord

theorem b65s_nine_pow : (b65s_gw b65s_nineWord) ^ 9 = 1 := by
  have h := b65s_gw_eq (u := b65s_cubeWord ++ b65s_cubeWord ++ b65s_cubeWord) (v := [])
    (by decide +kernel)
  simp only [b65s_cubeWord, b65s_gw_append] at h
  calc (b65s_gw b65s_nineWord) ^ 9 = b65s_gw [] := by
        rw [← h]; simp only [pow_succ, pow_zero, one_mul, mul_assoc]
    _ = 1 := rfl

theorem b65s_conj_cube_mem {G : Type*} [Group G] [Finite G] (H : Subgroup G)
    (hindex : H.index ≤ 6) (x : G) (hx : x ^ 9 = 1) (g : G) : g⁻¹ * x ^ 3 * g ∈ H := by
  classical
  let c : G ⧸ H := (g : G ⧸ H)
  have : Fintype (G ⧸ H) := Fintype.ofFinite _
  have hcard : Fintype.card (G ⧸ H) < Fintype.card (Fin 7) := by
    rw [Fintype.card_fin, ← Nat.card_eq_fintype_card]
    exact lt_of_le_of_lt hindex (by norm_num)
  obtain ⟨i, j, hij, heq⟩ := Fintype.exists_ne_map_eq_of_card_lt
    (fun k : Fin 7 ↦ x ^ (k : ℕ) • c) hcard
  have key : ∃ d : ℕ, 1 ≤ d ∧ d ≤ 6 ∧ x ^ d • c = c := by
    have hsplit : ∀ a b : Fin 7, a < b → x ^ (a : ℕ) • c = x ^ (b : ℕ) • c →
        x ^ ((b : ℕ) - a) • c = c := by
      intro a b hab he
      have hp : x ^ (b : ℕ) = x ^ (a : ℕ) * x ^ ((b : ℕ) - a) := by
        rw [← pow_add]; congr 1; omega
      rw [hp, mul_smul] at he
      exact (MulAction.injective (x ^ (a : ℕ)) he).symm
    rcases lt_or_gt_of_ne hij with h | h
    · exact ⟨(j : ℕ) - i, by omega, by omega, hsplit i j h heq⟩
    · exact ⟨(i : ℕ) - j, by omega, by omega, hsplit j i h heq.symm⟩
  obtain ⟨d, hd1, hd6, hd⟩ := key
  have hpow : ∀ k : ℕ, (x ^ d) ^ k • c = c := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ, mul_smul, hd, ih]
  have h3 : x ^ 3 • c = c := by
    have hred : ∀ k m : ℕ, d * k = 3 + 9 * m → x ^ 3 = (x ^ d) ^ k := by
      intro k m hk
      rw [← pow_mul, hk, pow_add, pow_mul, hx, one_pow, mul_one]
    interval_cases d
    · rw [hred 3 0 rfl]; exact hpow 3
    · rw [hred 6 1 rfl]; exact hpow 6
    · rw [hred 1 0 rfl]; exact hpow 1
    · rw [hred 3 1 rfl]; exact hpow 3
    · rw [hred 6 3 rfl]; exact hpow 6
    · rw [hred 2 1 rfl]; exact hpow 2
  have hc : ((x ^ 3 * g : G) : G ⧸ H) = (g : G ⧸ H) := h3
  have := QuotientGroup.eq.mp hc.symm
  simpa [mul_assoc] using this

/-- The six pieces: the first reflection and five conjugates of the cube of the order-nine word,
each written as `A ++ cube ++ B` with `A` a positive word for the inverse of `B`.
Source: computed in the integral realization of `HurwitzPrymRex_g32SOne`. -/
def b65s_conjugators : List (List (Fin 4) × List (Fin 4)) :=
  [([], []), ([1, 1], [1]), ([2, 2, 2], [2]), ([3, 3], [3]), ([0, 0], [0])]

theorem b65s_conjugators_inv : ∀ p ∈ b65s_conjugators, b65s_gw p.1 = (b65s_gw p.2)⁻¹ := by
  intro p hp
  rw [eq_inv_iff_mul_eq_one, ← b65s_gw_append]
  simp only [b65s_conjugators, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl
  · rfl
  all_goals exact (b65s_gw_eq (v := []) (by decide +kernel)).trans rfl

theorem b65s_small_index_of_mem (H : Subgroup b4b_Group) (hindex : H.index ≤ 6)
    (h0 : b4b_generators 0 ∈ H) : H = ⊤ := by
  have hc : ∀ p ∈ b65s_conjugators, b65s_gw (p.1 ++ b65s_cubeWord ++ p.2) ∈ H := by
    intro p hp
    rw [b65s_gw_append, b65s_gw_append, b65s_conjugators_inv p hp]
    have : b65s_gw b65s_cubeWord = (b65s_gw b65s_nineWord) ^ 3 := by
      simp only [b65s_cubeWord, b65s_gw_append, pow_succ, pow_zero, one_mul]
    rw [this]
    exact b65s_conj_cube_mem H hindex _ b65s_nine_pow _
  have P0 : b65s_gw [0] ∈ H := by simpa [b65s_gw] using h0
  have P1 := hc ([], []) (by simp [b65s_conjugators])
  have P2 := hc ([1, 1], [1]) (by simp [b65s_conjugators])
  have P3 := hc ([2, 2, 2], [2]) (by simp [b65s_conjugators])
  have P4 := hc ([3, 3], [3]) (by simp [b65s_conjugators])
  have P5 := hc ([0, 0], [0]) (by simp [b65s_conjugators])
  simp only at P1 P2 P3 P4 P5
  set q0 : List (Fin 4) := [0]
  set q1 : List (Fin 4) := [] ++ b65s_cubeWord ++ []
  set q2 : List (Fin 4) := [1, 1] ++ b65s_cubeWord ++ [1]
  set q3 : List (Fin 4) := [2, 2, 2] ++ b65s_cubeWord ++ [2]
  set q4 : List (Fin 4) := [3, 3] ++ b65s_cubeWord ++ [3]
  set q5 : List (Fin 4) := [0, 0] ++ b65s_cubeWord ++ [0]
  have hg : ∀ k : Fin 4, b4b_generators k ∈ H := by
    intro k
    have hk : b4b_generators k = b65s_gw [k] := by simp [b65s_gw]
    rw [hk]
    fin_cases k
    · exact P0
    · rw [b65s_gw_eq (v := q0 ++ q0 ++ q3 ++ q0 ++ q3 ++ q0 ++ q0 ++ q3) (by decide +kernel)]
      simp only [b65s_gw_append]
      repeat' (first | assumption | apply H.mul_mem)
    · rw [b65s_gw_eq (v := q0 ++ q0 ++ q2 ++ q0 ++ q4 ++ q2 ++ q2 ++ q0 ++ q3 ++ q0 ++ q0)
        (by decide +kernel)]
      simp only [b65s_gw_append]
      repeat' (first | assumption | apply H.mul_mem)
    · rw [b65s_gw_eq (v := q0 ++ q0 ++ q3 ++ q2 ++ q4 ++ q4 ++ q1 ++ q1 ++ q3 ++ q0)
        (by decide +kernel)]
      simp only [b65s_gw_append]
      repeat' (first | assumption | apply H.mul_mem)
  apply top_unique
  intro g _
  have hind : ∀ (x : Matrix (Fin 4) (Fin 4) ℂ), x ∈ Submonoid.closure
        {g32R1 g32h_omega, g32R2 g32h_omega, g32X g32h_omega, g32Y g32h_omega} →
      ∃ hx : x ∈ g32h_G, (⟨x, hx⟩ : b4b_Group) ∈ H := by
    intro x hcl
    induction hcl using Submonoid.closure_induction with
    | mem x hmem =>
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
        rcases hmem with rfl | rfl | rfl | rfl
        · exact ⟨(b4b_generators 0).property, hg 0⟩
        · exact ⟨(b4b_generators 1).property, hg 1⟩
        · exact ⟨(b4b_generators 2).property, hg 2⟩
        · exact ⟨(b4b_generators 3).property, hg 3⟩
    | one => exact ⟨one_mem _, one_mem H⟩
    | mul x y hx hy ihx ihy =>
        rcases ihx with ⟨hxG, hxH⟩
        rcases ihy with ⟨hyG, hyH⟩
        exact ⟨mul_mem hxG hyG, H.mul_mem hxH hyH⟩
  rcases hind g.val g.property with ⟨hgG, hmem⟩
  simpa using hmem

theorem b65s_small_index_aux (H : Subgroup b4b_Group) (hindex : H.index ≤ 6)
    (href : ∃ g : b4b_Group, g * b4b_generators 0 * g⁻¹ ∈ H) :
    H = ⊤ := by
  obtain ⟨g, hg⟩ := href
  let H' := H.comap (MulAut.conj g).toMonoidHom
  have hi : H'.index = H.index :=
    Subgroup.index_comap_of_surjective H (MulAut.conj g).surjective
  have hH' : H' = ⊤ := b65s_small_index_of_mem H' (hi ▸ hindex) (by
    change (MulAut.conj g) (b4b_generators 0) ∈ H
    simpa using hg)
  apply top_unique
  intro k _
  have hk : g⁻¹ * k * g ∈ H' := hH' ▸ Subgroup.mem_top _
  change (MulAut.conj g) (g⁻¹ * k * g) ∈ H at hk
  simpa [mul_assoc] using hk

theorem b65s_opposite_conversion_aux (Γ : Type*) [Group Γ] (κ : Γ →* b4b_Groupᵐᵒᵖ) :
    (Function.Surjective ((b65s_unopInv b4b_Group).comp κ) ↔ Function.Surjective κ) ∧
      ∀ c : Γ, (b65s_column κ c).val =
        b65r_operator (b4b_toMatrix (MulOpposite.unop (κ (c⁻¹)))) := by
  refine ⟨⟨fun h y ↦ ?_, fun h g ↦ ?_⟩, fun c ↦ ?_⟩
  · obtain ⟨c, hc⟩ := h (MulOpposite.unop y)⁻¹
    refine ⟨c, MulOpposite.unop_injective (inv_injective ?_)⟩
    simpa [b65s_unopInv] using hc
  · obtain ⟨c, hc⟩ := h (MulOpposite.op g⁻¹)
    exact ⟨c, by simp [b65s_unopInv, hc]⟩
  · rw [map_inv, MulOpposite.unop_inv]
    rfl

theorem b65s_columnRoot_list :
    List.ofFn b65s_columnRoot = ((List.ofFn b4b_root).map (fun x ↦ x⁻¹)).reverse := rfl

theorem b65s_reflection_inv_isConj (u v : List (Fin 4)) :
    IsConj (b4b_reflection u)⁻¹ (b4b_reflection v)⁻¹ := by
  refine isConj_iff.mpr ⟨(v.map b4b_generators).prod * ((u.map b4b_generators).prod)⁻¹, ?_⟩
  simp only [b4b_reflection]
  group

theorem b65s_reflection_isConj (u v : List (Fin 4)) :
    IsConj (b4b_reflection u) (b4b_reflection v) := by
  refine isConj_iff.mpr ⟨(v.map b4b_generators).prod * ((u.map b4b_generators).prod)⁻¹, ?_⟩
  simp only [b4b_reflection]
  group

/-- Pairing of the column-root slots with the original root slots of equal class.
Source: `b4b_root`; inverse pairs and conjugate reflections. -/
def b65s_columnPerm : Equiv.Perm (Fin 13) :=
  Equiv.ofBijective ![12, 10, 11, 8, 9, 6, 7, 4, 5, 2, 3, 0, 1] (by decide)

theorem b65s_columnRoot_class (i : Fin 13) :
    ConjClasses.mk (b65s_columnRoot i) = ConjClasses.mk (b4b_root (b65s_columnPerm i)) := by
  apply ConjClasses.mk_eq_mk_iff_isConj.mpr
  fin_cases i
  · have h4 : (b4b_generators 2) ^ 4 = 1 := b63_generator_two_fourth
    change IsConj ((b4b_generators 2) ^ 2)⁻¹ ((b4b_generators 2) ^ 2)
    rw [show ((b4b_generators 2) ^ 2)⁻¹ = (b4b_generators 2) ^ 2 by
      rw [inv_eq_iff_mul_eq_one, ← pow_add, show 2 + 2 = 4 from rfl, h4]]
  · change IsConj ((b4b_reflection [3, 2, 1])⁻¹)⁻¹ (b4b_reflection [3, 2])
    rw [inv_inv]; exact b65s_reflection_isConj _ _
  · change IsConj (b4b_reflection [3, 2])⁻¹ (b4b_reflection [3, 2, 1])⁻¹
    exact b65s_reflection_inv_isConj _ _
  · change IsConj ((b4b_reflection [0, 0, 2])⁻¹)⁻¹ (b4b_reflection [1, 3, 1])
    rw [inv_inv]; exact b65s_reflection_isConj _ _
  · change IsConj (b4b_reflection [1, 3, 1])⁻¹ (b4b_reflection [0, 0, 2])⁻¹
    exact b65s_reflection_inv_isConj _ _
  · change IsConj ((b4b_reflection [3])⁻¹)⁻¹ (b4b_reflection [3])
    rw [inv_inv]
  · change IsConj (b4b_reflection [3])⁻¹ (b4b_reflection [3])⁻¹
    exact IsConj.refl _
  · change IsConj ((b4b_reflection [2])⁻¹)⁻¹ (b4b_reflection [2])
    rw [inv_inv]
  · change IsConj (b4b_reflection [2])⁻¹ (b4b_reflection [2])⁻¹
    exact IsConj.refl _
  · change IsConj (b4b_generators 1)⁻¹ (b4b_generators 1)⁻¹
    exact IsConj.refl _
  · change IsConj ((b4b_generators 1)⁻¹)⁻¹ (b4b_generators 1)
    rw [inv_inv]
  · change IsConj ((b4b_generators 0)⁻¹)⁻¹ (b4b_generators 0)
    rw [inv_inv]
  · change IsConj (b4b_generators 0)⁻¹ (b4b_generators 0)⁻¹
    exact IsConj.refl _

theorem b65s_column_root_aux  :
    b4_Nielsen b65s_columnRoot ∧ b4_classes b65s_columnRoot = b4_classes b4b_root := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [b65s_columnRoot_list, ← List.prod_inv_reverse, b63d_root_product, inv_one]
  · have hr : Set.range b65s_columnRoot = (Set.range b4b_root)⁻¹ := by
      ext g
      simp only [Set.mem_range, Set.mem_inv, b65s_columnRoot]
      constructor
      · rintro ⟨i, rfl⟩; exact ⟨i.rev, by simp⟩
      · rintro ⟨i, hi⟩; exact ⟨i.rev, by simp [hi]⟩
    rw [hr, Subgroup.closure_inv, b63d_root_subgroup]
  · unfold b4_classes
    rw [List.map_ofFn, List.map_ofFn]
    have hf : (ConjClasses.mk ∘ b65s_columnRoot) =
        (ConjClasses.mk ∘ b4b_root) ∘ b65s_columnPerm := by
      funext i
      exact b65s_columnRoot_class i
    rw [hf]
    exact Multiset.coe_eq_coe.mpr (b65s_columnPerm.ofFn_comp_perm _)

theorem b65s_step_sameComponent (m : b65s_Move) (t : Fin 13 → b4b_Group) :
    b4_SameComponent t (b65s_step m t) := by
  cases m with
  | positive i =>
      exact Relation.EqvGen.rel _ _ (Or.inr ⟨i.castSucc, i.succ, by simp, rfl⟩)
  | conjugate g => exact Relation.EqvGen.rel _ _ (Or.inl ⟨g, rfl⟩)
  | negative i =>
      have hne : i.castSucc ≠ i.succ := Fin.castSucc_lt_succ.ne
      have hb : b4_braid i.castSucc i.succ (b65s_step (.negative i) t) = t := by
        funext j
        simp only [b4_braid, b65s_step]
        by_cases hj : j = i.castSucc
        · subst hj
          simp [hne]
          group
        · by_cases hk : j = i.succ
          · subst hk
            simp [hne.symm, hne]
          · simp [Function.update_apply, hj, hk, Equiv.swap_apply_of_ne_of_ne]
      refine Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ (Or.inr ⟨i.castSucc, i.succ, by simp, ?_⟩))
      exact hb.symm

theorem b65s_word_orbit_aux (w : List b65s_Move) (t : Fin 13 → b4b_Group) :
    b4_SameComponent t (b65s_word w t) ∧
      b4_classes (b65s_word w t) = b4_classes t ∧
      (b4_Nielsen (b65s_word w t) ↔ b4_Nielsen t) := by
  have h : b4_SameComponent t (b65s_word w t) := by
    induction w generalizing t with
    | nil => exact Relation.EqvGen.refl t
    | cons m w ih =>
        exact Relation.EqvGen.trans _ _ _ (b65s_step_sameComponent m t) (ih (b65s_step m t))
  exact ⟨h, b4_classes_of_sameComponent h,
    ⟨fun hn ↦ b4_nielsen_of_sameComponent (Relation.EqvGen.symm _ _ h) hn,
      b4_nielsen_of_sameComponent h⟩⟩

theorem b65s_normalize_injective {a b z w : ℂ} (ha : a ≠ 0) (hb : b ≠ 0) (hab : b - a ≠ 0)
    (hz : z ≠ 0) (hw : w ≠ 0) (h : b65s_normalize a b z = b65s_normalize a b w) : z = w := by
  unfold b65s_normalize at h
  field_simp at h
  have : a * (z - w) = 0 := by linear_combination h
  rcases mul_eq_zero.mp this with h' | h'
  · exact absurd h' ha
  · exact sub_eq_zero.mp h'

theorem b65s_normalize_ne_zero {a b z : ℂ} (hb : b ≠ 0) (hab : b - a ≠ 0)
    (hz : z ≠ 0) (hza : z ≠ a) : b65s_normalize a b z ≠ 0 := by
  unfold b65s_normalize
  exact div_ne_zero (mul_ne_zero (sub_ne_zero.mpr hza) hb) (mul_ne_zero hz hab)

theorem b65s_normalize_ne_one {a b z : ℂ} (ha : a ≠ 0) (hab : b - a ≠ 0)
    (hz : z ≠ 0) (hzb : z ≠ b) : b65s_normalize a b z ≠ 1 := by
  unfold b65s_normalize
  intro h
  rw [div_eq_one_iff_eq (mul_ne_zero hz hab)] at h
  have : a * (z - b) = 0 := by linear_combination h
  rcases mul_eq_zero.mp this with h' | h'
  · exact ha h'
  · exact hzb (sub_eq_zero.mp h')

theorem b65s_chart_of {t : Fin 10 → ℂ} (ht : Function.Injective t) (h0 : ∀ i, t i ≠ 0)
    (h1 : ∀ i, t i ≠ 1) : t ∈ b6_chart := by
  intro (i : Fin (10 + 3)) (j : Fin (10 + 3)) hij
  induction i using Fin.addCases with
  | left i =>
    induction j using Fin.addCases with
    | left j =>
      simp only [b6_branch, Fin.append_left] at hij
      rw [ht (OnePoint.coe_injective hij)]
    | right k =>
      simp only [b6_branch, Fin.append_left, Fin.append_right] at hij
      fin_cases k
      · exact absurd (OnePoint.coe_injective hij) (h0 i)
      · exact absurd (OnePoint.coe_injective hij) (h1 i)
      · exact absurd hij (OnePoint.coe_ne_infty _)
  | right k =>
    induction j using Fin.addCases with
    | left j =>
      simp only [b6_branch, Fin.append_left, Fin.append_right] at hij
      fin_cases k
      · exact absurd (OnePoint.coe_injective hij).symm (h0 j)
      · exact absurd (OnePoint.coe_injective hij).symm (h1 j)
      · exact absurd hij.symm (OnePoint.coe_ne_infty _)
    | right l =>
      simp only [b6_branch, Fin.append_right] at hij
      fin_cases k <;> fin_cases l <;> simp_all

theorem b65s_normalization_aux  :
    ∃ p : Fin 13 → ℂ,
      Function.Injective p ∧
      Set.range (fun i ↦ (p i : OnePoint ℂ)) = b65s_branch ∧
      p 12 = 0 ∧ b65r_P 5 (p 10) = 0 ∧ b65r_P (-7) (p 11) = 0 ∧
      (fun i : Fin 10 ↦ b65s_normalize (p 10) (p 11) (p (Fin.castLE (by omega) i))) ∈ b6_chart := by
  classical
  obtain ⟨a, ha⟩ : ((b65s_poly 5).roots.toFinset).Nonempty := by
    rw [← Finset.card_pos, b65s_card5]; norm_num
  obtain ⟨b, hb⟩ : ((b65s_poly (-7)).roots.toFinset).Nonempty := by
    rw [← Finset.card_pos, b65s_cardneg7]; norm_num
  have ha' := (b65s_mem_roots 5 a (by norm_num)).mp ha
  have hb' := (b65s_mem_roots (-7) b (by norm_num)).mp hb
  have ha0 : a ≠ 0 := fun h ↦ b65s_fibre_ne_zero 5 (by norm_num) (h ▸ ha')
  have hb0 : b ≠ 0 := fun h ↦ b65s_fibre_ne_zero (-7) (by norm_num) (h ▸ hb')
  have hab : a ≠ b := fun h ↦ b65s_fibres_disjoint a ha' (h ▸ hb')
  let S := ((b65s_branchFinset.erase 0).erase a).erase b
  have hmemS : ∀ z, z ∈ S ↔ z ≠ b ∧ z ≠ a ∧ z ≠ 0 ∧ z ∈ b65s_branchFinset := by
    intro z; simp only [S, Finset.mem_erase]
  have hS : S.card = 10 := by
    have h0m : (0 : ℂ) ∈ b65s_branchFinset := (b65s_mem_branchFinset 0).mpr (Or.inl rfl)
    have ham : a ∈ b65s_branchFinset.erase 0 :=
      Finset.mem_erase.mpr ⟨ha0, (b65s_mem_branchFinset a).mpr (Or.inr (Or.inl ha'))⟩
    have hbm : b ∈ (b65s_branchFinset.erase 0).erase a :=
      Finset.mem_erase.mpr ⟨hab.symm, Finset.mem_erase.mpr
        ⟨hb0, (b65s_mem_branchFinset b).mpr (Or.inr (Or.inr hb'))⟩⟩
    simp only [S]
    rw [Finset.card_erase_of_mem hbm, Finset.card_erase_of_mem ham,
      Finset.card_erase_of_mem h0m, b65s_branchFinset_card]
  let e : S ≃ Fin 10 := Fintype.equivFinOfCardEq (by rw [Fintype.card_coe, hS])
  let p : Fin 13 → ℂ := fun i ↦
    if h : i.val < 10 then (e.symm ⟨i.val, h⟩ : ℂ) else if i.val = 10 then a
    else if i.val = 11 then b else 0
  have hpS : ∀ i : Fin 13, (h : i.val < 10) → p i = (e.symm ⟨i.val, h⟩ : ℂ) := by
    intro i h; simp only [p]
    simp [h]
  have hp10 : p 10 = a := by simp [p]
  have hp11 : p 11 = b := by simp [p]
  have hp12 : p 12 = 0 := by simp [p]
  have hlow : ∀ i : Fin 13, i.val < 10 → p i ≠ b ∧ p i ≠ a ∧ p i ≠ 0 ∧ p i ∈ b65s_branchFinset := by
    intro i h
    rw [hpS i h]
    exact (hmemS _).mp (e.symm ⟨i.val, h⟩).property
  have hinj : Function.Injective p := by
    intro i j hij
    by_cases hi : i.val < 10 <;> by_cases hj : j.val < 10
    · rw [hpS i hi, hpS j hj] at hij
      have := e.symm.injective (Subtype.ext hij)
      exact Fin.ext (by simpa using this)
    all_goals
      have hi' : i.val < 13 := i.isLt
      have hj' : j.val < 13 := j.isLt
    · obtain ⟨h1, h2, h3, -⟩ := hlow i hi
      exfalso
      have : j = 10 ∨ j = 11 ∨ j = 12 := by omega
      rcases this with rfl | rfl | rfl
      · exact h2 (hij.trans hp10)
      · exact h1 (hij.trans hp11)
      · exact h3 (hij.trans hp12)
    · obtain ⟨h1, h2, h3, -⟩ := hlow j hj
      exfalso
      have : i = 10 ∨ i = 11 ∨ i = 12 := by omega
      rcases this with rfl | rfl | rfl
      · exact h2 (hij.symm.trans hp10)
      · exact h1 (hij.symm.trans hp11)
      · exact h3 (hij.symm.trans hp12)
    · have hi3 : i = 10 ∨ i = 11 ∨ i = 12 := by omega
      have hj3 : j = 10 ∨ j = 11 ∨ j = 12 := by omega
      rcases hi3 with rfl | rfl | rfl <;> rcases hj3 with rfl | rfl | rfl <;>
        simp only [hp10, hp11, hp12] at hij
      all_goals first | rfl | exact absurd hij (by assumption) |
        exact absurd hij.symm (by assumption)
  have hrange : Set.range p = ↑b65s_branchFinset := by
    ext z
    simp only [Set.mem_range, Finset.mem_coe]
    constructor
    · rintro ⟨i, rfl⟩
      by_cases hi : i.val < 10
      · exact (hlow i hi).2.2.2
      · have : i = 10 ∨ i = 11 ∨ i = 12 := by omega
        rcases this with rfl | rfl | rfl
        · rw [hp10]; exact (b65s_mem_branchFinset a).mpr (Or.inr (Or.inl ha'))
        · rw [hp11]; exact (b65s_mem_branchFinset b).mpr (Or.inr (Or.inr hb'))
        · rw [hp12]; exact (b65s_mem_branchFinset 0).mpr (Or.inl rfl)
    · intro hz
      by_cases h0 : z = 0
      · exact ⟨12, h0 ▸ hp12⟩
      by_cases hza : z = a
      · exact ⟨10, hza ▸ hp10⟩
      by_cases hzb : z = b
      · exact ⟨11, hzb ▸ hp11⟩
      have hzS : z ∈ S := (hmemS z).mpr ⟨hzb, hza, h0, hz⟩
      refine ⟨⟨(e ⟨z, hzS⟩).val, by omega⟩, ?_⟩
      rw [hpS _ (e ⟨z, hzS⟩).isLt]
      simp
  refine ⟨p, hinj, ?_, hp12, hp10 ▸ ha', hp11 ▸ hb', ?_⟩
  · rw [b65s_branch_eq, ← hrange, ← Set.range_comp]
    rfl
  · rw [hp10, hp11]
    have hba : b - a ≠ 0 := sub_ne_zero.mpr hab.symm
    have hcast : ∀ i : Fin 10, ((Fin.castLE (by omega) i : Fin 13)).val < 10 := fun i ↦ i.isLt
    apply b65s_chart_of
    · intro i j hij
      have := b65s_normalize_injective ha0 hb0 hba (hlow _ (hcast i)).2.2.1
        (hlow _ (hcast j)).2.2.1 hij
      have := hinj this
      exact Fin.ext (by simpa using congrArg Fin.val this)
    · intro i
      exact b65s_normalize_ne_zero hb0 hba (hlow _ (hcast i)).2.2.1 (hlow _ (hcast i)).2.1
    · intro i
      exact b65s_normalize_ne_one ha0 hba (hlow _ (hcast i)).2.2.1 (hlow _ (hcast i)).1

end HodgeLean.Foundations.Program
