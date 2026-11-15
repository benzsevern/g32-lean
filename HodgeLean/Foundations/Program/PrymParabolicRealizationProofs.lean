import HodgeLean.Foundations.Program.PrymParabolicRealizationDefs
import HodgeLean.Foundations.Program.PrymParabolicRealizationTrace

/-! # Proofs for stage H3b: cellular homology of the lifted complex

The `_aux` theorems that `PrymParabolicRealization.lean` restates.
Cellular homology, universal coefficients and the projector trace calculation.
HC no distance; AV milestone no distance.
-/

noncomputable section

open scoped TensorProduct

namespace HodgeLean.Foundations.Program

theorem hg2_Q_take {G : Type*} [Group G] {r : ℕ} (g : Fin r → G) (i : Fin r) :
    hg2_Q g i = ((List.ofFn g).take i.val).prod := by
  unfold hg2_Q
  rw [List.ofFn_eq_map, ← List.map_take]
  congr 2
  rw [List.Nodup.take_eq_filter_mem (List.nodup_finRange r)]
  apply List.filter_congr
  intro j hj
  simp only [List.elem_eq_mem, decide_eq_decide]
  rw [List.mem_take_iff_idxOf_lt (List.mem_finRange j), List.idxOf_finRange]
  rfl

theorem hg2_Q_rotate {G : Type*} [Group G] {r : ℕ} (g : Fin r → G)
    (hprod : (List.ofFn g).prod = 1) (i : Fin r) :
    hg2_Q g (finRotate r i) = hg2_Q g i * g i := by
  cases r with
  | zero => exact i.elim0
  | succ n =>
    by_cases hi : i = Fin.last n
    · subst i
      rw [finRotate_last, hg2_Q_take, hg2_Q_take]
      simp only [Fin.val_zero, List.take_zero, List.prod_nil, Fin.val_last]
      calc
        1 = (List.ofFn g).prod := hprod.symm
        _ = ((List.ofFn g).take (n + 1)).prod := by rw [List.take_of_length_le (by simp)]
        _ = ((List.ofFn g).take n).prod * g (Fin.last n) := by
          rw [List.prod_take_succ (List.ofFn g) n (by simp)]
          congr 1
          exact List.getElem_ofFn (by simp)
    · rw [hg2_Q_take, hg2_Q_take, coe_finRotate_of_ne_last hi,
        List.prod_take_succ _ _ (by simpa using i.isLt)]
      simp only [List.getElem_ofFn]

theorem hg2_boundary_comp_aux (R : Type*) [CommRing R] {G : Type*} [Group G] {r : ℕ}
    (g : Fin r → G) (hprod : (List.ofFn g).prod = 1) :
    hg2_bd1 R g ∘ₗ hg2_bd2 R g = 0 := by
  classical
  apply Finsupp.lhom_ext
  intro τ a
  rcases τ with ⟨i, x⟩ | ⟨i, x⟩
  · simp [hg2_bd1, hg2_bd2, hg2_face0, hg2_face1, hg2_face2, hg2_src, hg2_tgt, Finsupp.mapDomain_add, Finsupp.mapDomain_sub]
  · have hc : ((x * (g i)⁻¹ : G) : G ⧸ Subgroup.zpowers (g i)) =
        (x : G ⧸ Subgroup.zpowers (g i)) := by
      apply QuotientGroup.eq.mpr
      simp
    have ht : x * (g i)⁻¹ * (hg2_Q g i)⁻¹ =
        x * (hg2_Q g (finRotate r i))⁻¹ := by
      rw [hg2_Q_rotate g hprod, mul_inv_rev, mul_assoc]
    simp [hg2_bd1, hg2_bd2, hg2_face0, hg2_face1, hg2_face2, hg2_src, hg2_tgt,
      Finsupp.mapDomain_add, Finsupp.mapDomain_sub, hc, ht]

theorem hg2_loop_transport_aux {G : Type*} [Group G] {r : ℕ} (g : Fin r → G)
    (hprod : (List.ofFn g).prod = 1) (i : Fin r) (x y : G) :
    hg2_tgt g (Sum.inr (Sum.inl (finRotate r i, y))) = hg2_tgt g (Sum.inr (Sum.inl (i, x))) ↔
      y = x * g i := by
  simp only [hg2_tgt, Sum.inr.injEq, Sum.inl.injEq, hg2_Q_rotate g hprod,
    mul_inv_rev, ← mul_assoc, mul_right_cancel_iff]
  exact mul_inv_eq_iff_eq_mul

theorem hg2_ramification_aux {G : Type*} [Group G] {r : ℕ} (g : Fin r → G) (i : Fin r)
    (c : G ⧸ Subgroup.zpowers (g i)) :
    Nat.card {y : G // hg2_tgt g (Sum.inl (i, y)) = Sum.inr (Sum.inr ⟨i, c⟩)} =
      orderOf (g i) := by
  classical
  have heq : ∀ y : G,
      hg2_tgt g (Sum.inl (i, y)) = Sum.inr (Sum.inr ⟨i, c⟩) ↔
        (y : G ⧸ Subgroup.zpowers (g i)) = c := by
    intro y
    simp [hg2_tgt]
  let e := Equiv.subtypeEquivRight heq
  rw [Nat.card_congr e]
  induction c using QuotientGroup.induction_on with
  | H x =>
    let e' : {y : G // (y : G ⧸ Subgroup.zpowers (g i)) =
        (x : G ⧸ Subgroup.zpowers (g i))} ≃ Subgroup.zpowers (g i) :=
      (Equiv.subtypeEquivRight fun y => QuotientGroup.eq).trans
        { toFun := fun y => ⟨x⁻¹ * y.1, by simpa using (Subgroup.inv_mem _ y.2)⟩
          invFun := fun z => ⟨x * z.1, by simpa using z.2⟩
          left_inv := fun y => Subtype.ext (by simp)
          right_inv := fun z => Subtype.ext (by simp) }
    exact (Nat.card_congr e').trans (Nat.card_zpowers (g i))

theorem hg2_bd2_coeffs {R : Type*} [CommRing R] {G : Type*} [Group G]
    {r : ℕ} (g : Fin r → G) (w : hg2_Tri G r →₀ R) (i : Fin r) (x : G) :
    (hg2_bd2 R g w) (Sum.inl (i, x)) = w (Sum.inl (i, x)) + w (Sum.inr (i, x)) ∧
    (hg2_bd2 R g w) (Sum.inr (Sum.inr (i, x))) =
      w (Sum.inl (i, x)) + w (Sum.inr (i, x * g i)) ∧
    (hg2_bd2 R g w) (Sum.inr (Sum.inl (finRotate r i, x))) =
      -w (Sum.inl (finRotate r i, x)) - w (Sum.inr (i, x)) := by
  classical
  induction w using Finsupp.induction_linear with
  | zero => simp
  | add w z hw hz =>
    simp only [map_add, Finsupp.add_apply]
    constructor
    · rw [hw.1, hz.1]; ring
    constructor
    · rw [hw.2.1, hz.2.1]; ring
    · rw [hw.2.2, hz.2.2]; ring
  | single τ a =>
    rcases τ with ⟨j, y⟩ | ⟨j, y⟩ <;>
      simp [hg2_bd2, hg2_face0, hg2_face1, hg2_face2, Finsupp.single_apply,
        Prod.mk.injEq, mul_inv_eq_iff_eq_mul]
    all_goals by_cases hji : j = i <;> simp_all

theorem hg2_orient_coeffs {G : Type*} [Fintype G] {r : ℕ} (i : Fin r) (x : G) :
    hg2_orient (Sum.inl (i, x)) = 1 ∧ hg2_orient (Sum.inr (i, x)) = -1 := by
  classical
  simp [hg2_orient, Finsupp.single_apply, ite_and]

theorem hg2_cycles2_aux {G : Type*} [Group G] [Fintype G] {r : ℕ} (g : Fin r → G)
    (hprod : (List.ofFn g).prod = 1) (hg : Subgroup.closure (Set.range g) = ⊤) :
    LinearMap.ker (hg2_bd2 ℤ g) = Submodule.span ℤ {hg2_orient} := by
  classical
  apply le_antisymm
  · intro w hw
    have hz : hg2_bd2 ℤ g w = 0 := hw
    have he (i : Fin r) (x : G) : w (Sum.inr (i, x)) = -w (Sum.inl (i, x)) := by
      have h := (hg2_bd2_coeffs g w i x).1
      rw [hz, Finsupp.zero_apply] at h
      linarith
    have hr (i : Fin r) (x : G) :
        w (Sum.inl (finRotate r i, x)) = w (Sum.inl (i, x)) := by
      have h := (hg2_bd2_coeffs g w i x).2.2
      rw [hz, Finsupp.zero_apply, he] at h
      linarith
    have hm (i : Fin r) (x : G) :
        w (Sum.inl (i, x * g i)) = w (Sum.inl (i, x)) := by
      have h := (hg2_bd2_coeffs g w i x).2.1
      rw [hz, Finsupp.zero_apply, he] at h
      linarith
    cases r with
    | zero =>
      have hw0 : w = 0 := by
        ext τ
        rcases τ with ⟨i, x⟩ | ⟨i, x⟩ <;> exact i.elim0
      rw [hw0]
      exact Submodule.zero_mem _
    | succ n =>
      have hi (i : Fin (n + 1)) (x : G) :
          w (Sum.inl (i, x)) = w (Sum.inl (0, x)) := by
        induction i using Fin.induction with
        | zero => rfl
        | succ j hj =>
          have hjr : finRotate (n + 1) j.castSucc = j.succ := finRotate_of_lt j.isLt
          rw [← hjr, hr, hj]
      have hinv (y : G) : ∀ x : G,
          w (Sum.inl (0, x * y)) = w (Sum.inl (0, x)) := by
        have hy : y ∈ Subgroup.closure (Set.range g) := by rw [hg]; trivial
        induction hy using Subgroup.closure_induction with
        | mem z hz =>
          obtain ⟨i, rfl⟩ := hz
          intro x
          rw [← hi i (x * g i), hm, hi]
        | one => intro x; simp
        | mul a b ha hb ia ib => intro x; rw [← mul_assoc, ib, ia]
        | inv a ha ia =>
          intro x
          have h := ia (x * a⁻¹)
          simpa only [inv_mul_cancel_right] using h.symm
      have hc (i : Fin (n + 1)) (x : G) :
          w (Sum.inl (i, x)) = w (Sum.inl (0, (1 : G))) := by
        rw [hi]
        simpa using hinv x 1
      apply Submodule.mem_span_singleton.mpr
      refine ⟨w (Sum.inl (0, (1 : G))), ?_⟩
      ext τ
      rcases τ with ⟨i, x⟩ | ⟨i, x⟩
      · simp only [Finsupp.smul_apply, (hg2_orient_coeffs i x).1, smul_eq_mul, mul_one]
        exact (hc i x).symm
      · simp only [Finsupp.smul_apply, (hg2_orient_coeffs i x).2, smul_eq_mul, mul_neg_one]
        simp only [he, hc]
  · apply Submodule.span_le.mpr
    intro w hw
    obtain rfl := Set.mem_singleton_iff.mp hw
    change hg2_bd2 ℤ g hg2_orient = 0
    ext ε
    rcases ε with ⟨i, x⟩ | ⟨i, x⟩ | ⟨i, x⟩
    · rw [(hg2_bd2_coeffs g hg2_orient i x).1]
      simp only [(hg2_orient_coeffs i x).1, (hg2_orient_coeffs i x).2]; simp
    · obtain ⟨j, rfl⟩ := (finRotate r).surjective i
      rw [(hg2_bd2_coeffs g hg2_orient j x).2.2]
      simp only [(hg2_orient_coeffs _ x).1, (hg2_orient_coeffs j x).2]; simp
    · rw [(hg2_bd2_coeffs g hg2_orient i x).2.1]
      simp only [(hg2_orient_coeffs i x).1, (hg2_orient_coeffs i (x * g i)).2]; simp

theorem hg2_divide_difference (a b n z : ℤ) (hn : n ≠ 0) (h : a - b = n * z) :
    a / n - b / n = z := by
  rw [← Int.sub_ediv_of_dvd_sub (show n ∣ a - b from ⟨z, h⟩), h]
  exact Int.mul_ediv_cancel_left z hn

theorem hg2_bd2_saturated {G : Type*} [Group G] [Finite G] {r : ℕ}
    (g : Fin r → G) (n : ℤ) (hn : n ≠ 0) (z : hg2_Edge G r →₀ ℤ)
    (hz : n • z ∈ LinearMap.range (hg2_bd2 ℤ g)) : z ∈ LinearMap.range (hg2_bd2 ℤ g) := by
  classical
  letI := Fintype.ofFinite G
  obtain ⟨w, hw⟩ := hz
  let q : hg2_Tri G r →₀ ℤ := Finsupp.equivFunOnFinite.symm
    (fun τ => match τ with
      | Sum.inl p => w (Sum.inl p) / n
      | Sum.inr p => -((-w (Sum.inr p)) / n))
  have hqA (i : Fin r) (x : G) : q (Sum.inl (i, x)) = w (Sum.inl (i, x)) / n := by
    simp [q]
  have hqB (i : Fin r) (x : G) : q (Sum.inr (i, x)) = -((-w (Sum.inr (i, x))) / n) := by
    simp [q]
  have he (ε : hg2_Edge G r) : hg2_bd2 ℤ g w ε = n * z ε := by
    rw [hw]; rfl
  refine ⟨q, ?_⟩
  ext ε
  rcases ε with ⟨i, x⟩ | ⟨i, x⟩ | ⟨i, x⟩
  · rw [(hg2_bd2_coeffs g q i x).1, hqA, hqB]
    apply hg2_divide_difference _ _ _ _ hn
    simpa only [sub_neg_eq_add, (hg2_bd2_coeffs g w i x).1] using he (Sum.inl (i, x))
  · obtain ⟨j, rfl⟩ := (finRotate r).surjective i
    rw [(hg2_bd2_coeffs g q j x).2.2, hqA, hqB, sub_neg_eq_add]
    have hh := hg2_divide_difference (-w (Sum.inr (j, x)))
      (w (Sum.inl (finRotate r j, x))) n (z (Sum.inr (Sum.inl (finRotate r j, x)))) hn
    have hh' : -w (Sum.inr (j, x)) - w (Sum.inl (finRotate r j, x)) =
        n * z (Sum.inr (Sum.inl (finRotate r j, x))) := by
      have h := he (Sum.inr (Sum.inl (finRotate r j, x)))
      rw [(hg2_bd2_coeffs g w j x).2.2] at h
      linarith
    linarith [hh hh']
  · rw [(hg2_bd2_coeffs g q i x).2.1, hqA, hqB]
    apply hg2_divide_difference _ _ _ _ hn
    simpa only [sub_neg_eq_add, (hg2_bd2_coeffs g w i x).2.1] using
      he (Sum.inr (Sum.inr (i, x)))

theorem hg2_H1_finite_free {G : Type*} [Group G] [Finite G] {r : ℕ} (g : Fin r → G) :
    Module.Free ℤ (hg2_H1 ℤ g) ∧ Module.Finite ℤ (hg2_H1 ℤ g) := by
  classical
  letI : Module.Finite ℤ (hg2_H1 ℤ g) := inferInstance
  have ht : Module.IsTorsionFree ℤ (hg2_H1 ℤ g) := by
    apply Module.IsTorsionFree.of_smul_eq_zero
    intro n x hx
    by_cases hn : n = 0
    · exact Or.inl hn
    right
    obtain ⟨z, rfl⟩ := Submodule.mkQ_surjective _ x
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    change z.1 ∈ LinearMap.range (hg2_bd2 ℤ g)
    apply hg2_bd2_saturated g n hn z.1
    have hmem := (Submodule.Quotient.mk_eq_zero _).mp
      ((Submodule.mkQ _).map_smul n z |>.trans hx)
    exact hmem
  letI := ht
  exact ⟨inferInstance, inferInstance⟩

theorem hg2_H0_equiv {G : Type*} [Group G] {r : ℕ} [NeZero r] (g : Fin r → G)
    (hg : Subgroup.closure (Set.range g) = ⊤) :
    Nonempty (((hg2_Vert g →₀ ℤ) ⧸ LinearMap.range (hg2_bd1 ℤ g)) ≃ₗ[ℤ] ℤ) := by
  classical
  let p := LinearMap.range (hg2_bd1 ℤ g)
  let q := p.mkQ
  let v : hg2_Vert g := Sum.inl 1
  let a : (hg2_Vert g →₀ ℤ) →ₗ[ℤ] ℤ :=
    Finsupp.linearCombination ℤ (fun _ => (1 : ℤ))
  have ha : a ∘ₗ hg2_bd1 ℤ g = 0 := by
    apply Finsupp.lhom_ext
    intro ε n
    simp [a, hg2_bd1]
  let aq : ((hg2_Vert g →₀ ℤ) ⧸ p) →ₗ[ℤ] ℤ := p.liftQ a (by
    intro z hz
    obtain ⟨w, rfl⟩ := hz
    exact LinearMap.congr_fun ha w)
  have hed (ε : hg2_Edge G r) :
      q (Finsupp.single (hg2_tgt g ε) 1) = q (Finsupp.single (hg2_src g ε) 1) := by
    apply sub_eq_zero.mp
    rw [← map_sub]
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    exact ⟨Finsupp.single ε 1, by simp [hg2_bd1]⟩
  have he (i : Fin r) (x : G) :
      q (Finsupp.single (Sum.inr (Sum.inr ⟨i, (x : G ⧸ Subgroup.zpowers (g i))⟩)) 1) =
        q (Finsupp.single (Sum.inl x) 1) := hed (Sum.inl (i, x))
  have hm (i : Fin r) (x : G) :
      q (Finsupp.single (Sum.inl (x * g i)) 1) = q (Finsupp.single (Sum.inl x) 1) := by
    rw [← he i (x * g i), ← he i x]
    have hc : ((x * g i : G) : G ⧸ Subgroup.zpowers (g i)) =
        (x : G ⧸ Subgroup.zpowers (g i)) := QuotientGroup.eq.mpr (by simp)
    rw [hc]
  have hinv (y : G) : ∀ x : G,
      q (Finsupp.single (Sum.inl (x * y)) 1) = q (Finsupp.single (Sum.inl x) 1) := by
    have hy : y ∈ Subgroup.closure (Set.range g) := by rw [hg]; trivial
    induction hy using Subgroup.closure_induction with
    | mem z hz => obtain ⟨i, rfl⟩ := hz; exact hm i
    | one => intro x; simp
    | mul a b ha hb ia ib => intro x; rw [← mul_assoc, ib, ia]
    | inv a ha ia =>
      intro x
      have h := ia (x * a⁻¹)
      simpa only [inv_mul_cancel_right] using h.symm
  have hbase (x : G) : q (Finsupp.single (Sum.inl x) 1) = q (Finsupp.single v 1) := by
    simpa [v] using hinv x 1
  have hall (u : hg2_Vert g) : q (Finsupp.single u 1) = q (Finsupp.single v 1) := by
    rcases u with x | x | ⟨i, c⟩
    · exact hbase x
    · have h := hed (Sum.inr (Sum.inl ((0 : Fin r), x)))
      simpa [hg2_tgt, hg2_src, hg2_Q] using h.trans (hbase x)
    · induction c using QuotientGroup.induction_on with
      | H x => exact (he i x).trans (hbase x)
  let f : ℤ →ₗ[ℤ] ((hg2_Vert g →₀ ℤ) ⧸ p) := q ∘ₗ Finsupp.lsingle v
  have hf (n : ℤ) : aq (f n) = n := by
    simp [f, aq, q, a]
  have hsur : Function.Surjective f := by
    intro x
    obtain ⟨z, rfl⟩ := p.mkQ_surjective x
    induction z using Finsupp.induction_linear with
    | zero => exact ⟨0, by simp [f, q]⟩
    | add z w hz hw =>
      obtain ⟨a, ha⟩ := hz
      obtain ⟨b, hb⟩ := hw
      exact ⟨a + b, by rw [map_add, ha, hb, map_add]⟩
    | single u n =>
      refine ⟨n, ?_⟩
      change f n = q (Finsupp.single u n)
      have h := congrArg (fun t => n • t) (hall u)
      simpa [f, ← map_smul, ← Finsupp.single_smul] using h.symm
  exact ⟨(LinearEquiv.ofBijective f ⟨fun x y h => by simpa only [hf] using congrArg aq h,
    hsur⟩).symm⟩

theorem hg2_H1_rank_aux {G : Type*} [Group G] [Finite G] {r : ℕ} (g : Fin r → G)
    (hprod : (List.ofFn g).prod = 1) (hg : Subgroup.closure (Set.range g) = ⊤) :
    Module.Free ℤ (hg2_H1 ℤ g) ∧ Module.Finite ℤ (hg2_H1 ℤ g) ∧
      (Module.finrank ℤ (hg2_H1 ℤ g) : ℤ) + 2 * Nat.card G +
          ∑ i, (Nat.card (G ⧸ Subgroup.zpowers (g i)) : ℤ) =
        r * Nat.card G + 2 := by
  classical
  obtain ⟨hfree, hfinite⟩ := hg2_H1_finite_free g
  refine ⟨hfree, hfinite, ?_⟩
  letI := Fintype.ofFinite G
  cases r with
  | zero =>
    have hbot : (⊥ : Subgroup G) = ⊤ := by simpa using hg
    have hx (x : G) : x = 1 := by
      have hmem : x ∈ (⊥ : Subgroup G) := by rw [hbot]; trivial
      exact hmem
    letI : Subsingleton G := ⟨fun x y => (hx x).trans (hx y).symm⟩
    have hc : Nat.card G = 1 := Nat.card_unique
    have hf : Module.finrank ℤ (hg2_H1 ℤ g) = 0 := Module.finrank_zero_of_subsingleton
    simp only [hf, Nat.cast_zero, zero_mul, Finset.univ_eq_empty, Finset.sum_empty,
      add_zero, zero_add]
    have hc' : Fintype.card G = 1 := by simpa only [Nat.card_eq_fintype_card] using hc
    norm_num [Nat.card_eq_fintype_card, hc']
  | succ n =>
    letI : Fintype (hg2_Vert g) := Fintype.ofFinite _
    have hinc : LinearMap.range (hg2_bd2 ℤ g) ≤ LinearMap.ker (hg2_bd1 ℤ g) :=
      LinearMap.range_le_ker_iff.mpr (hg2_boundary_comp_aux ℤ g hprod)
    have h1 := LinearMap.finrank_range_add_finrank_ker (hg2_bd1 ℤ g)
    have h2 := LinearMap.finrank_range_add_finrank_ker (hg2_bd2 ℤ g)
    have h0 := (LinearMap.range (hg2_bd1 ℤ g)).finrank_quotient_add_finrank
    have hh := ((LinearMap.range (hg2_bd2 ℤ g)).comap
      (LinearMap.ker (hg2_bd1 ℤ g)).subtype).finrank_quotient_add_finrank
    have hcomap := (Submodule.comapSubtypeEquivOfLe hinc).finrank_eq
    change Module.finrank ℤ (hg2_H1 ℤ g) + _ = _ at hh
    rw [hcomap] at hh
    obtain ⟨e0⟩ := hg2_H0_equiv g hg
    have hf0 : Module.finrank ℤ ((hg2_Vert g →₀ ℤ) ⧸ LinearMap.range (hg2_bd1 ℤ g)) = 1 := by
      rw [e0.finrank_eq]; simp
    rw [hf0] at h0
    have hor : hg2_orient (G := G) (r := n + 1) ≠ 0 := by
      intro h
      have hv := (hg2_orient_coeffs (0 : Fin (n + 1)) (1 : G)).1
      rw [h, Finsupp.zero_apply] at hv
      norm_num at hv
    have hf2 : Module.finrank ℤ (LinearMap.ker (hg2_bd2 ℤ g)) = 1 := by
      rw [hg2_cycles2_aux g hprod hg,
        ← (LinearEquiv.toSpanNonzeroSingleton ℤ _ hg2_orient hor).finrank_eq]
      simp
    rw [hf2] at h2
    have hc1 : Module.finrank ℤ (hg2_Edge G (n + 1) →₀ ℤ) = 3 * ((n + 1) * Nat.card G) := by
      simp [Module.finrank_finsupp_self, hg2_Edge, Nat.card_eq_fintype_card]; omega
    have hc2 : Module.finrank ℤ (hg2_Tri G (n + 1) →₀ ℤ) = 2 * ((n + 1) * Nat.card G) := by
      simp [Module.finrank_finsupp_self, hg2_Tri, Nat.card_eq_fintype_card]; omega
    have hcv : Module.finrank ℤ (hg2_Vert g →₀ ℤ) =
        2 * Nat.card G + ∑ i, Nat.card (G ⧸ Subgroup.zpowers (g i)) := by
      rw [Module.finrank_finsupp_self, ← Nat.card_eq_fintype_card]
      simp only [hg2_Vert, Nat.card_sum, Nat.card_sigma]
      omega
    rw [hc1] at h1
    rw [hc2] at h2
    rw [hcv] at h0
    push_cast
    exact_mod_cast (by omega : Module.finrank ℤ (hg2_H1 ℤ g) + 2 * Nat.card G +
      ∑ i, Nat.card (G ⧸ Subgroup.zpowers (g i)) = (n + 1) * Nat.card G + 2)

theorem hg2_graph_boundary_split {V E : Type*} (src tgt : E → V)
    (b : (E →₀ ℤ) →ₗ[ℤ] (V →₀ ℤ))
    (hb : ∀ e, b (Finsupp.single e 1) = Finsupp.single (tgt e) 1 - Finsupp.single (src e) 1) :
    ∃ d : (V →₀ ℤ) →ₗ[ℤ] (E →₀ ℤ), b ∘ₗ d ∘ₗ b = b := by
  classical
  let p := LinearMap.range b
  let q := p.mkQ
  let f : V → (V →₀ ℤ) ⧸ p := fun v => q (Finsupp.single v 1)
  let S : Setoid V := Setoid.ker f
  let rep : V → V := fun v => Quotient.out (Quotient.mk S v)
  have hrep (v : V) : f (rep v) = f v :=
    Quotient.exact (Quotient.out_eq (Quotient.mk S v))
  have hmem (v : V) : Finsupp.single v 1 - Finsupp.single (rep v) 1 ∈ p := by
    apply (Submodule.Quotient.mk_eq_zero p).mp
    change q (Finsupp.single v 1 - Finsupp.single (rep v) 1) = 0
    rw [map_sub]
    exact sub_eq_zero.mpr (hrep v).symm
  choose c hc using hmem
  let d : (V →₀ ℤ) →ₗ[ℤ] (E →₀ ℤ) := Finsupp.linearCombination ℤ c
  refine ⟨d, ?_⟩
  apply Finsupp.lhom_ext
  intro e n
  have hed : f (tgt e) = f (src e) := by
    apply sub_eq_zero.mp
    change q (Finsupp.single (tgt e) 1) - q (Finsupp.single (src e) 1) = 0
    rw [← map_sub, ← hb]
    exact (Submodule.Quotient.mk_eq_zero p).mpr ⟨_, rfl⟩
  have her : rep (tgt e) = rep (src e) :=
    congrArg Quotient.out (Quotient.sound (show S (tgt e) (src e) from hed))
  have hsingle : Finsupp.single e n = n • Finsupp.single e 1 := by simp
  rw [hsingle]
  simp only [LinearMap.comp_apply, map_smul]
  congr 1
  rw [hb]
  simp only [map_sub, d, Finsupp.linearCombination_single, one_smul, hc, her]
  abel

def hg2_evaluation (I : Type*) (K : Type*) [Field K] :
    (I → K) →ₗ[K] ((I →₀ ℤ) →ₗ[ℤ] K) where
  toFun := Finsupp.linearCombination ℤ
  map_add' c d := by
    apply Finsupp.lhom_ext
    intro i n
    simp [add_smul]
  map_smul' a c := by
    apply Finsupp.lhom_ext
    intro i n
    simp [mul_left_comm]

theorem hg2_evaluation_single {I K : Type*} [Field K] (c : I → K) (i : I) (n : ℤ) :
    hg2_evaluation I K c (Finsupp.single i n) = n • c i := by
  simp [hg2_evaluation]

theorem hg2_evaluation_bd2 (K : Type*) [Field K] {G : Type*} [Group G] {r : ℕ}
    (g : Fin r → G) (c : hg2_Edge G r → K) :
    hg2_evaluation _ K c ∘ₗ hg2_bd2 ℤ g = hg2_evaluation _ K (hg2_delta1 K K g c) := by
  apply Finsupp.lhom_ext
  intro τ n
  simp [hg2_bd2, hg2_delta1, LinearMap.funLeft, hg2_evaluation, smul_add, smul_sub]

theorem hg2_evaluation_bd1 (K : Type*) [Field K] {G : Type*} [Group G] {r : ℕ}
    (g : Fin r → G) (c : hg2_Vert g → K) :
    hg2_evaluation _ K c ∘ₗ hg2_bd1 ℤ g = hg2_evaluation _ K (hg2_delta0 K K g c) := by
  apply Finsupp.lhom_ext
  intro ε n
  simp [hg2_bd1, hg2_delta0, LinearMap.funLeft, hg2_evaluation, smul_sub]

def hg2_cocycleEval (K : Type*) [Field K] {G : Type*} [Group G] {r : ℕ}
    (g : Fin r → G) :
    LinearMap.ker (hg2_delta1 K K g) →ₗ[K] (hg2_H1 ℤ g →ₗ[ℤ] K) where
  toFun c := ((LinearMap.range (hg2_bd2 ℤ g)).comap (LinearMap.ker (hg2_bd1 ℤ g)).subtype).liftQ
    ((hg2_evaluation _ K c.1).comp (LinearMap.ker (hg2_bd1 ℤ g)).subtype) (by
      intro z hz
      obtain ⟨w, hw⟩ := hz
      change hg2_evaluation _ K c.1 z.1 = 0
      change hg2_bd2 ℤ g w = z.1 at hw
      rw [← hw]
      have h := LinearMap.congr_fun (hg2_evaluation_bd2 K g c.1) w
      simpa only [LinearMap.comp_apply, LinearMap.mem_ker.mp c.2, map_zero, LinearMap.zero_apply] using h)
  map_add' c d := by
    apply LinearMap.ext
    intro x
    obtain ⟨z, rfl⟩ := Submodule.mkQ_surjective _ x
    simp [Submodule.liftQ_apply, map_add]
  map_smul' a c := by
    apply LinearMap.ext
    intro x
    obtain ⟨z, rfl⟩ := Submodule.mkQ_surjective _ x
    simp [Submodule.liftQ_apply, map_smul]

theorem hg2_cocycleEval_apply (K : Type*) [Field K] {G : Type*} [Group G] {r : ℕ}
    (g : Fin r → G) (c : LinearMap.ker (hg2_delta1 K K g))
    (z : LinearMap.ker (hg2_bd1 ℤ g)) :
    hg2_cocycleEval K g c (Submodule.Quotient.mk z) = hg2_evaluation _ K c.1 z.1 := rfl

theorem hg2_cocycleEval_coboundary (K : Type*) [Field K] {G : Type*} [Group G] {r : ℕ}
    (g : Fin r → G) (c : LinearMap.ker (hg2_delta1 K K g))
    (hc : c.1 ∈ LinearMap.range (hg2_delta0 K K g)) : hg2_cocycleEval K g c = 0 := by
  obtain ⟨φ, hφ⟩ := hc
  apply LinearMap.ext
  intro x
  obtain ⟨z, rfl⟩ := Submodule.mkQ_surjective _ x
  change hg2_evaluation _ K c.1 z.1 = 0
  rw [← hφ]
  have h := LinearMap.congr_fun (hg2_evaluation_bd1 K g φ) z.1
  simpa only [LinearMap.comp_apply, LinearMap.mem_ker.mp z.2, map_zero] using h.symm

def hg2_uctMap (K : Type*) [Field K] {G : Type*} [Group G] {r : ℕ} (g : Fin r → G) :
    hg2_coH1 K g →ₗ[K] (hg2_H1 ℤ g →ₗ[ℤ] K) :=
  ((LinearMap.range (hg2_delta0 K K g)).comap (LinearMap.ker (hg2_delta1 K K g)).subtype).liftQ
    (hg2_cocycleEval K g) (fun c hc => hg2_cocycleEval_coboundary K g c hc)

theorem hg2_uctMap_injective (K : Type*) [Field K] {G : Type*} [Group G] {r : ℕ}
    (g : Fin r → G) : Function.Injective (hg2_uctMap K g) := by
  classical
  obtain ⟨d, hd⟩ := hg2_graph_boundary_split (hg2_src g) (hg2_tgt g) (hg2_bd1 ℤ g)
    (fun ε => by simp [hg2_bd1])
  apply LinearMap.ker_eq_bot.mp
  apply eq_bot_iff.mpr
  intro x hx
  change x = 0
  obtain ⟨c, rfl⟩ := Submodule.mkQ_surjective _ x
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  change c.1 ∈ LinearMap.range (hg2_delta0 K K g)
  have hc : hg2_cocycleEval K g c = 0 := hx
  let φ : hg2_Vert g → K := fun v => hg2_evaluation _ K c.1 (d (Finsupp.single v 1))
  refine ⟨φ, ?_⟩
  ext ε
  let z := Finsupp.single ε 1 - d (hg2_bd1 ℤ g (Finsupp.single ε 1))
  have hz : z ∈ LinearMap.ker (hg2_bd1 ℤ g) := by
    change hg2_bd1 ℤ g z = 0
    have h := LinearMap.congr_fun hd (Finsupp.single ε 1)
    simpa only [z, map_sub, LinearMap.comp_apply, sub_eq_zero] using h.symm
  have h := congrArg (fun f : hg2_H1 ℤ g →ₗ[ℤ] K => f (Submodule.Quotient.mk ⟨z, hz⟩)) hc
  change hg2_evaluation _ K c.1 z = 0 at h
  simp only [z, map_sub, hg2_evaluation_single, one_smul] at h
  have hh : hg2_evaluation _ K c.1 (d (hg2_bd1 ℤ g (Finsupp.single ε 1))) =
      φ (hg2_tgt g ε) - φ (hg2_src g ε) := by
    simp [hg2_bd1, φ]
  rw [hh] at h
  change φ (hg2_tgt g ε) - φ (hg2_src g ε) = c.1 ε
  exact (sub_eq_zero.mp h).symm

theorem hg2_uctMap_surjective (K : Type*) [Field K] {G : Type*} [Group G] {r : ℕ}
    (g : Fin r → G) (hprod : (List.ofFn g).prod = 1) :
    Function.Surjective (hg2_uctMap K g) := by
  classical
  obtain ⟨d, hd⟩ := hg2_graph_boundary_split (hg2_src g) (hg2_tgt g) (hg2_bd1 ℤ g)
    (fun ε => by simp [hg2_bd1])
  let P : (hg2_Edge G r →₀ ℤ) →ₗ[ℤ] LinearMap.ker (hg2_bd1 ℤ g) :=
    (LinearMap.id - d ∘ₗ hg2_bd1 ℤ g).codRestrict _ (by
      intro z
      change hg2_bd1 ℤ g (z - d (hg2_bd1 ℤ g z)) = 0
      rw [map_sub]
      exact sub_eq_zero.mpr (LinearMap.congr_fun hd z).symm)
  have hP (z : hg2_Edge G r →₀ ℤ) (hz : hg2_bd1 ℤ g z = 0) : P z = ⟨z, hz⟩ := by
    apply Subtype.ext
    simp [P, hz]
  intro f
  let f' : (hg2_Edge G r →₀ ℤ) →ₗ[ℤ] K :=
    f ∘ₗ (Submodule.mkQ _) ∘ₗ P
  let c : hg2_Edge G r → K := fun ε => f' (Finsupp.single ε 1)
  have heval : hg2_evaluation _ K c = f' := by
    apply Finsupp.lhom_ext
    intro ε n
    rw [hg2_evaluation_single]
    change n • f' (Finsupp.single ε 1) = f' (Finsupp.single ε n)
    rw [← map_smul]
    congr 1
    simp
  have hbound : f' ∘ₗ hg2_bd2 ℤ g = 0 := by
    apply LinearMap.ext
    intro w
    have hz : hg2_bd1 ℤ g (hg2_bd2 ℤ g w) = 0 :=
      LinearMap.congr_fun (hg2_boundary_comp_aux ℤ g hprod) w
    change f (Submodule.Quotient.mk (P (hg2_bd2 ℤ g w))) = 0
    rw [hP _ hz]
    have hzero : (Submodule.Quotient.mk ⟨hg2_bd2 ℤ g w, hz⟩ : hg2_H1 ℤ g) = 0 := by
      apply (Submodule.Quotient.mk_eq_zero _).mpr
      exact ⟨w, rfl⟩
    rw [hzero, map_zero]
  have hc : c ∈ LinearMap.ker (hg2_delta1 K K g) := by
    change hg2_delta1 K K g c = 0
    ext τ
    have h := LinearMap.congr_fun (hg2_evaluation_bd2 K g c) (Finsupp.single τ 1)
    rw [heval] at h
    have h' := LinearMap.congr_fun hbound (Finsupp.single τ 1)
    rw [LinearMap.comp_apply] at h h'
    rw [h', hg2_evaluation_single, one_smul] at h
    exact h.symm
  refine ⟨Submodule.Quotient.mk ⟨c, hc⟩, ?_⟩
  apply LinearMap.ext
  intro x
  obtain ⟨z, rfl⟩ := Submodule.mkQ_surjective _ x
  change hg2_evaluation _ K c z.1 = f (Submodule.Quotient.mk z)
  rw [heval]
  change f (Submodule.Quotient.mk (P z.1)) = f (Submodule.Quotient.mk z)
  rw [hP z.1 (LinearMap.mem_ker.mp z.2)]

theorem hg2_uct_aux (K : Type*) [Field K] {G : Type*} [Group G] {r : ℕ} (g : Fin r → G)
    (hprod : (List.ofFn g).prod = 1) :
    ∃ e : hg2_coH1 K g ≃ₗ[K] (hg2_H1 ℤ g →ₗ[ℤ] K),
      ∀ (c : LinearMap.ker (hg2_delta1 K K g)) (z : LinearMap.ker (hg2_bd1 ℤ g)),
        e (Submodule.Quotient.mk c) (Submodule.Quotient.mk z) = hg2_pair K c.1 z.1 := by
  let e := LinearEquiv.ofBijective (hg2_uctMap K g)
    ⟨hg2_uctMap_injective K g, hg2_uctMap_surjective K g hprod⟩
  refine ⟨e, ?_⟩
  intro c z
  change hg2_evaluation _ K c.1 z.1 = hg2_pair K c.1 z.1
  change Finsupp.linearCombination ℤ c.1 z.1 = hg2_pair K c.1 z.1
  simp [Finsupp.linearCombination_apply, hg2_pair]

theorem hg2_chainAct1_mul (R : Type*) [CommRing R] {G : Type*} [Group G] {r : ℕ}
    (h k : G) : hg2_chainAct1 R (r := r) h ∘ₗ hg2_chainAct1 R k = hg2_chainAct1 R (h * k) := by
  apply Finsupp.lhom_ext
  intro ε a
  rcases ε with ⟨i, x⟩ | ⟨i, x⟩ | ⟨i, x⟩ <;>
    simp [hg2_chainAct1, hg2_actEdge, mul_assoc]

theorem hg2_H1act_mul (R : Type*) [CommRing R] {G : Type*} [Group G] {r : ℕ}
    (g : Fin r → G) (h k : G) : hg2_H1act R g h ∘ₗ hg2_H1act R g k = hg2_H1act R g (h * k) := by
  apply LinearMap.ext
  intro x
  obtain ⟨z, rfl⟩ := Submodule.mkQ_surjective _ x
  change Submodule.Quotient.mk _ = Submodule.Quotient.mk _
  congr 1
  apply Subtype.ext
  exact LinearMap.congr_fun (hg2_chainAct1_mul R h k) z.1

theorem hg2_projector_square (x : hg2_H1 ℤ b4b_root) :
    hg2_projector (hg2_projector x) = b4b_projectorDenominator • hg2_projector x := by
  classical
  have hcomp (g k : b4b_Group) (z : hg2_H1 ℤ b4b_root) :
      hg2_H1act ℤ b4b_root g (hg2_H1act ℤ b4b_root k z) =
        hg2_H1act ℤ b4b_root (g * k) z :=
    LinearMap.congr_fun (hg2_H1act_mul ℤ b4b_root g k) z
  have hreindex (g : b4b_Group) :
      (∑ k : b4b_Group, (b4b_projectorCoeff g * b4b_projectorCoeff k) •
        hg2_H1act ℤ b4b_root (g * k) x) =
      ∑ h : b4b_Group, (b4b_projectorCoeff g * b4b_projectorCoeff (g⁻¹ * h)) •
        hg2_H1act ℤ b4b_root h x := by
    simpa only [inv_mul_cancel_left] using
      Fintype.sum_bijective (g * ·) (Group.mulLeft_bijective g) _ _ (fun k => by simp)
  simp only [hg2_projector, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul,
    Finset.smul_sum, smul_smul, hcomp]
  rw [Finset.sum_comm]
  conv_lhs =>
    enter [2, g, 2, k]
    rw [mul_comm (b4b_projectorCoeff k) (b4b_projectorCoeff g)]
  simp_rw [hreindex]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_smul, b63l_projector_convolution]

theorem hg2_H1act_one (R : Type*) [CommRing R] {G : Type*} [Group G] {r : ℕ}
    (g : Fin r → G) : hg2_H1act R g 1 = LinearMap.id := by
  have hchain : hg2_chainAct1 R (G := G) (r := r) 1 = LinearMap.id := by
    apply Finsupp.lhom_ext
    intro ε a
    rcases ε with ⟨i, x⟩ | ⟨i, x⟩ | ⟨i, x⟩ <;>
      simp [hg2_chainAct1, hg2_actEdge]
  apply LinearMap.ext
  intro x
  obtain ⟨z, rfl⟩ := Submodule.mkQ_surjective _ x
  change Submodule.Quotient.mk _ = Submodule.Quotient.mk z
  congr 1
  apply Subtype.ext
  exact LinearMap.congr_fun hchain z.1

def hg2_H1representation (R : Type*) [CommRing R] {G : Type*} [Group G] {r : ℕ}
    (g : Fin r → G) : Representation R G (hg2_H1 R g) where
  toFun := hg2_H1act R g
  map_one' := hg2_H1act_one R g
  map_mul' h k := (hg2_H1act_mul R g h k).symm

theorem hg2_projector_baseChange_square :
    hg2_projector.baseChange ℚ ∘ₗ hg2_projector.baseChange ℚ =
      (b4b_projectorDenominator : ℚ) • hg2_projector.baseChange ℚ := by
  have h : hg2_projector ∘ₗ hg2_projector = b4b_projectorDenominator • hg2_projector := by
    apply LinearMap.ext
    intro x
    exact hg2_projector_square x
  have h' := congrArg (fun f : Module.End ℤ (hg2_H1 ℤ b4b_root) => f.baseChange ℚ) h
  simpa only [LinearMap.baseChange_comp, LinearMap.baseChange_smul,
    Int.cast_smul_eq_zsmul] using h'

theorem hg2_projector_rank_rational :
    Module.finrank ℚ (LinearMap.range (hg2_projector.baseChange ℚ)) =
      Module.finrank ℤ (LinearMap.range hg2_projector) := by
  letI := (hg2_H1_finite_free b4b_root).1
  letI := (hg2_H1_finite_free b4b_root).2
  have hrange : LinearMap.range ((LinearMap.range hg2_projector).subtype.baseChange ℚ) =
      LinearMap.range (hg2_projector.baseChange ℚ) := by
    have hsurj : Function.Surjective (hg2_projector.rangeRestrict.baseChange ℚ) :=
      LinearMap.baseChange_surjective ℚ
        (LinearMap.range_eq_top.mp (LinearMap.range_rangeRestrict hg2_projector))
    have hfac : hg2_projector.baseChange ℚ =
        (LinearMap.range hg2_projector).subtype.baseChange ℚ ∘ₗ
          hg2_projector.rangeRestrict.baseChange ℚ := by
      rw [← LinearMap.baseChange_comp]
      rfl
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      obtain ⟨z, rfl⟩ := hsurj x
      exact ⟨z, by rw [hfac, LinearMap.comp_apply]⟩
    · rintro ⟨x, rfl⟩
      exact ⟨hg2_projector.rangeRestrict.baseChange ℚ x, by rw [hfac, LinearMap.comp_apply]⟩
  change Module.finrank ℚ _ = _
  rw [← hrange]
  change Module.finrank ℚ ((LinearMap.range hg2_projector).baseChange ℚ) = _
  rw [← (Submodule.toBaseChange.toLinearEquiv ℚ (LinearMap.range hg2_projector)).finrank_eq]
  exact Module.finrank_baseChange

theorem hg2_projector_trace_rank :
    LinearMap.trace ℚ (ℚ ⊗[ℤ] hg2_H1 ℤ b4b_root) (hg2_projector.baseChange ℚ) =
      (b4b_projectorDenominator : ℚ) * Module.finrank ℤ (LinearMap.range hg2_projector) := by
  letI := (hg2_H1_finite_free b4b_root).1
  letI := (hg2_H1_finite_free b4b_root).2
  let D : ℚ := b4b_projectorDenominator
  have hD : D ≠ 0 := by norm_num [D, b4b_projectorDenominator]
  let e := D⁻¹ • hg2_projector.baseChange ℚ
  have he : IsIdempotentElem e := by
    change e ∘ₗ e = e
    dsimp only [e]
    rw [LinearMap.smul_comp, LinearMap.comp_smul, hg2_projector_baseChange_square]
    simp only [smul_smul]
    change (D⁻¹ * (D⁻¹ * D)) • _ = D⁻¹ • _
    rw [inv_mul_cancel₀ hD, mul_one]
  have hrange : LinearMap.range e = LinearMap.range (hg2_projector.baseChange ℚ) :=
    LinearMap.range_smul _ _ (inv_ne_zero hD)
  calc
    _ = D * LinearMap.trace ℚ _ e := by simp [e, hD]
    _ = D * (Module.finrank ℚ (LinearMap.range e) : ℚ) := by rw [(LinearMap.IsIdempotentElem.isProj_range e he).trace]
    _ = _ := by rw [hrange, hg2_projector_rank_rational]

def hg2_augmentation {G : Type*} [Group G] {r : ℕ} (g : Fin r → G) :
    (hg2_Vert g →₀ ℤ) →ₗ[ℤ] ℤ := Finsupp.linearCombination ℤ (fun _ => (1 : ℤ))

theorem hg2_augmentation_bd1 {G : Type*} [Group G] {r : ℕ} (g : Fin r → G) :
    hg2_augmentation g ∘ₗ hg2_bd1 ℤ g = 0 := by
  apply Finsupp.lhom_ext
  intro ε n
  simp [hg2_augmentation, hg2_bd1]

theorem hg2_bd1_range_augmentation {G : Type*} [Group G] [Finite G] {r : ℕ}
    [NeZero r] (g : Fin r → G) (hg : Subgroup.closure (Set.range g) = ⊤) :
    LinearMap.range (hg2_bd1 ℤ g) = LinearMap.ker (hg2_augmentation g) := by
  classical
  let p := LinearMap.range (hg2_bd1 ℤ g)
  let a := hg2_augmentation g
  let aq : ((hg2_Vert g →₀ ℤ) ⧸ p) →ₗ[ℤ] ℤ :=
    p.liftQ a (LinearMap.range_le_ker_iff.mpr (hg2_augmentation_bd1 g))
  obtain ⟨e⟩ := hg2_H0_equiv g hg
  letI : Module.Free ℤ ((hg2_Vert g →₀ ℤ) ⧸ p) := Module.Free.of_equiv e.symm
  have hs : Function.Surjective aq := by
    intro n
    refine ⟨p.mkQ (Finsupp.single (Sum.inl (1 : G)) n), ?_⟩
    simp [aq, a, hg2_augmentation]
  have hd : Module.finrank ℤ ((hg2_Vert g →₀ ℤ) ⧸ p) = 1 := by
    rw [e.finrank_eq]; simp
  have hr := LinearMap.finrank_range_add_finrank_ker aq
  rw [LinearMap.range_eq_top.mpr hs, finrank_top, Module.finrank_self, hd] at hr
  have hk : Module.finrank ℤ (LinearMap.ker aq) = 0 := by omega
  have hsub : Subsingleton (LinearMap.ker aq) := (Module.finrank_eq_zero_iff_of_free ℤ _).mp hk
  have hi : Function.Injective aq := LinearMap.ker_eq_bot.mp (Submodule.subsingleton_iff_eq_bot.mp hsub)
  apply le_antisymm (LinearMap.range_le_ker_iff.mpr (hg2_augmentation_bd1 g))
  intro z hz
  apply (Submodule.Quotient.mk_eq_zero p).mp
  apply hi
  change a z = 0
  exact hz

theorem hg2_orient_act {G : Type*} [Group G] [Fintype G] {r : ℕ} (h : G) :
    Finsupp.lmapDomain ℤ ℤ (hg2_actTri (r := r) h) hg2_orient = hg2_orient := by
  classical
  simp only [hg2_orient, map_sum, map_sub, Finsupp.lmapDomain_apply,
    Finsupp.mapDomain_single, hg2_actTri]
  apply Finset.sum_congr rfl
  intro i hi
  exact Fintype.sum_equiv (Equiv.mulLeft h) _ _ (fun x => rfl)

def hg2_weightedCells (I : Type*) (act : b4b_Group → I → I) : Module.End ℤ (I →₀ ℤ) :=
  ∑ h : b4b_Group, b4b_projectorCoeff h • Finsupp.lmapDomain ℤ ℤ (act h)

theorem hg2_projector_chain_trace_balance :
    LinearMap.trace ℤ (hg2_H1 ℤ b4b_root) hg2_projector +
      LinearMap.trace ℤ (hg2_Vert b4b_root →₀ ℤ) (hg2_weightedCells _ (hg2_actVert b4b_root)) +
      LinearMap.trace ℤ (hg2_Tri b4b_Group 13 →₀ ℤ) (hg2_weightedCells _ hg2_actTri) =
      LinearMap.trace ℤ (hg2_Edge b4b_Group 13 →₀ ℤ) (hg2_weightedCells _ hg2_actEdge) := by
  classical
  letI := (hg2_H1_finite_free b4b_root).1
  letI := (hg2_H1_finite_free b4b_root).2
  apply hg2_trace_complex (hg2_bd2 ℤ b4b_root) (hg2_bd1 ℤ b4b_root)
    (hg2_boundary_comp_aux ℤ b4b_root b63d_root_product) (hg2_augmentation b4b_root)
    (fun n => ⟨Finsupp.single (Sum.inl 1) n, by simp [hg2_augmentation]⟩)
    (hg2_bd1_range_augmentation b4b_root b63d_root_subgroup)
    (Submodule.mkQ _) (Submodule.mkQ_surjective _) (Submodule.ker_mkQ _)
  · apply LinearMap.ext
    intro w
    simp only [hg2_weightedCells, LinearMap.comp_apply, LinearMap.sum_apply,
      LinearMap.smul_apply, map_sum, map_smul]
    apply Finset.sum_congr rfl
    intro h hh
    exact congrArg (fun z => b4b_projectorCoeff h • z) (hg2_bd2_act ℤ b4b_root h w)
  · apply LinearMap.ext
    intro w
    simp only [hg2_weightedCells, LinearMap.comp_apply, LinearMap.sum_apply,
      LinearMap.smul_apply, map_sum, map_smul]
    apply Finset.sum_congr rfl
    intro h hh
    exact congrArg (fun z => b4b_projectorCoeff h • z) (hg2_bd1_act ℤ b4b_root h w)
  · apply Finsupp.lhom_ext
    intro v n
    simp only [LinearMap.comp_apply, LinearMap.zero_apply, hg2_weightedCells,
      LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul,
      Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, hg2_augmentation, Finsupp.linearCombination_single,
      smul_eq_mul, mul_one, ← Finset.sum_mul, hg2_projectorCoeff_sum, zero_mul]
  · intro w hw
    rw [hg2_cycles2_aux b4b_root b63d_root_product b63d_root_subgroup] at hw
    obtain ⟨n, rfl⟩ := Submodule.mem_span_singleton.mp hw
    simp only [hg2_weightedCells, LinearMap.sum_apply, LinearMap.smul_apply, map_smul,
      hg2_orient_act]
    rw [← Finset.sum_smul, hg2_projectorCoeff_sum, zero_smul]
    simp
  · intro z hz
    let zh (h : b4b_Group) : LinearMap.ker (hg2_bd1 ℤ b4b_root) :=
      ⟨hg2_chainAct1 ℤ h z.1, by
        rw [LinearMap.mem_ker, hg2_bd1_act, LinearMap.mem_ker.mp z.2, map_zero]⟩
    have hsum : (⟨hg2_weightedCells _ hg2_actEdge z.1, hz⟩ : LinearMap.ker (hg2_bd1 ℤ b4b_root)) =
        ∑ h : b4b_Group, b4b_projectorCoeff h • zh h := by
      apply Subtype.ext
      simp [hg2_weightedCells, zh, hg2_chainAct1]
    change Submodule.Quotient.mk (⟨hg2_weightedCells _ hg2_actEdge z.1, hz⟩ :
      LinearMap.ker (hg2_bd1 ℤ b4b_root)) = hg2_projector (Submodule.Quotient.mk z)
    rw [hsum]
    change (Submodule.mkQ _) (∑ h : b4b_Group, b4b_projectorCoeff h • zh h) = _
    simp only [map_sum, map_smul, hg2_projector, LinearMap.sum_apply, LinearMap.smul_apply]
    rfl

theorem hg2_projectorCoeff_one : b4b_projectorCoeff 1 = 6 := by
  apply Int.cast_injective (α := ℂ)
  rw [b63l_projectorCoeff_complex]
  norm_num

theorem hg2_weightedCells_trace (I : Type*) [Fintype I] [DecidableEq I]
    (act : b4b_Group → I → I) :
    LinearMap.trace ℤ (I →₀ ℤ) (hg2_weightedCells I act) =
      ∑ h : b4b_Group, b4b_projectorCoeff h * ∑ i : I, if act h i = i then (1 : ℤ) else 0 := by
  simp only [hg2_weightedCells, map_sum, map_smul, hg2_trace_lmapDomain, smul_eq_mul]

theorem hg2_regular_cell_traces :
    LinearMap.trace ℤ (hg2_Edge b4b_Group 13 →₀ ℤ) (hg2_weightedCells _ hg2_actEdge) = 36391680 ∧
    LinearMap.trace ℤ (hg2_Tri b4b_Group 13 →₀ ℤ) (hg2_weightedCells _ hg2_actTri) = 24261120 := by
  classical
  constructor <;> rw [hg2_weightedCells_trace] <;>
    simp only [hg2_Edge, hg2_Tri, Fintype.sum_sum_type, Fintype.sum_prod_type,
      hg2_actEdge, hg2_actTri, Sum.inl.injEq, Sum.inr.injEq, Prod.mk.injEq,
      true_and, mul_eq_right] <;>
    simp [mul_add, mul_ite, Finset.sum_add_distrib, hg2_projectorCoeff_one, b63l_card_group]

theorem hg2_vertex_trace :
    LinearMap.trace ℤ (hg2_Vert b4b_root →₀ ℤ)
      (hg2_weightedCells _ (hg2_actVert b4b_root)) = 10730880 := by
  classical
  have hv (h : b4b_Group) :
      (∑ v : hg2_Vert b4b_root, if hg2_actVert b4b_root h v = v then (1 : ℤ) else 0) =
        (if h = 1 then 311040 else 0) +
          ∑ i : Fin 13, ∑ q : b4b_Group ⧸ Subgroup.zpowers (b4b_root i),
            if h • q = q then (1 : ℤ) else 0 := by
    simp only [hg2_Vert, Fintype.sum_sum_type, Fintype.sum_sigma, hg2_actVert,
      Sum.inl.injEq, Sum.inr.injEq, Sigma.mk.inj_iff, heq_eq_eq, mul_eq_right,
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    by_cases hh : h = 1 <;> simp [hh, b63l_card_group] <;> ring
  rw [hg2_weightedCells_trace]
  simp_rw [hv, mul_add, mul_ite, mul_zero]
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true, hg2_projectorCoeff_one]
  apply Int.cast_injective (α := ℂ)
  push_cast
  conv_lhs =>
    enter [2, 2, h]
    rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [hg2_projector_coset_trace]
  have hn : (∑ i : Fin 13, (b4b_toMatrix (b4b_root i) - 1).rank) = 14 := by
    exact_mod_cast b63d_root_rank_sum
  have hr : (∑ i : Fin 13, ((b4b_toMatrix (b4b_root i) - 1).rank : ℂ)) = 14 := by
    exact_mod_cast hn
  simp only [mul_sub, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, ← mul_assoc, ← Finset.mul_sum]
  rw [hr]
  norm_num [b4b_projectorDenominator]

theorem hg2_projector_rank_aux :
    Module.finrank ℤ (LinearMap.range hg2_projector) = 12 := by
  letI := (hg2_H1_finite_free b4b_root).1
  letI := (hg2_H1_finite_free b4b_root).2
  have hb := hg2_projector_chain_trace_balance
  rw [hg2_vertex_trace, hg2_regular_cell_traces.1, hg2_regular_cell_traces.2] at hb
  have ht : LinearMap.trace ℤ (hg2_H1 ℤ b4b_root) hg2_projector = 1399680 := by
    linarith only [hb]
  have hr := hg2_projector_trace_rank
  rw [LinearMap.trace_baseChange, ht] at hr
  norm_num [b4b_projectorDenominator] at hr
  have hc : (Module.finrank ℤ (LinearMap.range hg2_projector) : ℚ) = 12 := by
    linarith only [hr]
  exact_mod_cast hc

end HodgeLean.Foundations.Program
