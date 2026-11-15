import HodgeLean.Foundations.Program.SchoenTowerHardtCellCharts
import Mathlib.Algebra.MvPolynomial.Equiv
import HodgeLean.Foundations.Program.SchoenTowerHardtCad3FormulaTools

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

theorem s2v_hardt_cad3_band_formulas_aux {n r : ℕ}
    (C : s2v_t11b_Formula n) (ψ : Fin r → C.realize → ℝ)
    (hm : ∀ a, StrictMono (fun q => ψ q a))
    (g : Fin r → s2v_t11b_Formula (n + 1))
    (hg : ∀ q y, y ∈ (g q).realize ↔ ∃ a : C.realize,
      (∀ v, y v.succ = a.val v) ∧ y 0 = ψ q a) :
    ∃ b : Fin (r + 1) → s2v_t11b_Formula (n + 1), ∀ i y, y ∈ (b i).realize ↔ ∃ a : C.realize,
        (∀ v, y v.succ = a.val v) ∧
        (∀ q : Fin r, q.val < i.val → ψ q a < y 0) ∧
        (∀ q : Fin r, i.val ≤ q.val → y 0 < ψ q a) := by
  classical
  have hcmp : ∀ (i : Fin (r + 1)) (q : Fin r),
      ∃ F : s2v_t11b_Formula (n + 1), ∀ y, y ∈ F.realize ↔
        ∃ a : C.realize, (∀ v, y v.succ = a.val v) ∧
          (if q.val < i.val then ψ q a < y 0 else y 0 < ψ q a) := by
    intro i q
    let p : MvPolynomial (Fin ((n + 1) + 1)) ℝ :=
      if q.val < i.val then MvPolynomial.X 0 - MvPolynomial.X (Fin.succ 0)
      else MvPolynomial.X (Fin.succ 0) - MvPolynomial.X 0
    obtain ⟨F, hF⟩ := s2v_hardt_cad3_graph_substitution C (ψ q) (g q) (hg q)
      Fin.succ (.compl (.nonneg p))
    refine ⟨F, ?_⟩
    intro y
    rw [hF]
    apply exists_congr
    intro a
    apply and_congr_right
    intro _
    by_cases h : q.val < i.val <;>
      simp [p, h, s2v_t11b_Formula.realize, sub_nonneg, not_le]
  choose f hf using hcmp
  choose B hB using fun i => s2v_hardt_cad3_finite_inter (f i)
  refine ⟨fun i => .inter (s2v_hardt1_rename Fin.succ C) (B i), ?_⟩
  intro i y
  change (_ ∧ _) ↔ _
  rw [s2v_hardt1_realize_rename, hB]
  constructor
  · rintro ⟨hy, h⟩
    let a : C.realize := ⟨WithLp.toLp 2 (fun v => y v.succ), hy⟩
    have hsign : ∀ q : Fin r,
        if q.val < i.val then ψ q a < y 0 else y 0 < ψ q a := by
      intro q
      obtain ⟨a', ha', hs⟩ := (hf i q y).mp (h q)
      have he : a' = a := by
        apply Subtype.ext
        ext v
        exact (ha' v).symm
      simpa only [he] using hs
    refine ⟨a, (fun _ => rfl), ?_, ?_⟩
    · intro q hq
      simpa only [if_pos hq] using hsign q
    · intro q hq
      simpa only [if_neg (not_lt.mpr hq)] using hsign q
  · rintro ⟨a, ha, hlo, hhi⟩
    have he : WithLp.toLp 2 (fun v => y v.succ) = a.val := by
      ext v
      exact ha v
    refine ⟨he.symm ▸ a.property, ?_⟩
    intro q
    apply (hf i q y).mpr
    refine ⟨a, ha, ?_⟩
    split_ifs with h
    · exact hlo q h
    · exact hhi q (le_of_not_gt h)

theorem s2v_hardt_cad3_cylinder_partition_aux {n r : ℕ}
    (C : s2v_t11b_Formula n) (ψ : Fin r → C.realize → ℝ)
    (hm : ∀ a, StrictMono (fun q => ψ q a))
    (hC : C.realize.Nonempty)
    (g : Fin r → s2v_t11b_Formula (n + 1))
    (hg : ∀ q y, y ∈ (g q).realize ↔ ∃ a : C.realize,
      (∀ v, y v.succ = a.val v) ∧ y 0 = ψ q a)
    (b : Fin (r + 1) → s2v_t11b_Formula (n + 1))
    (hb : ∀ i y, y ∈ (b i).realize ↔ ∃ a : C.realize,
        (∀ v, y v.succ = a.val v) ∧
        (∀ q : Fin r, q.val < i.val → ψ q a < y 0) ∧
        (∀ q : Fin r, i.val ≤ q.val → y 0 < ψ q a)) :
    (∀ i, (b i).realize.Nonempty) ∧ (∀ q, (g q).realize.Nonempty) ∧
    Pairwise (fun i j => Disjoint (b i).realize (b j).realize) ∧
    Pairwise (fun i j => Disjoint (g i).realize (g j).realize) ∧
    (∀ i q, Disjoint (b i).realize (g q).realize) ∧
    (∀ y : EuclideanSpace ℝ (Fin (n + 1)),
      ((∃ i, y ∈ (b i).realize) ∨ (∃ q, y ∈ (g q).realize)) ↔
      ∃ a : C.realize, ∀ v, y v.succ = a.val v) ∧
    (∀ i y, y ∈ (b i).realize →
      WithLp.toLp 2 (fun v => y v.succ) ∈ C.realize) := by
  classical
  have base_eq : ∀ (y : EuclideanSpace ℝ (Fin (n + 1))) (a a' : C.realize),
      (∀ v, y v.succ = a.val v) → (∀ v, y v.succ = a'.val v) → a = a' := by
    intro y a a' ha ha'
    apply Subtype.ext
    ext v
    exact (ha v).symm.trans (ha' v)
  have witness : ∀ (a : C.realize) (i : Fin (r + 1)), ∃ t : ℝ,
      (∀ q : Fin r, q.val < i.val → ψ q a < t) ∧
      (∀ q : Fin r, i.val ≤ q.val → t < ψ q a) := by
    intro a i
    by_cases hi : i.val = 0
    · by_cases hr : r = 0
      · subst r
        exact ⟨0, by simp, by simp⟩
      · let q : Fin r := ⟨0, Nat.pos_of_ne_zero hr⟩
        refine ⟨ψ q a - 1, ?_, ?_⟩
        · intro j hj
          omega
        · intro j hj
          have hle := (hm a).monotone (show q ≤ j by change 0 ≤ j.val; omega)
          linarith
    · let q : Fin r := ⟨i.val - 1, by omega⟩
      by_cases hir : i.val < r
      · let q' : Fin r := ⟨i.val, hir⟩
        have hlt := hm a (show q < q' by change i.val - 1 < i.val; omega)
        refine ⟨(ψ q a + ψ q' a) / 2, ?_, ?_⟩
        · intro j hj
          have hle := (hm a).monotone (show j ≤ q by change j.val ≤ i.val - 1; omega)
          linarith
        · intro j hj
          have hle := (hm a).monotone (show q' ≤ j from hj)
          linarith
      · refine ⟨ψ q a + 1, ?_, ?_⟩
        · intro j hj
          have hle := (hm a).monotone (show j ≤ q by change j.val ≤ i.val - 1; omega)
          linarith
        · intro j hj
          omega
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    obtain ⟨a, ha⟩ := hC
    obtain ⟨t, ht⟩ := witness ⟨a, ha⟩ i
    refine ⟨WithLp.toLp 2 (Fin.cons t (fun v => a v)), (hb _ _).mpr ?_⟩
    exact ⟨⟨a, ha⟩, (fun _ => rfl), ht⟩
  · intro q
    obtain ⟨a, ha⟩ := hC
    refine ⟨WithLp.toLp 2 (Fin.cons (ψ q ⟨a, ha⟩) (fun v => a v)),
      (hg _ _).mpr ?_⟩
    exact ⟨⟨a, ha⟩, (fun _ => rfl), rfl⟩
  · intro i j hij
    apply Set.disjoint_left.mpr
    intro y hyi hyj
    obtain ⟨a, ha, hlo, hhi⟩ := (hb _ _).mp hyi
    obtain ⟨a', ha', hlo', hhi'⟩ := (hb _ _).mp hyj
    have he := base_eq y a a' ha ha'
    subst a'
    rcases lt_or_gt_of_ne hij with hij | hij
    · let q : Fin r := ⟨i.val, by have := j.isLt; change i.val < j.val at hij; omega⟩
      exact (hhi q (by rfl)).asymm (hlo' q hij)
    · let q : Fin r := ⟨j.val, by have := i.isLt; change j.val < i.val at hij; omega⟩
      exact (hhi' q (by rfl)).asymm (hlo q hij)
  · intro i j hij
    apply Set.disjoint_left.mpr
    intro y hyi hyj
    obtain ⟨a, ha, hi⟩ := (hg _ _).mp hyi
    obtain ⟨a', ha', hj⟩ := (hg _ _).mp hyj
    have he := base_eq y a a' ha ha'
    subst a'
    exact hij ((hm a).injective (hi.symm.trans hj))
  · intro i q
    apply Set.disjoint_left.mpr
    intro y hyi hyq
    obtain ⟨a, ha, hlo, hhi⟩ := (hb _ _).mp hyi
    obtain ⟨a', ha', hq⟩ := (hg _ _).mp hyq
    have he := base_eq y a a' ha ha'
    subst a'
    rcases lt_or_ge q.val i.val with h | h
    · exact (ne_of_lt (hlo q h)) hq.symm
    · exact (ne_of_lt (hhi q h)) hq
  · intro y
    constructor
    · rintro (⟨i, hi⟩ | ⟨q, hq⟩)
      · obtain ⟨a, ha, _⟩ := (hb _ _).mp hi
        exact ⟨a, ha⟩
      · obtain ⟨a, ha, _⟩ := (hg _ _).mp hq
        exact ⟨a, ha⟩
    · rintro ⟨a, ha⟩
      by_cases he : ∃ q, y 0 = ψ q a
      · obtain ⟨q, hq⟩ := he
        exact Or.inr ⟨q, (hg _ _).mpr ⟨a, ha, hq⟩⟩
      · let T : Finset (Fin r) := Finset.univ.filter (fun q => ψ q a < y 0)
        let i : Fin (r + 1) := ⟨T.card, by
          have : T.card ≤ r := (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq
            (Finset.card_fin r)
          omega⟩
        have memT : ∀ q, q ∈ T ↔ ψ q a < y 0 := by simp [T]
        have initial : ∀ q, q ∈ T ↔ q.val < T.card := by
          intro q
          constructor
          · intro hq
            have sub : Finset.Iic q ⊆ T := by
              intro j hj
              apply (memT j).mpr
              exact lt_of_le_of_lt ((hm a).monotone (Finset.mem_Iic.mp hj)) ((memT q).mp hq)
            have hc := Finset.card_le_card sub
            simpa using hc
          · intro hq
            by_contra hn
            have sub : T ⊆ Finset.Iio q := by
              intro j hj
              apply Finset.mem_Iio.mpr
              by_contra hjq
              have hh := lt_of_le_of_lt ((hm a).monotone (le_of_not_gt hjq)) ((memT j).mp hj)
              exact hn ((memT q).mpr hh)
            have hc := Finset.card_le_card sub
            have : T.card ≤ q.val := by simpa using hc
            omega
        refine Or.inl ⟨i, (hb _ _).mpr ⟨a, ha, ?_, ?_⟩⟩
        · intro q hq
          exact (memT q).mp ((initial q).mpr hq)
        · intro q hq
          have hn : ¬ ψ q a < y 0 := by
            intro h
            have := (initial q).mp ((memT q).mpr h)
            change T.card ≤ q.val at hq
            omega
          exact lt_of_le_of_ne (le_of_not_gt hn) (fun h => he ⟨q, h⟩)
  · intro i y hy
    obtain ⟨a, ha, _⟩ := (hb _ _).mp hy
    have he : WithLp.toLp 2 (fun v => y v.succ) = a.val := by
      ext v
      exact ha v
    rw [he]
    exact a.property


def s2v_hardt_cad3_ambient_band {n : ℕ} (C : s2v_t11b_Formula n)
    (l u : C.realize → ℝ) (b : s2v_t11b_Formula (n + 1))
    (hb : ∀ y, y ∈ b.realize ↔ ∃ a : C.realize,
      (∀ v, y v.succ = a.val v) ∧ l a < y 0 ∧ y 0 < u a) :
    b.realize ≃ₜ {z : C.realize × ℝ | l z.1 < z.2 ∧ z.2 < u z.1} where
  toFun y := by
    let a : C.realize := ⟨WithLp.toLp 2 (fun v => y.val v.succ), by
      obtain ⟨a, ha, _⟩ := (hb _).mp y.property
      have he : WithLp.toLp 2 (fun v => y.val v.succ) = a.val := by
        ext v
        exact ha v
      rw [he]
      exact a.property⟩
    refine ⟨(a, y.val 0), ?_⟩
    obtain ⟨a', ha', ht⟩ := (hb _).mp y.property
    have he : a = a' := by
      apply Subtype.ext
      ext v
      exact ha' v
    simpa only [he, Set.mem_setOf_eq, Prod.fst, Prod.snd] using ht
  invFun z := ⟨WithLp.toLp 2 (Fin.cons z.val.2 (fun v => z.val.1.val v)),
    (hb _).mpr ⟨z.val.1, (fun _ => rfl), z.property⟩⟩
  left_inv y := by
    apply Subtype.ext
    ext v
    refine Fin.cases ?_ (fun _ => ?_) v <;> rfl
  right_inv z := by
    apply Subtype.ext
    apply Prod.ext
    · apply Subtype.ext
      ext v
      rfl
    · rfl
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.prodMk
    · apply Continuous.subtype_mk
      apply (PiLp.continuous_toLp 2 (fun _ => ℝ)).comp
      apply continuous_pi
      intro v
      change Continuous (fun y : b.realize => y.val v.succ)
      fun_prop
    · change Continuous (fun y : b.realize => y.val 0)
      fun_prop
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply (PiLp.continuous_toLp 2 (fun _ => ℝ)).comp
    apply continuous_pi
    intro v
    refine Fin.cases ?_ (fun j => ?_) v
    · change Continuous (fun z : {z : C.realize × ℝ | l z.1 < z.2 ∧ z.2 < u z.1} => z.val.2)
      fun_prop
    · change Continuous (fun z : {z : C.realize × ℝ | l z.1 < z.2 ∧ z.2 < u z.1} => z.val.1.val j)
      fun_prop

def s2v_hardt_cad3_ambient_region {n : ℕ} (C : s2v_t11b_Formula n)
    (D : Set (C.realize × ℝ)) (b : s2v_t11b_Formula (n + 1))
    (hb : ∀ y, y ∈ b.realize ↔ ∃ a : C.realize,
      (∀ v, y v.succ = a.val v) ∧ (a, y 0) ∈ D) :
    b.realize ≃ₜ D where
  toFun y := by
    let a : C.realize := ⟨WithLp.toLp 2 (fun v => y.val v.succ), by
      obtain ⟨a, ha, _⟩ := (hb _).mp y.property
      have he : WithLp.toLp 2 (fun v => y.val v.succ) = a.val := by
        ext v
        exact ha v
      rw [he]
      exact a.property⟩
    refine ⟨(a, y.val 0), ?_⟩
    obtain ⟨a', ha', ht⟩ := (hb _).mp y.property
    have he : a = a' := by
      apply Subtype.ext
      ext v
      exact ha' v
    simpa only [he, Set.mem_setOf_eq, Prod.fst, Prod.snd] using ht
  invFun z := ⟨WithLp.toLp 2 (Fin.cons z.val.2 (fun v => z.val.1.val v)),
    (hb _).mpr ⟨z.val.1, (fun _ => rfl), z.property⟩⟩
  left_inv y := by
    apply Subtype.ext
    ext v
    refine Fin.cases ?_ (fun _ => ?_) v <;> rfl
  right_inv z := by
    apply Subtype.ext
    apply Prod.ext
    · apply Subtype.ext
      ext v
      rfl
    · rfl
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.prodMk
    · apply Continuous.subtype_mk
      apply (PiLp.continuous_toLp 2 (fun _ => ℝ)).comp
      apply continuous_pi
      intro v
      change Continuous (fun y : b.realize => y.val v.succ)
      fun_prop
    · change Continuous (fun y : b.realize => y.val 0)
      fun_prop
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply (PiLp.continuous_toLp 2 (fun _ => ℝ)).comp
    apply continuous_pi
    intro v
    refine Fin.cases ?_ (fun j => ?_) v
    · change Continuous (fun z : D => z.val.2)
      fun_prop
    · change Continuous (fun z : D => z.val.1.val j)
      fun_prop


def s2v_hardt_cad3_bounded_topology {n d : ℕ} (C : s2v_t11b_Formula n)
    (e : C.realize ≃ₜ
      {z : EuclideanSpace ℝ (Fin d) | ∀ v, -1 < z v ∧ z v < 1})
    (l u : C.realize → ℝ) (hl : Continuous l) (hu : Continuous u)
    (hlu : ∀ a, l a < u a) (b : s2v_t11b_Formula (n + 1))
    (hb : ∀ y, y ∈ b.realize ↔ ∃ a : C.realize,
      (∀ v, y v.succ = a.val v) ∧ l a < y 0 ∧ y 0 < u a) :
    b.realize ≃ₜ
      {z : EuclideanSpace ℝ (Fin (d + 1)) | ∀ v, -1 < z v ∧ z v < 1} :=
  (s2v_hardt_cad3_ambient_band C l u b hb).trans
    (s2v_hardt_band_chart e l u hl hu hlu)

theorem s2v_hardt_cad3_bounded_topology_coordinates {n d : ℕ} (C : s2v_t11b_Formula n)
    (e : C.realize ≃ₜ
      {z : EuclideanSpace ℝ (Fin d) | ∀ v, -1 < z v ∧ z v < 1})
    (l u : C.realize → ℝ) (hl : Continuous l) (hu : Continuous u)
    (hlu : ∀ a, l a < u a) (b : s2v_t11b_Formula (n + 1))
    (hb : ∀ y, y ∈ b.realize ↔ ∃ a : C.realize,
      (∀ v, y v.succ = a.val v) ∧ l a < y 0 ∧ y 0 < u a)
    (y : b.realize) (a : C.realize) (ha : ∀ v, y.val v.succ = a.val v) :
    (∀ v, (s2v_hardt_cad3_bounded_topology C e l u hl hu hlu b hb y).val v.succ =
      (e a).val v) ∧
    (s2v_hardt_cad3_bounded_topology C e l u hl hu hlu b hb y).val 0 =
      2 * ((y.val 0 - l a) / (u a - l a)) - 1 := by
  have he : ((s2v_hardt_cad3_ambient_band C l u b hb y).val.1) = a := by
    apply Subtype.ext
    ext v
    exact ha v
  constructor
  · intro v
    change (e ((s2v_hardt_cad3_ambient_band C l u b hb y).val.1)).val v = (e a).val v
    rw [he]
  · change 2 * ((y.val 0 - l ((s2v_hardt_cad3_ambient_band C l u b hb y).val.1)) /
        (u ((s2v_hardt_cad3_ambient_band C l u b hb y).val.1) -
          l ((s2v_hardt_cad3_ambient_band C l u b hb y).val.1))) - 1 = _
    rw [he]

def s2v_hardt_cad3_box_product (d : ℕ) :
    ({z : EuclideanSpace ℝ (Fin d) | ∀ v, -1 < z v ∧ z v < 1} ×
      Set.Ioo (-1 : ℝ) 1) ≃ₜ
      {z : EuclideanSpace ℝ (Fin (d + 1)) | ∀ v, -1 < z v ∧ z v < 1} where
  toFun z := ⟨WithLp.toLp 2 (Fin.cons z.2.val (fun v => z.1.val v)), by
    intro v
    exact Fin.cases z.2.property (fun j => z.1.property j) v⟩
  invFun z := (⟨WithLp.toLp 2 (fun v => z.val v.succ), fun v => z.property v.succ⟩,
    ⟨z.val 0, z.property 0⟩)
  left_inv z := by
    apply Prod.ext
    · apply Subtype.ext
      ext v
      rfl
    · rfl
  right_inv z := by
    apply Subtype.ext
    ext v
    exact Fin.cases rfl (fun _ => rfl) v
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply (PiLp.continuous_toLp 2 (fun _ => ℝ)).comp
    apply continuous_pi
    intro v
    refine Fin.cases ?_ (fun j => ?_) v
    · change Continuous (fun z : ({z : EuclideanSpace ℝ (Fin d) | ∀ v, -1 < z v ∧ z v < 1} × Set.Ioo (-1 : ℝ) 1) => z.2.val)
      fun_prop
    · change Continuous (fun z : ({z : EuclideanSpace ℝ (Fin d) | ∀ v, -1 < z v ∧ z v < 1} × Set.Ioo (-1 : ℝ) 1) => z.1.val j)
      fun_prop
  continuous_invFun := by
    apply Continuous.prodMk
    · apply Continuous.subtype_mk
      apply (PiLp.continuous_toLp 2 (fun _ => ℝ)).comp
      apply continuous_pi
      intro v
      change Continuous (fun z : {z : EuclideanSpace ℝ (Fin (d + 1)) | ∀ v, -1 < z v ∧ z v < 1} => z.val v.succ)
      fun_prop
    · apply Continuous.subtype_mk
      change Continuous (fun z : {z : EuclideanSpace ℝ (Fin (d + 1)) | ∀ v, -1 < z v ∧ z v < 1} => z.val 0)
      fun_prop

theorem s2v_hardt_cad3_bounded_chart_aux {n d : ℕ} (C : s2v_t11b_Formula n)
    (e : C.realize ≃ₜ
      {z : EuclideanSpace ℝ (Fin d) | ∀ v, -1 < z v ∧ z v < 1})
    (G : s2v_t11b_Formula (n + d))
    (hG : ∀ a : C.realize, ∀ z : EuclideanSpace ℝ (Fin d),
      WithLp.toLp 2 (Fin.append (fun v => a.val v) (fun v => z v)) ∈ G.realize ↔
      z = (e a).val)
    (l u : C.realize → ℝ) (hl : Continuous l) (hu : Continuous u)
    (hlu : ∀ a, l a < u a)
    (L U : s2v_t11b_Formula (n + 1))
    (hL : ∀ y, y ∈ L.realize ↔ ∃ a : C.realize,
      (∀ v, y v.succ = a.val v) ∧ y 0 = l a)
    (hU : ∀ y, y ∈ U.realize ↔ ∃ a : C.realize,
      (∀ v, y v.succ = a.val v) ∧ y 0 = u a)
    (b : s2v_t11b_Formula (n + 1))
    (hb : ∀ y, y ∈ b.realize ↔ ∃ a : C.realize,
      (∀ v, y v.succ = a.val v) ∧ l a < y 0 ∧ y 0 < u a) :
    ∃ E : b.realize ≃ₜ
      {z : EuclideanSpace ℝ (Fin (d + 1)) | ∀ v, -1 < z v ∧ z v < 1},
    ∃ F : s2v_t11b_Formula ((n + 1) + (d + 1)),
    ∃ I : s2v_t11b_Formula ((d + 1) + (n + 1)),
      (∀ y : b.realize, ∀ a : C.realize,
        (∀ v, y.val v.succ = a.val v) →
        (∀ v, (E y).val v.succ = (e a).val v) ∧ (E y).val 0 = 2 * ((y.val 0 - l a) / (u a - l a)) - 1) ∧
      (∀ y : b.realize, ∀ z : EuclideanSpace ℝ (Fin (d + 1)),
        WithLp.toLp 2 (Fin.append (fun v => y.val v) (fun v => z v)) ∈ F.realize ↔
          z = (E y).val) ∧
      (∀ z : {z : EuclideanSpace ℝ (Fin (d + 1)) | ∀ v, -1 < z v ∧ z v < 1},
        ∀ y : EuclideanSpace ℝ (Fin (n + 1)),
        WithLp.toLp 2 (Fin.append (fun v => z.val v) (fun v => y v)) ∈ I.realize ↔
          y = (E.symm z).val) := by
  classical
  let N := (n + 1) + (d + 1)
  let Y : Fin (n + 1) → Fin N := Fin.castAdd (d + 1)
  let Z : Fin (d + 1) → Fin N := Fin.natAdd (n + 1)
  let p : MvPolynomial (Fin ((N + 1) + 1)) ℝ :=
    (MvPolynomial.X ((Z 0).succ.succ) + 1) *
      (MvPolynomial.X 0 - MvPolynomial.X (Fin.succ 0)) -
      2 * (MvPolynomial.X ((Y 0).succ.succ) - MvPolynomial.X (Fin.succ 0))
  let R : s2v_t11b_Formula ((N + 1) + 1) := .inter (.nonneg p) (.nonneg (-p))
  have hR (t v : ℝ) (w : EuclideanSpace ℝ (Fin N)) :
      WithLp.toLp 2 (Fin.cons v (Fin.cons t (fun j => w j))) ∈ R.realize ↔
        (w (Z 0) + 1) * (v - t) - 2 * (w (Y 0) - t) = 0 := by
    simp only [R, p, s2v_t11b_Formula.realize, Set.mem_inter_iff, Set.mem_setOf_eq,
      map_sub, MvPolynomial.eval_add, MvPolynomial.eval_mul,
      MvPolynomial.eval_X, map_one, MvPolynomial.eval_ofNat,
      map_neg, WithLp.ofLp_toLp, Fin.cons_zero, Fin.cons_succ, neg_nonneg]
    exact ⟨fun h => le_antisymm h.2 h.1, fun h => ⟨h.ge, h.le⟩⟩
  obtain ⟨Ru, hRu⟩ := s2v_hardt_cad3_graph_substitution C u U hU
    (fun v => (Y v.succ).succ) R
  obtain ⟨Rl, hRl⟩ := s2v_hardt_cad3_graph_substitution C l L hL
    (fun v => Y v.succ) Ru
  let ρ : Fin (n + d) → Fin N :=
    Fin.addCases (fun v => Y v.succ) (fun v => Z v.succ)
  let F₀ : s2v_t11b_Formula N := .inter (s2v_hardt1_rename ρ G) Rl
  let E := s2v_hardt_cad3_bounded_topology C e l u hl hu hlu b hb
  have hF₀ : ∀ y : b.realize, ∀ z : EuclideanSpace ℝ (Fin (d + 1)),
      WithLp.toLp 2 (Fin.append (fun v => y.val v) (fun v => z v)) ∈ F₀.realize ↔
        z = (E y).val := by
    intro y z
    obtain ⟨a, ha, hy⟩ := (hb y.val).mp y.property
    have unique (a' : C.realize) (h : ∀ v, y.val v.succ = a'.val v) : a' = a := by
      apply Subtype.ext
      ext v
      exact (h v).symm.trans (ha v)
    have hscalar : WithLp.toLp 2 (Fin.append (fun v => y.val v) (fun v => z v)) ∈ Rl.realize ↔
        (z 0 + 1) * (u a - l a) - 2 * (y.val 0 - l a) = 0 := by
      rw [hRl]
      constructor
      · rintro ⟨a', ha', ht⟩
        have he := unique a' (by simpa [Y] using ha')
        subst a'
        obtain ⟨a', ha', ht⟩ := (hRu _).mp ht
        have he := unique a' (by simpa [Y] using ha')
        subst a'
        simpa [Y, Z] using (hR (l a) (u a) _).mp ht
      · intro ht
        refine ⟨a, ?_, (hRu _).mpr ⟨a, ?_, ?_⟩⟩
        · simpa [Y] using ha
        · simpa [Y] using ha
        · apply (hR (l a) (u a) _).mpr
          simpa [Y, Z] using ht
    have hbase : WithLp.toLp 2 (Fin.append (fun v => y.val v) (fun v => z v)) ∈
        (s2v_hardt1_rename ρ G).realize ↔
        WithLp.toLp 2 (fun v => z v.succ) = (e a).val := by
      rw [s2v_hardt1_realize_rename]
      have he : WithLp.toLp 2 (fun i =>
          Fin.append (fun v => y.val v) (fun v => z v) (ρ i)) =
          WithLp.toLp 2 (Fin.append (fun v => a.val v) (fun v => z v.succ)) := by
        ext i
        refine Fin.addCases (fun j => ?_) (fun j => ?_) i
        · simpa [ρ, Y] using ha j
        · simp [ρ, Z]
      rw [he]
      exact hG a (WithLp.toLp 2 (fun v => z v.succ))
    change (_ ∧ _) ↔ _
    rw [hbase, hscalar]
    have hcoords := s2v_hardt_cad3_bounded_topology_coordinates C e l u hl hu hlu b hb y a ha
    have hd : u a - l a ≠ 0 := ne_of_gt (sub_pos.mpr (hlu a))
    constructor
    · rintro ⟨hz, ht⟩
      ext v
      refine Fin.cases ?_ (fun j => ?_) v
      · rw [hcoords.2]
        field_simp [hd]
        nlinarith
      · exact (congrArg (fun w : EuclideanSpace ℝ (Fin d) => w j) hz).trans (hcoords.1 j).symm
    · intro hz
      constructor
      · ext j
        exact (congrArg (fun w : EuclideanSpace ℝ (Fin (d + 1)) => w j.succ) hz).trans (hcoords.1 j)
      · have hz0 := (congrArg (fun w : EuclideanSpace ℝ (Fin (d + 1)) => w 0) hz).trans hcoords.2
        rw [hz0]
        field_simp [hd]
        <;> ring
  obtain ⟨F, I, hF, hI⟩ := s2v_hardt_cad3_inverse_graph b _ E F₀ hF₀
  exact ⟨E, F, I, s2v_hardt_cad3_bounded_topology_coordinates C e l u hl hu hlu b hb, hF, hI⟩

def s2v_hardt_cad3_line_normalization : ℝ ≃ₜ Set.Ioo (-1 : ℝ) 1 where
  toFun t := ⟨t / (1 + |t|), by
    have hd : 0 < 1 + |t| := by positivity
    constructor
    · apply (lt_div_iff₀ hd).mpr
      nlinarith [neg_abs_le t]
    · apply (div_lt_iff₀ hd).mpr
      nlinarith [le_abs_self t]⟩
  invFun z := z.val / (1 - |z.val|)
  left_inv t := by
    have hd : 0 < 1 + |t| := by positivity
    change (t / (1 + |t|)) / (1 - |t / (1 + |t|)|) = t
    rw [abs_div, abs_of_pos hd]
    field_simp
    <;> ring
  right_inv z := by
    apply Subtype.ext
    have hz : |z.val| < 1 := abs_lt.mpr z.property
    have hd : 0 < 1 - |z.val| := by linarith
    change (z.val / (1 - |z.val|)) / (1 + |z.val / (1 - |z.val|)|) = z.val
    rw [abs_div, abs_of_pos hd]
    field_simp
    <;> ring
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact continuous_id.div (continuous_const.add continuous_abs)
      (fun t => ne_of_gt (by positivity))
  continuous_invFun := by
    apply continuous_subtype_val.div
      (continuous_const.sub (continuous_abs.comp continuous_subtype_val))
    intro z
    have hz : |z.val| < 1 := abs_lt.mpr z.property
    change 1 - |z.val| ≠ 0
    linarith

def s2v_hardt_cad3_ray_normalization : Set.Ioi (0 : ℝ) ≃ₜ Set.Ioo (-1 : ℝ) 1 where
  toFun t := ⟨(t.val - 1) / (t.val + 1), by
    have hd : 0 < t.val + 1 := by linarith [show 0 < t.val from t.property]
    constructor
    · apply (lt_div_iff₀ hd).mpr
      linarith [show 0 < t.val from t.property]
    · apply (div_lt_iff₀ hd).mpr
      linarith⟩
  invFun z := ⟨(1 + z.val) / (1 - z.val), by
    change 0 < (1 + z.val) / (1 - z.val)
    exact div_pos (by linarith [show (-1 : ℝ) < z.val from z.property.1]) (by linarith [show z.val < (1 : ℝ) from z.property.2])⟩
  left_inv t := by
    apply Subtype.ext
    have hd : t.val + 1 ≠ 0 := by linarith [show 0 < t.val from t.property]
    change (1 + (t.val - 1) / (t.val + 1)) / (1 - (t.val - 1) / (t.val + 1)) = t.val
    field_simp
    <;> ring
  right_inv z := by
    apply Subtype.ext
    have hd : 1 - z.val ≠ 0 := by linarith [show z.val < (1 : ℝ) from z.property.2]
    change ((1 + z.val) / (1 - z.val) - 1) / ((1 + z.val) / (1 - z.val) + 1) = z.val
    field_simp
    <;> ring
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact (continuous_subtype_val.sub continuous_const).div
      (continuous_subtype_val.add continuous_const)
      (fun t => by linarith [show 0 < t.val from t.property])
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact (continuous_const.add continuous_subtype_val).div
      (continuous_const.sub continuous_subtype_val)
      (fun z => by linarith [show z.val < (1 : ℝ) from z.property.2])

def s2v_hardt_cad3_ray_product {X : Type*} [TopologicalSpace X]
    (s : X → ℝ) (hs : Continuous s) (upper : Bool) :
    {z : X × ℝ | if upper then s z.1 < z.2 else z.2 < s z.1} ≃ₜ
      X × Set.Ioi (0 : ℝ) where
  toFun z := (z.val.1, ⟨if upper then z.val.2 - s z.val.1 else s z.val.1 - z.val.2, by
    have h := z.property
    cases upper <;> simp only [Bool.false_eq_true, Bool.true_eq, ite_true, ite_false, Set.mem_setOf_eq, Set.mem_Ioi] at h ⊢ <;>
      exact sub_pos.mpr h⟩)
  invFun z := ⟨(z.1, if upper then s z.1 + z.2.val else s z.1 - z.2.val), by
    have h : 0 < z.2.val := z.2.property
    cases upper <;> simp only [Bool.false_eq_true, Bool.true_eq, ite_true, ite_false,
      Set.mem_setOf_eq] <;> linarith⟩
  left_inv z := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · cases upper <;> dsimp <;> ring
  right_inv z := by
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      cases upper <;> dsimp <;> ring
  continuous_toFun := by
    apply Continuous.prodMk
    · exact continuous_fst.comp continuous_subtype_val
    · apply Continuous.subtype_mk
      cases upper
      · change Continuous (fun z : {z : X × ℝ | z.2 < s z.1} => s z.val.1 - z.val.2)
        exact (hs.comp (continuous_fst.comp continuous_subtype_val)).sub
          (continuous_snd.comp continuous_subtype_val)
      · change Continuous (fun z : {z : X × ℝ | s z.1 < z.2} => z.val.2 - s z.val.1)
        exact (continuous_snd.comp continuous_subtype_val).sub
          (hs.comp (continuous_fst.comp continuous_subtype_val))
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply Continuous.prodMk continuous_fst
    cases upper
    · change Continuous (fun z : X × Set.Ioi (0 : ℝ) => s z.1 - z.2.val)
      exact (hs.comp continuous_fst).sub (continuous_subtype_val.comp continuous_snd)
    · change Continuous (fun z : X × Set.Ioi (0 : ℝ) => s z.1 + z.2.val)
      exact (hs.comp continuous_fst).add (continuous_subtype_val.comp continuous_snd)

theorem s2v_hardt_cad3_ray_chart_aux {n d : ℕ} (C : s2v_t11b_Formula n)
    (e : C.realize ≃ₜ
      {z : EuclideanSpace ℝ (Fin d) | ∀ v, -1 < z v ∧ z v < 1})
    (G : s2v_t11b_Formula (n + d))
    (hG : ∀ a : C.realize, ∀ z : EuclideanSpace ℝ (Fin d),
      WithLp.toLp 2 (Fin.append (fun v => a.val v) (fun v => z v)) ∈ G.realize ↔
      z = (e a).val)
    (s : C.realize → ℝ) (hs : Continuous s) (upper : Bool)
    (S : s2v_t11b_Formula (n + 1))
    (hS : ∀ y, y ∈ S.realize ↔ ∃ a : C.realize,
      (∀ v, y v.succ = a.val v) ∧ y 0 = s a)
    (b : s2v_t11b_Formula (n + 1))
    (hb : ∀ y, y ∈ b.realize ↔ ∃ a : C.realize,
      (∀ v, y v.succ = a.val v) ∧ (if upper then s a < y 0 else y 0 < s a)) :
    ∃ E : b.realize ≃ₜ
      {z : EuclideanSpace ℝ (Fin (d + 1)) | ∀ v, -1 < z v ∧ z v < 1},
    ∃ F : s2v_t11b_Formula ((n + 1) + (d + 1)),
    ∃ I : s2v_t11b_Formula ((d + 1) + (n + 1)),
      (∀ y : b.realize, ∀ a : C.realize,
        (∀ v, y.val v.succ = a.val v) →
        (∀ v, (E y).val v.succ = (e a).val v) ∧ (E y).val 0 = ((if upper then y.val 0 - s a else s a - y.val 0) - 1) /
          ((if upper then y.val 0 - s a else s a - y.val 0) + 1)) ∧
      (∀ y : b.realize, ∀ z : EuclideanSpace ℝ (Fin (d + 1)),
        WithLp.toLp 2 (Fin.append (fun v => y.val v) (fun v => z v)) ∈ F.realize ↔
          z = (E y).val) ∧
      (∀ z : {z : EuclideanSpace ℝ (Fin (d + 1)) | ∀ v, -1 < z v ∧ z v < 1},
        ∀ y : EuclideanSpace ℝ (Fin (n + 1)),
        WithLp.toLp 2 (Fin.append (fun v => z.val v) (fun v => y v)) ∈ I.realize ↔
          y = (E.symm z).val) := by
  classical
  let D : Set (C.realize × ℝ) := {z | if upper then s z.1 < z.2 else z.2 < s z.1}
  let A := s2v_hardt_cad3_ambient_region C D b hb
  let E := (((A.trans (s2v_hardt_cad3_ray_product s hs upper)).trans
    (e.prodCongr s2v_hardt_cad3_ray_normalization)).trans (s2v_hardt_cad3_box_product d))
  have coords : ∀ (y : b.realize) (a : C.realize),
      (∀ v, y.val v.succ = a.val v) →
      (∀ v, (E y).val v.succ = (e a).val v) ∧
        (E y).val 0 = ((if upper then y.val 0 - s a else s a - y.val 0) - 1) /
          ((if upper then y.val 0 - s a else s a - y.val 0) + 1) := by
    intro y a ha
    have he : (A y).val.1 = a := by
      apply Subtype.ext
      ext v
      exact ha v
    constructor
    · intro v
      change (e (A y).val.1).val v = (e a).val v
      rw [he]
    · change ((if upper then y.val 0 - s (A y).val.1 else s (A y).val.1 - y.val 0) - 1) /
        ((if upper then y.val 0 - s (A y).val.1 else s (A y).val.1 - y.val 0) + 1) = _
      rw [he]
  let N := (n + 1) + (d + 1)
  let Y : Fin (n + 1) → Fin N := Fin.castAdd (d + 1)
  let Z : Fin (d + 1) → Fin N := Fin.natAdd (n + 1)
  let vP : MvPolynomial (Fin (N + 1)) ℝ :=
    if upper then MvPolynomial.X ((Y 0).succ) - MvPolynomial.X 0
    else MvPolynomial.X 0 - MvPolynomial.X ((Y 0).succ)
  let p : MvPolynomial (Fin (N + 1)) ℝ :=
    MvPolynomial.X ((Z 0).succ) * (vP + 1) - (vP - 1)
  let R : s2v_t11b_Formula (N + 1) := .inter (.nonneg p) (.nonneg (-p))
  have hR (t : ℝ) (w : EuclideanSpace ℝ (Fin N)) :
      WithLp.toLp 2 (Fin.cons t (fun j => w j)) ∈ R.realize ↔
        w (Z 0) * ((if upper then w (Y 0) - t else t - w (Y 0)) + 1) -
          ((if upper then w (Y 0) - t else t - w (Y 0)) - 1) = 0 := by
    cases upper <;>
      simp only [R, p, vP, s2v_t11b_Formula.realize, Set.mem_inter_iff, Set.mem_setOf_eq,
        map_sub, MvPolynomial.eval_add, MvPolynomial.eval_mul, MvPolynomial.eval_X,
        map_one, map_neg, Bool.false_eq_true, Bool.true_eq, ite_true, ite_false,
        WithLp.ofLp_toLp, Fin.cons_zero, Fin.cons_succ, neg_nonneg] <;>
      exact ⟨fun h => le_antisymm h.2 h.1, fun h => ⟨h.ge, h.le⟩⟩
  obtain ⟨Rs, hRs⟩ := s2v_hardt_cad3_graph_substitution C s S hS
    (fun v => Y v.succ) R
  let ρ : Fin (n + d) → Fin N :=
    Fin.addCases (fun v => Y v.succ) (fun v => Z v.succ)
  let F₀ : s2v_t11b_Formula N := .inter (s2v_hardt1_rename ρ G) Rs
  have hF₀ : ∀ y : b.realize, ∀ z : EuclideanSpace ℝ (Fin (d + 1)),
      WithLp.toLp 2 (Fin.append (fun v => y.val v) (fun v => z v)) ∈ F₀.realize ↔
        z = (E y).val := by
    intro y z
    obtain ⟨a, ha, hy⟩ := (hb y.val).mp y.property
    let v : ℝ := if upper then y.val 0 - s a else s a - y.val 0
    have hv : 0 < v := by
      cases upper <;> simp only [Bool.false_eq_true, Bool.true_eq, ite_true, ite_false] at hy ⊢
      · exact sub_pos.mpr hy
      · exact sub_pos.mpr hy
    have hd : v + 1 ≠ 0 := by linarith
    have hscalar : WithLp.toLp 2 (Fin.append (fun v => y.val v) (fun v => z v)) ∈ Rs.realize ↔
        z 0 * (v + 1) - (v - 1) = 0 := by
      rw [hRs]
      constructor
      · rintro ⟨a', ha', ht⟩
        have he : a' = a := by
          apply Subtype.ext
          ext j
          have h : y.val j.succ = a'.val j := by simpa [Y] using ha' j
          exact h.symm.trans (ha j)
        subst a'
        simpa [Y, Z, v] using (hR (s a) _).mp ht
      · intro ht
        refine ⟨a, ?_, ?_⟩
        · simpa [Y] using ha
        · apply (hR (s a) _).mpr
          simpa [Y, Z, v] using ht
    have hbase : WithLp.toLp 2 (Fin.append (fun v => y.val v) (fun v => z v)) ∈
        (s2v_hardt1_rename ρ G).realize ↔
        WithLp.toLp 2 (fun v => z v.succ) = (e a).val := by
      rw [s2v_hardt1_realize_rename]
      have he : WithLp.toLp 2 (fun i =>
          Fin.append (fun v => y.val v) (fun v => z v) (ρ i)) =
          WithLp.toLp 2 (Fin.append (fun v => a.val v) (fun v => z v.succ)) := by
        ext i
        refine Fin.addCases (fun j => ?_) (fun j => ?_) i
        · simpa [ρ, Y] using ha j
        · simp [ρ, Z]
      rw [he]
      exact hG a (WithLp.toLp 2 (fun v => z v.succ))
    change (_ ∧ _) ↔ _
    rw [hbase, hscalar]
    have hc := coords y a ha
    constructor
    · rintro ⟨hz, ht⟩
      ext j
      refine Fin.cases ?_ (fun j => ?_) j
      · rw [hc.2]
        change z 0 = (v - 1) / (v + 1)
        apply (eq_div_iff hd).mpr
        linarith
      · exact (congrArg (fun w : EuclideanSpace ℝ (Fin d) => w j) hz).trans (hc.1 j).symm
    · intro hz
      constructor
      · ext j
        exact (congrArg (fun w : EuclideanSpace ℝ (Fin (d + 1)) => w j.succ) hz).trans (hc.1 j)
      · have hz0 := (congrArg (fun w : EuclideanSpace ℝ (Fin (d + 1)) => w 0) hz).trans hc.2
        change z 0 = (v - 1) / (v + 1) at hz0
        have := (eq_div_iff hd).mp hz0
        linarith
  obtain ⟨F, I, hF, hI⟩ := s2v_hardt_cad3_inverse_graph b _ E F₀ hF₀
  exact ⟨E, F, I, coords, hF, hI⟩

theorem s2v_hardt_cad3_whole_chart_aux {n d : ℕ} (C : s2v_t11b_Formula n)
    (e : C.realize ≃ₜ
      {z : EuclideanSpace ℝ (Fin d) | ∀ v, -1 < z v ∧ z v < 1})
    (G : s2v_t11b_Formula (n + d))
    (hG : ∀ a : C.realize, ∀ z : EuclideanSpace ℝ (Fin d),
      WithLp.toLp 2 (Fin.append (fun v => a.val v) (fun v => z v)) ∈ G.realize ↔
      z = (e a).val)

    (b : s2v_t11b_Formula (n + 1))
    (hb : ∀ y, y ∈ b.realize ↔ ∃ a : C.realize,
      (∀ v, y v.succ = a.val v) ∧ True) :
    ∃ E : b.realize ≃ₜ
      {z : EuclideanSpace ℝ (Fin (d + 1)) | ∀ v, -1 < z v ∧ z v < 1},
    ∃ F : s2v_t11b_Formula ((n + 1) + (d + 1)),
    ∃ I : s2v_t11b_Formula ((d + 1) + (n + 1)),
      (∀ y : b.realize, ∀ a : C.realize,
        (∀ v, y.val v.succ = a.val v) →
        (∀ v, (E y).val v.succ = (e a).val v) ∧ (E y).val 0 = y.val 0 / (1 + |y.val 0|)) ∧
      (∀ y : b.realize, ∀ z : EuclideanSpace ℝ (Fin (d + 1)),
        WithLp.toLp 2 (Fin.append (fun v => y.val v) (fun v => z v)) ∈ F.realize ↔
          z = (E y).val) ∧
      (∀ z : {z : EuclideanSpace ℝ (Fin (d + 1)) | ∀ v, -1 < z v ∧ z v < 1},
        ∀ y : EuclideanSpace ℝ (Fin (n + 1)),
        WithLp.toLp 2 (Fin.append (fun v => z.val v) (fun v => y v)) ∈ I.realize ↔
          y = (E.symm z).val) := by
  classical
  let A := (s2v_hardt_cad3_ambient_region C Set.univ b hb).trans
    (Homeomorph.Set.univ (C.realize × ℝ))
  let E := (A.trans (e.prodCongr s2v_hardt_cad3_line_normalization)).trans
    (s2v_hardt_cad3_box_product d)
  have coords : ∀ (y : b.realize) (a : C.realize),
      (∀ v, y.val v.succ = a.val v) →
      (∀ v, (E y).val v.succ = (e a).val v) ∧
        (E y).val 0 = y.val 0 / (1 + |y.val 0|) := by
    intro y a ha
    have he : (A y).1 = a := by
      apply Subtype.ext
      ext v
      exact ha v
    constructor
    · intro v
      change (e (A y).1).val v = (e a).val v
      rw [he]
    · rfl
  let N := (n + 1) + (d + 1)
  let Y : Fin (n + 1) → Fin N := Fin.castAdd (d + 1)
  let Z : Fin (d + 1) → Fin N := Fin.natAdd (n + 1)
  let tP : MvPolynomial (Fin N) ℝ := MvPolynomial.X (Y 0)
  let zP : MvPolynomial (Fin N) ℝ := MvPolynomial.X (Z 0)
  let Rp : s2v_t11b_Formula N := .inter (.nonneg tP)
    (s2v_t11b_zeroFormula (zP * (1 + tP) - tP))
  let Rm : s2v_t11b_Formula N := .inter (.nonneg (-tP))
    (s2v_t11b_zeroFormula (zP * (1 - tP) - tP))
  let R : s2v_t11b_Formula N := .compl (.inter (.compl Rp) (.compl Rm))
  have hRp (w : EuclideanSpace ℝ (Fin N)) : w ∈ Rp.realize ↔
      0 ≤ w (Y 0) ∧ w (Z 0) * (1 + w (Y 0)) - w (Y 0) = 0 := by
    change (_ ∧ _) ↔ _
    rw [s2v_t11b_realize_zeroFormula]
    simp only [s2v_t11b_Formula.realize, Set.mem_setOf_eq, tP, zP,
      map_sub, MvPolynomial.eval_add, MvPolynomial.eval_mul, MvPolynomial.eval_X, map_one]
  have hRm (w : EuclideanSpace ℝ (Fin N)) : w ∈ Rm.realize ↔
      w (Y 0) ≤ 0 ∧ w (Z 0) * (1 - w (Y 0)) - w (Y 0) = 0 := by
    change (_ ∧ _) ↔ _
    rw [s2v_t11b_realize_zeroFormula]
    simp only [s2v_t11b_Formula.realize, Set.mem_setOf_eq, tP, zP,
      map_sub, MvPolynomial.eval_mul, MvPolynomial.eval_X, map_one, map_neg, neg_nonneg]
  have hR (w : EuclideanSpace ℝ (Fin N)) : w ∈ R.realize ↔
      w (Z 0) = w (Y 0) / (1 + |w (Y 0)|) := by
    change (¬ (¬ w ∈ Rp.realize ∧ ¬ w ∈ Rm.realize)) ↔ _
    rw [not_and_or, not_not, not_not, hRp, hRm]
    have hd : 1 + |w (Y 0)| ≠ 0 := ne_of_gt (by positivity)
    rw [eq_div_iff hd]
    constructor
    · rintro (⟨ht, hz⟩ | ⟨ht, hz⟩)
      · rw [abs_of_nonneg ht]
        linarith
      · rw [abs_of_nonpos ht]
        linarith
    · intro hz
      rcases le_total 0 (w (Y 0)) with ht | ht
      · left
        rw [abs_of_nonneg ht] at hz
        exact ⟨ht, sub_eq_zero.mpr hz⟩
      · right
        rw [abs_of_nonpos ht] at hz
        exact ⟨ht, by nlinarith⟩
  let ρ : Fin (n + d) → Fin N :=
    Fin.addCases (fun v => Y v.succ) (fun v => Z v.succ)
  let F₀ : s2v_t11b_Formula N := .inter (s2v_hardt1_rename ρ G) R
  have hF₀ : ∀ y : b.realize, ∀ z : EuclideanSpace ℝ (Fin (d + 1)),
      WithLp.toLp 2 (Fin.append (fun v => y.val v) (fun v => z v)) ∈ F₀.realize ↔
        z = (E y).val := by
    intro y z
    obtain ⟨a, ha, _⟩ := (hb y.val).mp y.property
    have hbase : WithLp.toLp 2 (Fin.append (fun v => y.val v) (fun v => z v)) ∈
        (s2v_hardt1_rename ρ G).realize ↔
        WithLp.toLp 2 (fun v => z v.succ) = (e a).val := by
      rw [s2v_hardt1_realize_rename]
      have he : WithLp.toLp 2 (fun i =>
          Fin.append (fun v => y.val v) (fun v => z v) (ρ i)) =
          WithLp.toLp 2 (Fin.append (fun v => a.val v) (fun v => z v.succ)) := by
        ext i
        refine Fin.addCases (fun j => ?_) (fun j => ?_) i
        · simpa [ρ, Y] using ha j
        · simp [ρ, Z]
      rw [he]
      exact hG a (WithLp.toLp 2 (fun v => z v.succ))
    change (_ ∧ _) ↔ _
    rw [hbase, hR]
    have hc := coords y a ha
    have hscalar : (WithLp.toLp 2 (Fin.append (fun v => y.val v) (fun v => z v))) (Z 0) = z 0 := by simp [Z]
    have hheight : (WithLp.toLp 2 (Fin.append (fun v => y.val v) (fun v => z v))) (Y 0) = y.val 0 := by simp [Y]
    rw [hscalar, hheight]
    constructor
    · rintro ⟨hz, ht⟩
      ext j
      refine Fin.cases ?_ (fun j => ?_) j
      · exact ht.trans hc.2.symm
      · exact (congrArg (fun w : EuclideanSpace ℝ (Fin d) => w j) hz).trans (hc.1 j).symm
    · intro hz
      constructor
      · ext j
        exact (congrArg (fun w : EuclideanSpace ℝ (Fin (d + 1)) => w j.succ) hz).trans (hc.1 j)
      · exact (congrArg (fun w : EuclideanSpace ℝ (Fin (d + 1)) => w 0) hz).trans hc.2
  obtain ⟨F, I, hF, hI⟩ := s2v_hardt_cad3_inverse_graph b _ E F₀ hF₀
  exact ⟨E, F, I, coords, hF, hI⟩

theorem s2v_hardt_cad3_continuous_height {X : Type*} [TopologicalSpace X]
    {r : ℕ} (ψ : Fin r → X → ℝ) (hm : ∀ a, StrictMono (fun q => ψ q a))
    (hψ : ∀ q, Continuous (ψ q)) (i : Fin (r + 1)) :
    ∃ f : X → ℝ, Continuous f ∧ ∀ a,
      (∀ q : Fin r, q.val < i.val → ψ q a < f a) ∧
      (∀ q : Fin r, i.val ≤ q.val → f a < ψ q a) := by
  by_cases hi : i.val = 0
  · by_cases hr : r = 0
    · subst r
      exact ⟨fun _ => 0, continuous_const, by simp⟩
    · let q : Fin r := ⟨0, Nat.pos_of_ne_zero hr⟩
      refine ⟨fun a => ψ q a - 1, (hψ q).sub continuous_const, ?_⟩
      intro a
      constructor
      · intro j hj
        omega
      · intro j hj
        have hle := (hm a).monotone (show q ≤ j by change 0 ≤ j.val; omega)
        linarith
  · let q : Fin r := ⟨i.val - 1, by omega⟩
    by_cases hir : i.val < r
    · let q' : Fin r := ⟨i.val, hir⟩
      refine ⟨fun a => (ψ q a + ψ q' a) / 2,
        ((hψ q).add (hψ q')).div_const 2, ?_⟩
      intro a
      have hlt := hm a (show q < q' by change i.val - 1 < i.val; omega)
      constructor
      · intro j hj
        have hle := (hm a).monotone (show j ≤ q by change j.val ≤ i.val - 1; omega)
        linarith
      · intro j hj
        have hle := (hm a).monotone (show q' ≤ j from hj)
        linarith
    · refine ⟨fun a => ψ q a + 1, (hψ q).add continuous_const, ?_⟩
      intro a
      constructor
      · intro j hj
        have hle := (hm a).monotone (show j ≤ q by change j.val ≤ i.val - 1; omega)
        linarith
      · intro j hj
        omega

theorem s2v_hardt_cad3_band_preconnected {n r : ℕ}
    (C : s2v_t11b_Formula n) (ψ : Fin r → C.realize → ℝ)
    (hm : ∀ a, StrictMono (fun q => ψ q a))
    (hC : IsConnected C.realize) (hψ : ∀ q, Continuous (ψ q))
    (i : Fin (r + 1)) (b : s2v_t11b_Formula (n + 1))
    (hb : ∀ y, y ∈ b.realize ↔ ∃ a : C.realize,
        (∀ v, y v.succ = a.val v) ∧
        (∀ q : Fin r, q.val < i.val → ψ q a < y 0) ∧
        (∀ q : Fin r, i.val ≤ q.val → y 0 < ψ q a)) :
    IsPreconnected b.realize := by
  obtain ⟨f, hf, hbound⟩ := s2v_hardt_cad3_continuous_height ψ hm hψ i
  let lift : C.realize → ℝ → EuclideanSpace ℝ (Fin (n + 1)) :=
    fun a t => WithLp.toLp 2 (Fin.cons t (fun v => a.val v))
  have hlift (a : C.realize) : Continuous (lift a) := by
    apply (PiLp.continuous_toLp 2 (fun _ => ℝ)).comp
    apply continuous_pi
    intro v
    refine Fin.cases ?_ (fun _ => ?_) v
    · exact continuous_id
    · exact continuous_const
  let graph : Set (EuclideanSpace ℝ (Fin (n + 1))) := Set.range (fun a => lift a (f a))
  have hgraph : IsPreconnected graph := by
    letI := Subtype.preconnectedSpace hC.isPreconnected
    apply isPreconnected_range
    apply (PiLp.continuous_toLp 2 (fun _ => ℝ)).comp
    apply continuous_pi
    intro v
    refine Fin.cases ?_ (fun j => ?_) v
    · exact hf
    · change Continuous (fun a : C.realize => a.val j)
      fun_prop
  let fiber : C.realize → Set ℝ := fun a => {t |
    (∀ q : Fin r, q.val < i.val → ψ q a < t) ∧
    (∀ q : Fin r, i.val ≤ q.val → t < ψ q a)}
  have hinterval (a : C.realize) : (fiber a).OrdConnected := by
    constructor
    intro x hx y hy z hz
    exact ⟨fun q hq => lt_of_lt_of_le (hx.1 q hq) hz.1,
      fun q hq => lt_of_le_of_lt hz.2 (hy.2 q hq)⟩
  have hpieces (a : C.realize) : IsPreconnected (graph ∪ lift a '' fiber a) := by
    apply hgraph.union (lift a (f a))
    · exact ⟨a, rfl⟩
    · exact ⟨f a, hbound a, rfl⟩
    · exact (hinterval a).isPreconnected.image _ (hlift a).continuousOn
  have hunion : (⋃ a : C.realize, graph ∪ lift a '' fiber a) = b.realize := by
    ext y
    constructor
    · intro hy
      obtain ⟨a, ha⟩ := Set.mem_iUnion.mp hy
      rcases ha with hg | ⟨t, ht, rfl⟩
      · obtain ⟨a', rfl⟩ := hg
        exact (hb _).mpr ⟨a', (fun _ => rfl), hbound a'⟩
      · exact (hb _).mpr ⟨a, (fun _ => rfl), ht⟩
    · intro hy
      obtain ⟨a, ha, ht⟩ := (hb _).mp hy
      apply Set.mem_iUnion.mpr
      refine ⟨a, Or.inr ⟨y 0, ht, ?_⟩⟩
      ext v
      refine Fin.cases ?_ (fun j => ?_) v
      · rfl
      · exact (ha j).symm
  rw [← hunion]
  apply isPreconnected_iUnion _ hpieces
  obtain ⟨a, ha⟩ := hC.nonempty
  refine ⟨lift ⟨a, ha⟩ (f ⟨a, ha⟩), Set.mem_iInter.mpr ?_⟩
  intro a'
  exact Or.inl ⟨⟨a, ha⟩, rfl⟩

theorem s2v_hardt_cad3_band_signs_aux {n r k : ℕ}
    (C : s2v_t11b_Formula n) (ψ : Fin r → C.realize → ℝ)
    (hm : ∀ a, StrictMono (fun q => ψ q a))
    (hC : IsConnected C.realize) (hψ : ∀ q, Continuous (ψ q))
    (P : Fin k → Polynomial (MvPolynomial (Fin n) ℝ))
    (hz : ∀ j, (∀ a : C.realize,
      (P j).map (MvPolynomial.eval (fun v => a.val v)) = 0) ∨
      (∀ a : C.realize, (P j).map (MvPolynomial.eval (fun v => a.val v)) ≠ 0))
    (hr : ∀ a : C.realize, ∀ t : ℝ, (∃ q, t = ψ q a) ↔
      ∃ j, (P j).map (MvPolynomial.eval (fun v => a.val v)) ≠ 0 ∧
        (P j).eval₂ (MvPolynomial.eval (fun v => a.val v)) t = 0)
    (b : Fin (r + 1) → s2v_t11b_Formula (n + 1))
    (hb : ∀ i y, y ∈ (b i).realize ↔ ∃ a : C.realize,
        (∀ v, y v.succ = a.val v) ∧
        (∀ q : Fin r, q.val < i.val → ψ q a < y 0) ∧
        (∀ q : Fin r, i.val ≤ q.val → y 0 < ψ q a)) :
    ∀ i j, (∀ y ∈ (b i).realize,
      (P j).eval₂ (MvPolynomial.eval (fun v => y v.succ)) (y 0) < 0) ∨
      (∀ y ∈ (b i).realize,
      (P j).eval₂ (MvPolynomial.eval (fun v => y v.succ)) (y 0) = 0) ∨
      (∀ y ∈ (b i).realize,
      0 < (P j).eval₂ (MvPolynomial.eval (fun v => y v.succ)) (y 0)) := by
  classical
  intro i j
  rcases hz j with hzj | hzj
  · refine Or.inr (Or.inl ?_)
    intro y hy
    obtain ⟨a, ha, _⟩ := (hb i y).mp hy
    have he : (fun v => y v.succ) = (fun v => a.val v) := funext ha
    rw [he, Polynomial.eval₂_eq_eval_map, hzj a, Polynomial.eval_zero]
  · have hnonzero : ∀ y ∈ (b i).realize,
        (P j).eval₂ (MvPolynomial.eval (fun v => y v.succ)) (y 0) ≠ 0 := by
      intro y hy heval
      obtain ⟨a, ha, hlo, hhi⟩ := (hb i y).mp hy
      have he : (fun v => y v.succ) = (fun v => a.val v) := funext ha
      rw [he] at heval
      obtain ⟨q, hq⟩ := (hr a (y 0)).mpr ⟨j, hzj a, heval⟩
      rcases lt_or_ge q.val i.val with h | h
      · exact (ne_of_lt (hlo q h)) hq.symm
      · exact (ne_of_lt (hhi q h)) hq
    let F : EuclideanSpace ℝ (Fin (n + 1)) → ℝ :=
      fun y => (P j).eval₂ (MvPolynomial.eval (fun v => y v.succ)) (y 0)
    have hF : Continuous F := by
      let Q := (MvPolynomial.finSuccEquiv ℝ n).symm (P j)
      have he : ∀ y : EuclideanSpace ℝ (Fin (n + 1)),
          F y = MvPolynomial.eval (fun v => y v) Q := by
        intro y
        have h := (MvPolynomial.eval_eq_eval_mv_eval' (fun v => y v.succ) (y 0) Q).symm
        simp only [← Polynomial.eval₂_eq_eval_map] at h
        rw [AlgEquiv.apply_symm_apply] at h
        have hcoord : Fin.cons (y 0) (fun v => y v.succ) = (fun v => y v) := by
          funext v
          refine Fin.cases ?_ (fun _ => ?_) v <;> rfl
        simpa only [F, WithLp.ofLp_toLp, hcoord] using h
      rw [show F = (fun y => MvPolynomial.eval (fun v => y v) Q) from funext he]
      exact Q.continuous_eval.comp (by fun_prop)
    have hconn := s2v_hardt_cad3_band_preconnected C ψ hm hC hψ i (b i) (hb i)
    obtain ⟨a, ha⟩ := hC.nonempty
    obtain ⟨f, _, hf⟩ := s2v_hardt_cad3_continuous_height ψ hm hψ i
    let x : EuclideanSpace ℝ (Fin (n + 1)) :=
      WithLp.toLp 2 (Fin.cons (f ⟨a, ha⟩) (fun v => a v))
    have hx : x ∈ (b i).realize := (hb i x).mpr ⟨⟨a, ha⟩, (fun _ => rfl), hf _⟩
    rcases lt_or_gt_of_ne (hnonzero x hx) with hneg | hpos
    · refine Or.inl ?_
      intro y hy
      by_contra h
      have hle : 0 ≤ F y := le_of_not_gt h
      obtain ⟨z, hz, hez⟩ := hconn.intermediate_value hx hy hF.continuousOn
        (show (0 : ℝ) ∈ Set.Icc (F x) (F y) from ⟨le_of_lt hneg, hle⟩)
      exact hnonzero z hz hez
    · refine Or.inr (Or.inr ?_)
      intro y hy
      by_contra h
      have hle : F y ≤ 0 := le_of_not_gt h
      obtain ⟨z, hz, hez⟩ := hconn.intermediate_value hy hx hF.continuousOn
        (show (0 : ℝ) ∈ Set.Icc (F y) (F x) from ⟨hle, le_of_lt hpos⟩)
      exact hnonzero z hz hez


theorem s2v_hardt_cad3_section_sign_refinement_aux {n r k : ℕ}
    (C : s2v_t11b_Formula n) (ψ : Fin r → C.realize → ℝ)
    (hm : ∀ a, StrictMono (fun q => ψ q a))
    (g : Fin r → s2v_t11b_Formula (n + 1))
    (hg : ∀ q y, y ∈ (g q).realize ↔ ∃ a : C.realize,
      (∀ v, y v.succ = a.val v) ∧ y 0 = ψ q a)
    (P : Fin k → Polynomial (MvPolynomial (Fin n) ℝ)) :
    ∃ m : ℕ, ∃ c : Fin m → s2v_t11b_Formula n,
      (∀ i, (c i).realize.Nonempty) ∧
      Pairwise (fun i j => Disjoint (c i).realize (c j).realize) ∧
      (⋃ i, (c i).realize) = C.realize ∧
      ∀ i q j, (∀ a : C.realize, a.val ∈ (c i).realize →
        (P j).eval₂ (MvPolynomial.eval (fun v => a.val v)) (ψ q a) < 0) ∨
        (∀ a : C.realize, a.val ∈ (c i).realize →
        (P j).eval₂ (MvPolynomial.eval (fun v => a.val v)) (ψ q a) = 0) ∨
        (∀ a : C.realize, a.val ∈ (c i).realize →
        0 < (P j).eval₂ (MvPolynomial.eval (fun v => a.val v)) (ψ q a)) := by
  classical
  have form : ∀ (q : Fin r) (j : Fin k) (pos : Bool),
      ∃ F : s2v_t11b_Formula n, ∀ a : C.realize, a.val ∈ F.realize ↔
        if pos then 0 ≤ (P j).eval₂ (MvPolynomial.eval (fun v => a.val v)) (ψ q a)
        else (P j).eval₂ (MvPolynomial.eval (fun v => a.val v)) (ψ q a) ≤ 0 := by
    intro q j pos
    let Q := (MvPolynomial.finSuccEquiv ℝ n).symm (P j)
    let p := if pos then Q else -Q
    obtain ⟨F, hF⟩ := s2v_hardt_cad3_graph_substitution C (ψ q) (g q) (hg q)
      id (.nonneg p)
    have heval (a : C.realize) :
        MvPolynomial.eval (Fin.cons (ψ q a) (fun v => a.val v)) Q =
          (P j).eval₂ (MvPolynomial.eval (fun v => a.val v)) (ψ q a) := by
      rw [← s2v_t11b_finSucc_family_eval, AlgEquiv.apply_symm_apply]
    have hp (a : C.realize) :
        WithLp.toLp 2 (Fin.cons (ψ q a) (fun v => a.val v)) ∈
          (s2v_t11b_Formula.nonneg p).realize ↔
        if pos then 0 ≤ (P j).eval₂ (MvPolynomial.eval (fun v => a.val v)) (ψ q a)
        else (P j).eval₂ (MvPolynomial.eval (fun v => a.val v)) (ψ q a) ≤ 0 := by
      cases pos <;> simp only [p, Bool.false_eq_true, Bool.true_eq, ite_true, ite_false,
        s2v_t11b_Formula.realize, Set.mem_setOf_eq, WithLp.ofLp_toLp, map_neg,
        neg_nonneg, heval]
    refine ⟨F, ?_⟩
    intro a
    rw [hF]
    constructor
    · rintro ⟨a', ha', h⟩
      have he : a' = a := by
        apply Subtype.ext
        ext v
        exact (ha' v).symm
      subst a'
      exact (hp a).mp h
    · intro h
      exact ⟨a, (fun _ => rfl), (hp a).mpr h⟩
  choose f hf using form
  let J := Fin r × Fin k × Bool
  let E := Fintype.equivFin J
  let A : Fin (Fintype.card J) → s2v_t11b_Formula n :=
    fun i => f (E.symm i).1 (E.symm i).2.1 (E.symm i).2.2
  obtain ⟨m, c, hc, hdisj, hcover, hpattern⟩ := s2v_hardt_cad3_boolean_refinement C A
  have hlocus (q : Fin r) (j : Fin k) (pos : Bool) (a : C.realize) :
      a.val ∈ (A (E (q, j, pos))).realize ↔
        if pos then 0 ≤ (P j).eval₂ (MvPolynomial.eval (fun v => a.val v)) (ψ q a)
        else (P j).eval₂ (MvPolynomial.eval (fun v => a.val v)) (ψ q a) ≤ 0 := by
    simp only [A, E.symm_apply_apply]
    exact hf q j pos a
  refine ⟨m, c, hc, hdisj, hcover, ?_⟩
  intro i q j
  rcases hpattern i (E (q, j, true)) with hpos | hpos
  · rcases hpattern i (E (q, j, false)) with hneg | hneg
    · refine Or.inr (Or.inl ?_)
      intro a ha
      have hp : 0 ≤ (P j).eval₂ (MvPolynomial.eval (fun v => a.val v)) (ψ q a) :=
        (hlocus q j true a).mp (hpos a.val ha)
      have hn : (P j).eval₂ (MvPolynomial.eval (fun v => a.val v)) (ψ q a) ≤ 0 :=
        (hlocus q j false a).mp (hneg a.val ha)
      exact le_antisymm hn hp
    · refine Or.inr (Or.inr ?_)
      intro a ha
      apply lt_of_not_ge
      intro hn
      exact hneg a.val ha ((hlocus q j false a).mpr hn)
  · refine Or.inl ?_
    intro a ha
    apply lt_of_not_ge
    intro hp
    exact hpos a.val ha ((hlocus q j true a).mpr hp)

end HodgeLean.Foundations.Program
