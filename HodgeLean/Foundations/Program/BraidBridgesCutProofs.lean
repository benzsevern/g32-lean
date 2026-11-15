import HodgeLean.Foundations.Program.BraidBridgesDefs
import Mathlib.Analysis.Complex.Convex

noncomputable section
namespace HodgeLean.Foundations.Program

theorem b65x_slit_point (z : b65x_Down) :
    (∀ k, ¬ b65x_OnCut k z.val) ↔
      ∀ k, z.val.re = b65x_cutPoint k → 0 < z.val.im := by
  constructor
  · intro h k hk
    have hn : z.val.im ≠ 0 := by
      intro hi
      have hz : z.val = (b65x_cutPoint k : ℂ) := by
        apply Complex.ext <;> simp_all
      fin_cases k
      · exact z.property.2.1 (by simpa [b65x_cutPoint] using hz)
      · exact z.property.2.2 (by simpa [b65x_cutPoint] using hz)
      · exact z.property.1 (by simpa [b65x_cutPoint] using hz)
    exact lt_of_le_of_ne (not_lt.mp (fun hi ↦ h k ⟨hk, hi⟩)) (Ne.symm hn)
  · intro h k hk
    exact (not_lt_of_gt (h k hk.1)) hk.2

theorem b65x_slit_contractible :
    ContractibleSpace {z : ℂ // ∀ k, z.re = b65x_cutPoint k → 0 < z.im} := by
  let S := {z : ℂ // ∀ k, z.re = b65x_cutPoint k → 0 < z.im}
  let o : S := ⟨Complex.I, by simp⟩
  let g : C(S, S) := ⟨fun z ↦ ⟨⟨z.val.re, 1⟩, by simp⟩, by
    apply Continuous.subtype_mk
    simp only [Complex.mk_eq_add_mul_I]
    dsimp [S]
    fun_prop⟩
  have hm (t : unitInterval) (z : S) (k : Fin 3) (hk : z.val.re = b65x_cutPoint k) :
      0 < (1 - (t : ℝ)) * z.val.im + (t : ℝ) := by
    have hc := (convex_Ioi (0 : ℝ)) (z.property k hk) (by norm_num : (0 : ℝ) < 1)
      (sub_nonneg.mpr t.property.2) t.property.1 (sub_add_cancel 1 (t : ℝ))
    simpa only [smul_eq_mul, mul_one, Set.mem_Ioi] using hc
  let H : ContinuousMap.Homotopy (ContinuousMap.id S) g := {
    toFun := fun p ↦ ⟨⟨p.2.val.re, (1 - (p.1 : ℝ)) * p.2.val.im + (p.1 : ℝ)⟩,
      hm p.1 p.2⟩
    continuous_toFun := by
      apply Continuous.subtype_mk
      simp only [Complex.mk_eq_add_mul_I]
      dsimp [S]
      fun_prop
    map_zero_left := by intro z; apply Subtype.ext; apply Complex.ext <;> simp
    map_one_left := by intro z; apply Subtype.ext; apply Complex.ext <;> simp [g] }
  let K : ContinuousMap.Homotopy g (ContinuousMap.const S o) := {
    toFun := fun p ↦ ⟨⟨(1 - (p.1 : ℝ)) * p.2.val.re, 1⟩, by simp⟩
    continuous_toFun := by
      apply Continuous.subtype_mk
      simp only [Complex.mk_eq_add_mul_I]
      dsimp [S]
      fun_prop
    map_zero_left := by intro z; apply Subtype.ext; apply Complex.ext <;> simp [g]
    map_one_left := by intro z; apply Subtype.ext; apply Complex.ext <;> simp [o] }
  exact (contractible_iff_id_nullhomotopic S).mpr ⟨o, ⟨H.trans K⟩⟩

theorem b65x_slit_paths_homotopic {x y : b65x_Down} (p q : Path x y)
    (hp : ∀ t k, ¬ b65x_OnCut k (p t).val)
    (hq : ∀ t k, ¬ b65x_OnCut k (q t).val) : p.Homotopic q := by
  let S := {z : ℂ | ∀ k, z.re = b65x_cutPoint k → 0 < z.im}
  have hS : S ⊆ {z : ℂ | z ≠ 0 ∧ z ≠ 5 ∧ z ≠ -7} := by
    intro z hz
    refine ⟨?_, ?_, ?_⟩ <;> intro he <;> subst z
    · have := hz 2 (by norm_num [b65x_cutPoint]); norm_num at this
    · have := hz 0 (by norm_num [b65x_cutPoint]); norm_num at this
    · have := hz 1 (by norm_num [b65x_cutPoint]); norm_num at this
  let : ContractibleSpace S := b65x_slit_contractible
  let T : Set b65x_Down := {z | z.val ∈ S}
  let : ContractibleSpace T := RiemannRochTop_contractible_nested_subset S _ hS
  exact RiemannRochTop_paths_homotopic_in_subset (X := b65x_Down) T p q
    (fun t ↦ (b65x_slit_point (p t)).mp (hp t))
    (fun t ↦ (b65x_slit_point (q t)).mp (hq t))

theorem b65x_lower_subset : {z : ℂ | z.im < 0} ⊆
    {z : ℂ | z ≠ 0 ∧ z ≠ 5 ∧ z ≠ -7} := by
  intro z hz
  refine ⟨?_, ?_, ?_⟩ <;> intro he <;> subst z <;> norm_num at hz

theorem b65x_lower_contractible :
    ContractibleSpace {z : b65x_Down // z.val.im < 0} := by
  let S : Set ℂ := {z | z.im < 0}
  let : ContractibleSpace S := (convex_halfSpace_im_lt 0).contractibleSpace
    ⟨-Complex.I, by simp⟩
  exact RiemannRochTop_contractible_nested_subset S _ b65x_lower_subset

theorem b65x_lower_overlap_path {p q : b65x_Down}
    (hp : p.val.im < 0) (hq : q.val.im < 0)
    (hne : ∀ k, p.val.re ≠ b65x_cutPoint k)
    (hside : ∀ k, (p.val.re < b65x_cutPoint k ↔ q.val.re < b65x_cutPoint k) ∧
      (b65x_cutPoint k < p.val.re ↔ b65x_cutPoint k < q.val.re)) :
    ∃ L : Path p q, ∀ t, (L t).val.im < 0 ∧ ∀ k, ¬ b65x_OnCut k (L t).val := by
  let W : Set ℂ := {z | z.im < 0 ∧ ∀ k : Fin 3,
    if p.val.re < b65x_cutPoint k then z.re < b65x_cutPoint k
    else b65x_cutPoint k < z.re}
  have hW : Convex ℝ W := by
    intro x hx y hy a b ha hb hab
    refine ⟨(convex_halfSpace_im_lt 0) hx.1 hy.1 ha hb hab, ?_⟩
    intro k
    by_cases hk : p.val.re < b65x_cutPoint k
    · simpa only [Set.mem_ofPred_eq, ite_eq_left hk] using
        (convex_halfSpace_re_lt (b65x_cutPoint k))
          (by simpa only [Set.mem_ofPred_eq, ite_eq_left hk] using hx.2 k)
          (by simpa only [Set.mem_ofPred_eq, ite_eq_left hk] using hy.2 k) ha hb hab
    · simpa only [Set.mem_ofPred_eq, ite_eq_right hk] using
        (convex_halfSpace_re_gt (b65x_cutPoint k))
          (by simpa only [Set.mem_ofPred_eq, ite_eq_right hk] using hx.2 k)
          (by simpa only [Set.mem_ofPred_eq, ite_eq_right hk] using hy.2 k) ha hb hab
  have hpW : p.val ∈ W := by
    refine ⟨hp, fun k ↦ ?_⟩
    split_ifs with hk
    · exact hk
    · exact lt_of_le_of_ne (not_lt.mp hk) (hne k).symm
  have hqW : q.val ∈ W := by
    refine ⟨hq, fun k ↦ ?_⟩
    split_ifs with hk
    · exact (hside k).1.mp hk
    · exact (hside k).2.mp (lt_of_le_of_ne (not_lt.mp hk) (hne k).symm)
  let : ContractibleSpace W := hW.contractibleSpace ⟨p.val, hpW⟩
  let c := PathConnectedSpace.somePath (⟨p.val, hpW⟩ : W) ⟨q.val, hqW⟩
  let f : C(W, b65x_Down) := ⟨fun z ↦ ⟨z.val, b65x_lower_subset z.property.1⟩, by fun_prop⟩
  refine ⟨c.map f.continuous, fun t ↦ ⟨(c t).property.1, fun k hc ↦ ?_⟩⟩
  have h := (c t).property.2 k
  have hc : (c t).val.re = b65x_cutPoint k := hc.1
  split_ifs at h <;> exact (ne_of_lt h) (by first | exact hc | exact hc.symm)

theorem b65x_excursions_homotopic
    {x p q p' q' : b65x_Down}
    (a : Path x p) (d : Path p q) (b : Path q x)
    (a' : Path x p') (d' : Path p' q') (b' : Path q' x)
    (L : Path p p') (R : Path q q')
    (ha : ∀ t k, ¬ b65x_OnCut k (a t).val)
    (hd : ∀ t, (d t).val.im < 0)
    (hb : ∀ t k, ¬ b65x_OnCut k (b t).val)
    (ha' : ∀ t k, ¬ b65x_OnCut k (a' t).val)
    (hd' : ∀ t, (d' t).val.im < 0)
    (hb' : ∀ t k, ¬ b65x_OnCut k (b' t).val)
    (hL : ∀ t, (L t).val.im < 0 ∧ ∀ k, ¬ b65x_OnCut k (L t).val)
    (hR : ∀ t, (R t).val.im < 0 ∧ ∀ k, ¬ b65x_OnCut k (R t).val) :
    ((a.trans d).trans b).Homotopic ((a'.trans d').trans b') := by
  let S₀ : Set ℂ := {z | ∀ k, z.re = b65x_cutPoint k → 0 < z.im}
  have hS₀ : S₀ ⊆ {z : ℂ | z ≠ 0 ∧ z ≠ 5 ∧ z ≠ -7} := by
    intro z hz
    refine ⟨?_, ?_, ?_⟩ <;> intro he <;> subst z
    · have := hz 2 (by norm_num [b65x_cutPoint]); norm_num at this
    · have := hz 0 (by norm_num [b65x_cutPoint]); norm_num at this
    · have := hz 1 (by norm_num [b65x_cutPoint]); norm_num at this
  let S : Set b65x_Down := {z | z.val ∈ S₀}
  let T : Set b65x_Down := {z | z.val.im < 0}
  let : ContractibleSpace S₀ := b65x_slit_contractible
  let : ContractibleSpace S := RiemannRochTop_contractible_nested_subset S₀ _ hS₀
  let : ContractibleSpace T := b65x_lower_contractible
  exact RiemannRochTop_two_chart_loops_homotopic (X := b65x_Down) S T
    a d b a' d' b' L R
    (fun t ↦ (b65x_slit_point (a t)).mp (ha t)) hd
    (fun t ↦ (b65x_slit_point (b t)).mp (hb t))
    (fun t ↦ (b65x_slit_point (a' t)).mp (ha' t)) hd'
    (fun t ↦ (b65x_slit_point (b' t)).mp (hb' t))
    (fun t ↦ ⟨(b65x_slit_point (L t)).mp (hL t).2, (hL t).1⟩)
    (fun t ↦ ⟨(b65x_slit_point (R t)).mp (hR t).2, (hR t).1⟩)

theorem b65x_near_cut_sides (j : Fin 3) {x y : ℝ}
    (hx : |x - b65x_cutPoint j| < 1) (hy : |y - b65x_cutPoint j| < 1)
    (h : (x < b65x_cutPoint j ∧ y < b65x_cutPoint j) ∨
      (b65x_cutPoint j < x ∧ b65x_cutPoint j < y)) :
    ∀ k, (x < b65x_cutPoint k ↔ y < b65x_cutPoint k) ∧
      (b65x_cutPoint k < x ↔ b65x_cutPoint k < y) := by
  obtain ⟨hx₁, hx₂⟩ := abs_lt.mp hx
  obtain ⟨hy₁, hy₂⟩ := abs_lt.mp hy
  intro k
  fin_cases j <;> fin_cases k <;> norm_num [b65x_cutPoint] at * <;>
    rcases h with h | h <;> constructor <;> constructor <;> intro hh <;> linarith

theorem b65x_split_three {X : Type} [TopologicalSpace X] {x : X}
    (d : Path x x) (a b : unitInterval) :
    ((((d.subpath 0 a).cast d.source.symm rfl).trans (d.subpath a b)).trans
      ((d.subpath b 1).cast rfl d.target.symm)).Homotopic d := by
  have h := ((Path.Homotopic.subpath_trans_subpath d 0 a b).hcomp
    (Path.Homotopic.refl (d.subpath b 1))).trans
      (Path.Homotopic.subpath_trans_subpath d 0 b 1)
  have h' := h.pathCast d.source.symm d.target.symm
  rw [Path.subpath_zero_one] at h'
  convert h' using 1 <;> ext t <;> rfl

theorem b65x_single_excursion {x : b65x_Down} (d : Path x x) (j : Fin 3)
    (hd : b65x_CrossesAs d [(j, 1)]) :
    ∃ (p q : b65x_Down) (a : Path x p) (δ : Path p q) (b : Path q x),
      (∀ t k, ¬ b65x_OnCut k (a t).val) ∧
      (∀ t, (δ t).val.im < 0) ∧
      (∀ t k, ¬ b65x_OnCut k (b t).val) ∧
      |p.val.re - b65x_cutPoint j| < 1 ∧
      |q.val.re - b65x_cutPoint j| < 1 ∧
      p.val.re < b65x_cutPoint j ∧ b65x_cutPoint j < q.val.re ∧
      ((a.trans δ).trans b).Homotopic d := by
  obtain ⟨u, -, hu, -, hc, ε, hε, hdir⟩ := hd
  have hu₀ := hu 0
  have hc₀ : b65x_OnCut j (d (u 0)).val := (hc j (u 0)).mpr ⟨0, rfl, rfl⟩
  have hopen : IsOpen {s : unitInterval |
      |(d s).val.re - b65x_cutPoint j| < 1 ∧ (d s).val.im < 0} := by
    apply IsOpen.inter
    · exact isOpen_lt (show Continuous (fun s : unitInterval ↦
        |(d s).val.re - b65x_cutPoint j|) by fun_prop) continuous_const
    · exact isOpen_lt (show Continuous (fun s : unitInterval ↦ (d s).val.im) by
        fun_prop) continuous_const
  have hmem : u 0 ∈ {s : unitInterval |
      |(d s).val.re - b65x_cutPoint j| < 1 ∧ (d s).val.im < 0} := by
    exact ⟨by rw [hc₀.1]; norm_num, hc₀.2⟩
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hopen (u 0) hmem
  let v : ℝ := min r (min ε (min (u 0 : ℝ) (1 - (u 0 : ℝ)))) / 2
  have hu1 : 0 < 1 - (u 0 : ℝ) := by linarith [hu₀.2]
  have hu0 : 0 < (u 0 : ℝ) := hu₀.1
  have hv : 0 < v := by dsimp [v]; positivity
  have hvr : v < r := by
    have := min_le_left r (min ε (min (u 0 : ℝ) (1 - (u 0 : ℝ))))
    dsimp [v]; linarith
  have hvε : v < ε := by
    have h₁ := min_le_right r (min ε (min (u 0 : ℝ) (1 - (u 0 : ℝ))))
    have h₂ := min_le_left ε (min (u 0 : ℝ) (1 - (u 0 : ℝ)))
    dsimp [v]; linarith
  have hvu : v < (u 0 : ℝ) := by
    have h₁ := min_le_right r (min ε (min (u 0 : ℝ) (1 - (u 0 : ℝ))))
    have h₂ := min_le_right ε (min (u 0 : ℝ) (1 - (u 0 : ℝ)))
    have h₃ := min_le_left (u 0 : ℝ) (1 - (u 0 : ℝ))
    dsimp [v]; linarith
  have hv1 : v < 1 - (u 0 : ℝ) := by
    have h₁ := min_le_right r (min ε (min (u 0 : ℝ) (1 - (u 0 : ℝ))))
    have h₂ := min_le_right ε (min (u 0 : ℝ) (1 - (u 0 : ℝ)))
    have h₃ := min_le_right (u 0 : ℝ) (1 - (u 0 : ℝ))
    dsimp [v]; linarith
  let l : unitInterval := ⟨(u 0 : ℝ) - v, by constructor <;> linarith [hu₀.2]⟩
  let h : unitInterval := ⟨(u 0 : ℝ) + v, by constructor <;> linarith [hu₀.1]⟩
  have hl : |(l : ℝ) - u 0| = v := by dsimp [l]; rw [sub_sub_cancel_left, abs_neg, abs_of_pos hv]
  have hh : |(h : ℝ) - u 0| = v := by dsimp [h]; rw [add_sub_cancel_left, abs_of_pos hv]
  have hnear (s : unitInterval) (hs : |(s : ℝ) - u 0| < r) :
      |(d s).val.re - b65x_cutPoint j| < 1 ∧ (d s).val.im < 0 := by
    apply hball
    simpa only [Metric.mem_ball, Subtype.dist_eq, Real.dist_eq] using hs
  refine ⟨d l, d h, (d.subpath 0 l).cast d.source.symm rfl,
    d.subpath l h, (d.subpath h 1).cast rfl d.target.symm, ?_, ?_, ?_,
    (hnear l (hl ▸ hvr)).1, (hnear h (hh ▸ hvr)).1, ?_, ?_, b65x_split_three d l h⟩
  · intro t k hk
    have ht : (d.subpath 0 l) t ∈ Set.range (d.subpath 0 l) := Set.mem_range_self t
    rw [Path.range_subpath_of_le _ _ _ (unitInterval.nonneg l)] at ht
    obtain ⟨s, hs, he⟩ := ht
    have hcut : b65x_OnCut k (d s).val := by
      rw [he]
      exact hk
    obtain ⟨m, -, hm⟩ := (hc k s).mp hcut
    have hm₀ : m = 0 := by
      have hm : m.val = 0 := by
        have hm : m.val < 1 := m.isLt
        omega
      apply Fin.ext
      exact hm
    subst m
    have hsl : (s : ℝ) ≤ (l : ℝ) := hs.2
    rw [hm] at hsl
    dsimp [l] at hsl
    linarith
  · intro t
    have ht : (d.subpath l h) t ∈ Set.range (d.subpath l h) := Set.mem_range_self t
    rw [Path.range_subpath_of_le _ _ _ (by change (u 0 : ℝ) - v ≤ (u 0 : ℝ) + v; linarith)] at ht
    obtain ⟨s, hs, he⟩ := ht
    rw [← he]
    apply (hnear s ?_).2
    apply abs_lt.mpr
    have hsl : (l : ℝ) ≤ s := hs.1
    have hsh : (s : ℝ) ≤ h := hs.2
    dsimp [l, h] at hsl hsh
    constructor <;> linarith
  · intro t k hk
    have ht : (d.subpath h 1) t ∈ Set.range (d.subpath h 1) := Set.mem_range_self t
    rw [Path.range_subpath_of_le _ _ _ (unitInterval.le_one h)] at ht
    obtain ⟨s, hs, he⟩ := ht
    have hcut : b65x_OnCut k (d s).val := by
      rw [he]
      exact hk
    obtain ⟨m, -, hm⟩ := (hc k s).mp hcut
    have hm₀ : m = 0 := by
      have hm : m.val = 0 := by
        have hm : m.val < 1 := m.isLt
        omega
      apply Fin.ext
      exact hm
    subst m
    have hhs : (h : ℝ) ≤ s := hs.1
    rw [hm] at hhs
    dsimp [h] at hhs
    linarith
  · have hs := (hdir 0 l (hl ▸ hvε)).1 (by change (u 0 : ℝ) - v < (u 0 : ℝ); linarith)
    norm_num at hs
    linarith
  · have hs := (hdir 0 h (hh ▸ hvε)).2 (by change (u 0 : ℝ) < (u 0 : ℝ) + v; linarith)
    norm_num at hs
    linarith

theorem b65x_single_word_homotopic {x : b65x_Down} (d g : Path x x) (j : Fin 3)
    (hd : b65x_CrossesAs d [(j, 1)]) (hg : b65x_CrossesAs g [(j, 1)]) :
    d.Homotopic g := by
  obtain ⟨p, q, a, δ, b, ha, hδ, hb, hp, hq, hpj, hqj, hhom⟩ :=
    b65x_single_excursion d j hd
  obtain ⟨p', q', a', δ', b', ha', hδ', hb', hp', hq', hpj', hqj', hhom'⟩ :=
    b65x_single_excursion g j hg
  have hpne (k : Fin 3) : p.val.re ≠ b65x_cutPoint k := by
    intro he
    exact ha 1 k ⟨by simpa using he, by simpa using hδ 0⟩
  have hqne (k : Fin 3) : q.val.re ≠ b65x_cutPoint k := by
    intro he
    exact hb 0 k ⟨by simpa using he, by simpa using hδ 1⟩
  obtain ⟨L, hL⟩ := b65x_lower_overlap_path
    (show p.val.im < 0 by simpa using hδ 0)
    (show p'.val.im < 0 by simpa using hδ' 0) hpne
    (b65x_near_cut_sides j hp hp' (Or.inl ⟨hpj, hpj'⟩))
  obtain ⟨R, hR⟩ := b65x_lower_overlap_path
    (show q.val.im < 0 by simpa using hδ 1)
    (show q'.val.im < 0 by simpa using hδ' 1) hqne
    (b65x_near_cut_sides j hq hq' (Or.inr ⟨hqj, hqj'⟩))
  exact hhom.symm.trans ((b65x_excursions_homotopic a δ b a' δ' b' L R
    ha hδ hb ha' hδ' hb' hL hR).trans hhom')

theorem b65x_negative_symm {x : b65x_Down} (d : Path x x) (j : Fin 3)
    (hd : b65x_CrossesAs d [(j, -1)]) : b65x_CrossesAs d.symm [(j, 1)] := by
  obtain ⟨u, -, hu, -, hc, ε, hε, hdir⟩ := hd
  refine ⟨fun _ ↦ unitInterval.symm (u 0), ?_, ?_, ?_, ?_, ε, hε, ?_⟩
  · intro m n hmn
    have hm : m = 0 := Fin.eq_zero m
    have hn : n = 0 := Fin.eq_zero n
    subst m; subst n
    exact (lt_irrefl _ hmn).elim
  · intro m
    have := hu 0
    simp only [unitInterval.coe_symm_eq]
    constructor <;> linarith
  · intro m
    have hm : m = 0 := Fin.eq_zero m
    subst m
    exact Or.inl rfl
  · intro k s
    change b65x_OnCut k (d (unitInterval.symm s)).val ↔ _
    rw [hc]
    constructor
    · rintro ⟨m, hm, hs⟩
      have hm₀ : m = 0 := Fin.eq_zero m
      subst m
      refine ⟨0, hm, ?_⟩
      have he := congrArg unitInterval.symm hs
      simpa only [unitInterval.symm_symm] using he
    · rintro ⟨m, hm, hs⟩
      have hm₀ : m = 0 := Fin.eq_zero m
      subst m
      refine ⟨0, hm, ?_⟩
      rw [hs, unitInterval.symm_symm]
  · intro m s hs
    have hm : m = 0 := Fin.eq_zero m
    subst m
    have habs : |((unitInterval.symm s : unitInterval) : ℝ) - u 0| =
        |(s : ℝ) - unitInterval.symm (u 0)| := by
      simp only [unitInterval.coe_symm_eq]
      rw [show 1 - (s : ℝ) - u 0 = -((s : ℝ) - (1 - u 0)) by ring, abs_neg]
    have h := hdir 0 (unitInterval.symm s) (habs ▸ hs)
    constructor
    · intro hlt
      have hh : (u 0 : ℝ) < unitInterval.symm s := by
        simp only [unitInterval.coe_symm_eq] at hlt ⊢
        linarith
      have hh' := h.2 hh
      norm_num at hh' ⊢
      linarith
    · intro hlt
      have hh : ((unitInterval.symm s : unitInterval) : ℝ) < u 0 := by
        simp only [unitInterval.coe_symm_eq] at hlt ⊢
        linarith
      have hh' := h.1 hh
      norm_num at hh' ⊢
      linarith

theorem b65x_single_word_class {x : b65x_Down} (d g : Path x x) (j : Fin 3) (e : ℤ)
    (hd : b65x_CrossesAs d [(j, e)]) (hg : b65x_CrossesAs g [(j, 1)]) :
    FundamentalGroup.fromPath ⟦d⟧ = FundamentalGroup.fromPath ⟦g⟧ ^ e := by
  have he : e = 1 ∨ e = -1 := by
    obtain ⟨_, _, _, hsign, _⟩ := hd
    exact hsign 0
  rcases he with rfl | rfl
  · simpa using congrArg FundamentalGroup.fromPath
      (Quotient.sound (b65x_single_word_homotopic d g j hd hg))
  · have h := b65x_single_word_homotopic d.symm g j (b65x_negative_symm d j hd) hg
    have he : (FundamentalGroup.fromPath ⟦d⟧)⁻¹ = FundamentalGroup.fromPath ⟦g⟧ :=
      congrArg FundamentalGroup.fromPath (Quotient.sound h)
    rw [zpow_neg_one]
    exact inv_eq_iff_eq_inv.mp he

theorem b65x_empty_word {y : b65x_Down} (d : Path y y)
    (hd : b65x_CrossesAs d []) :
    FundamentalGroup.fromPath ⟦d⟧ = 1 := by
  obtain ⟨u, -, -, -, hc, -⟩ := hd
  have hn (s : unitInterval) (k : Fin 3) : ¬ b65x_OnCut k (d s).val := by
    rw [hc]
    simp
  have hy (k : Fin 3) : ¬ b65x_OnCut k y.val := by simpa using hn 0 k
  exact congrArg FundamentalGroup.fromPath (Quotient.sound
    (b65x_slit_paths_homotopic d (Path.refl y) hn (fun _ ↦ hy)))

theorem b65x_slit_path (x y : b65x_Down)
    (hx : ∀ k, ¬ b65x_OnCut k x.val) (hy : ∀ k, ¬ b65x_OnCut k y.val) :
    ∃ c : Path x y, ∀ t k, ¬ b65x_OnCut k (c t).val := by
  let S : Set ℂ := {z | ∀ k, z.re = b65x_cutPoint k → 0 < z.im}
  have hS : S ⊆ {z : ℂ | z ≠ 0 ∧ z ≠ 5 ∧ z ≠ -7} := by
    intro z hz
    refine ⟨?_, ?_, ?_⟩ <;> intro he <;> subst z
    · have := hz 2 (by norm_num [b65x_cutPoint]); norm_num at this
    · have := hz 0 (by norm_num [b65x_cutPoint]); norm_num at this
    · have := hz 1 (by norm_num [b65x_cutPoint]); norm_num at this
  let : ContractibleSpace S := b65x_slit_contractible
  let f : C(S, b65x_Down) := ⟨fun z ↦ ⟨z.val, hS z.property⟩, by fun_prop⟩
  let c := PathConnectedSpace.somePath (⟨x.val, (b65x_slit_point x).mp hx⟩ : S)
    ⟨y.val, (b65x_slit_point y).mp hy⟩
  exact ⟨c.map f.continuous, fun t ↦ (b65x_slit_point _).mpr (c t).property⟩

theorem b65x_split_based_class {X : Type} [TopologicalSpace X] {x : X}
    (d : Path x x) (v : unitInterval) (b : Path x (d v)) :
    FundamentalGroup.fromPath ⟦d⟧ =
      FundamentalGroup.fromPath ⟦b.trans ((d.subpath v 1).cast rfl d.target.symm)⟧ *
      FundamentalGroup.fromPath ⟦((d.subpath 0 v).cast d.source.symm rfl).trans b.symm⟧ := by
  let p := (d.subpath 0 v).cast d.source.symm rfl
  let q := (d.subpath v 1).cast rfl d.target.symm
  have h : ((p.trans b.symm).trans (b.trans q)).Homotopic (p.trans q) := by
    exact (Path.Homotopic.trans_assoc p b.symm (b.trans q)).trans
      ((Path.Homotopic.refl p).hcomp
        ((Path.Homotopic.trans_assoc b.symm b q).symm.trans
          (((Path.Homotopic.symm_trans b).hcomp (Path.Homotopic.refl q)).trans
            (Path.Homotopic.refl_trans q))))
  have hfull : (p.trans q).Homotopic d := by
    have hh := (Path.Homotopic.subpath_trans_subpath d 0 v 1).pathCast
      d.source.symm d.target.symm
    rw [Path.subpath_zero_one] at hh
    convert hh using 1 <;> ext t <;> rfl
  exact (congrArg FundamentalGroup.fromPath (Quotient.sound (h.trans hfull))).symm

theorem b65x_finite_based_subpaths {y : b65x_Down} (d : Path y y) {n : ℕ}
    (t : Fin (n + 1) → unitInterval) (ht0 : t 0 = 0) (ht1 : t (Fin.last n) = 1)
    (ht : ∀ i k, ¬ b65x_OnCut k (d (t i)).val) :
    ∃ a : (i : Fin (n + 1)) → Path y (d (t i)),
      (∀ i s k, ¬ b65x_OnCut k (a i s).val) ∧
      FundamentalGroup.fromPath ⟦d⟧ =
        (List.ofFn (fun k : Fin n ↦ FundamentalGroup.fromPath
          ⟦(a k.castSucc).trans
            ((d.subpath (t k.castSucc) (t k.succ)).trans (a k.succ).symm)⟧)).reverse.prod := by
  have h0 : d (t 0) = y := by rw [ht0]; exact d.source
  have h1 : d (t (Fin.last n)) = y := by rw [ht1]; exact d.target
  have hy (k : Fin 3) : ¬ b65x_OnCut k y.val := by simpa only [h0] using ht 0 k
  choose a ha using fun i ↦ b65x_slit_path y (d (t i)) hy (ht i)
  refine ⟨a, ha, ?_⟩
  let A : Path y y := (a 0).cast rfl h0.symm
  let B : Path y y := (a (Fin.last n)).cast rfl h1.symm
  have hA : A.Homotopic (Path.refl y) :=
    b65x_slit_paths_homotopic A (Path.refl y) (ha 0) (fun _ ↦ hy)
  have hB : B.symm.Homotopic (Path.refl y) :=
    b65x_slit_paths_homotopic B.symm (Path.refl y)
      (fun s ↦ ha (Fin.last n) (unitInterval.symm s)) (fun _ ↦ hy)
  have hsub := Path.Homotopic.concat_subpath d t
  have hmid := (Path.Homotopic.refl (a 0)).hcomp
    (hsub.hcomp (Path.Homotopic.refl (a (Fin.last n)).symm))
  have hh : ((a 0).trans ((Path.concat (d ∘ t)
      (fun k ↦ d.subpath (t k.castSucc) (t k.succ))).trans
        (a (Fin.last n)).symm)).Homotopic (A.trans (d.trans B.symm)) := by
    convert hmid using 1
    ext s
    simp only [Path.trans_apply, Path.cast_coe, Path.subpath, ht0, ht1,
      Path.symm_apply, A, B]
    congr 2
    ext
    simp
  have hfinish := (hA.hcomp ((Path.Homotopic.refl d).hcomp hB)).trans
    ((Path.Homotopic.refl_trans (d.trans (Path.refl y))).trans
      (Path.Homotopic.trans_refl d))
  have heq := congrArg FundamentalGroup.fromPath (Quotient.sound (hh.trans hfinish))
  exact heq.symm.trans (RiemannRochTop_concat_based_loop_class y (d ∘ t)
    (fun k ↦ d.subpath (t k.castSucc) (t k.succ)) a)

theorem b65x_cut_word_short {y : b65x_Down} (g : Fin 3 → Path y y)
    (hg : ∀ j, b65x_CrossesAs (g j) [(j, 1)])
    (d : Path y y) (w : List (Fin 3 × ℤ)) (hd : b65x_CrossesAs d w)
    (hw : w.length ≤ 1) :
    FundamentalGroup.fromPath ⟦d⟧ =
      (w.reverse.map (fun a ↦ FundamentalGroup.fromPath ⟦g a.1⟧ ^ a.2)).prod := by
  cases w with
  | nil => simpa using b65x_empty_word d hd
  | cons a w =>
    have hw₀ : w = [] := by simpa using hw
    subst w
    simpa using b65x_single_word_class d (g a.1) a.1 a.2 hd (hg a.1)

theorem b65x_stemmed_single {x p q : b65x_Down}
    (a : Path x p) (d : Path p q) (b : Path q x)
    (ha : ∀ s k, ¬ b65x_OnCut k (a s).val)
    (hb : ∀ s k, ¬ b65x_OnCut k (b s).val)
    (j : Fin 3) (e : ℤ) (he : e = 1 ∨ e = -1)
    (u : unitInterval) (hu0 : 0 < (u : ℝ)) (hu1 : (u : ℝ) < 1)
    (hc : ∀ k s, b65x_OnCut k (d s).val ↔ k = j ∧ s = u)
    (ε : ℝ) (hε : 0 < ε)
    (hs : ∀ s : unitInterval, |(s : ℝ) - u| < ε →
      ((s : ℝ) < u → (e : ℝ) * ((d s).val.re - b65x_cutPoint j) < 0) ∧
      ((u : ℝ) < s → 0 < (e : ℝ) * ((d s).val.re - b65x_cutPoint j))) :
    b65x_CrossesAs (a.trans (d.trans b)) [(j, e)] := by
  let v : unitInterval := ⟨(2 + (u : ℝ)) / 4, by constructor <;> linarith⟩
  have hv0 : (1 / 2 : ℝ) < v := by dsimp [v]; linarith
  have hv1 : (v : ℝ) < 3 / 4 := by dsimp [v]; linarith
  have hmiddle (s : unitInterval) (h0 : (1 / 2 : ℝ) < s) (h1 : (s : ℝ) ≤ 3 / 4) :
      (a.trans (d.trans b)) s = d ⟨4 * (s : ℝ) - 2, by constructor <;> linarith⟩ := by
    rw [Path.trans_apply, dite_eq_right (not_le.mpr h0), Path.trans_apply]
    rw [dite_eq_left (by change 2 * (s : ℝ) - 1 ≤ 1 / 2; linarith)]
    congr 1
    apply Subtype.ext
    dsimp
    ring
  refine ⟨fun _ ↦ v, ?_, ?_, (fun m ↦ by simpa using he), ?_,
    min (ε / 4) (min ((v : ℝ) - 1/2) (3/4 - (v : ℝ))), by positivity, ?_⟩
  · intro m n hmn
    have hm : m = 0 := Fin.eq_zero m
    have hn : n = 0 := Fin.eq_zero n
    subst m; subst n
    exact (lt_irrefl _ hmn).elim
  · intro m
    constructor <;> dsimp [v] <;> linarith
  · intro k s
    change b65x_OnCut k ((a.trans (d.trans b)) s).val ↔
      ∃ m : Fin 1, ([(j, e)] : List (Fin 3 × ℤ))[m].1 = k ∧ s = v
    simp only [Fin.exists_fin_one]
    change b65x_OnCut k ((a.trans (d.trans b)) s).val ↔ j = k ∧ s = v
    rw [eq_comm (a := j) (b := k)]
    by_cases h0 : (s : ℝ) ≤ 1/2
    · rw [Path.trans_apply, dite_eq_left h0]
      constructor
      · intro h; exact (ha _ k h).elim
      · rintro ⟨_, rfl⟩; exact (not_le.mpr hv0 h0).elim
    · have h0' := lt_of_not_ge h0
      by_cases h1 : (s : ℝ) ≤ 3/4
      · rw [hmiddle s h0' h1, hc]
        constructor
        · rintro ⟨hk, ht⟩
          refine ⟨hk, Subtype.ext ?_⟩
          have ht := congrArg Subtype.val ht
          dsimp [v] at *
          linarith
        · rintro ⟨hk, ht⟩
          refine ⟨hk, Subtype.ext ?_⟩
          change 4 * (s : ℝ) - 2 = (u : ℝ)
          have ht := congrArg Subtype.val ht
          dsimp [v] at ht
          linarith
      · rw [Path.trans_apply, dite_eq_right h0, Path.trans_apply,
          dite_eq_right (by change ¬ 2 * (s : ℝ) - 1 ≤ 1/2; linarith)]
        constructor
        · intro h; exact (hb _ k h).elim
        · rintro ⟨_, rfl⟩; exact (h1 (le_of_lt hv1)).elim
  · intro m s hnear
    have hm : m = 0 := Fin.eq_zero m
    subst m
    have hε' : |(s : ℝ) - v| < ε / 4 := lt_of_lt_of_le hnear (min_le_left _ _)
    have hl : |(s : ℝ) - v| < (v : ℝ) - 1/2 :=
      lt_of_lt_of_le hnear (le_trans (min_le_right _ _) (min_le_left _ _))
    have hr : |(s : ℝ) - v| < 3/4 - (v : ℝ) :=
      lt_of_lt_of_le hnear (le_trans (min_le_right _ _) (min_le_right _ _))
    have hl' := (abs_lt.mp hl).1
    have hr' := (abs_lt.mp hr).2
    have h0 : (1/2 : ℝ) < s := by linarith
    have h1 : (s : ℝ) ≤ 3/4 := by linarith
    rw [hmiddle s h0 h1]
    have hdnear : |(4 * (s : ℝ) - 2) - u| < ε := by
      have h := abs_lt.mp hε'
      apply abs_lt.mpr
      dsimp [v] at h
      constructor <;> linarith [h.1, h.2]
    have h := hs ⟨4 * (s : ℝ) - 2, by constructor <;> linarith⟩ hdnear
    constructor
    · intro hlt
      apply h.1
      change 4 * (s : ℝ) - 2 < u
      dsimp [v] at hlt
      linarith
    · intro hlt
      apply h.2
      change (u : ℝ) < 4 * (s : ℝ) - 2
      dsimp [v] at hlt
      linarith

theorem b65x_subpath_stemmed_single {y : b65x_Down}
    (d : Path y y) (w : List (Fin 3 × ℤ))
    (u : Fin w.length → unitInterval)
    (he : ∀ m : Fin w.length, w[m].2 = 1 ∨ w[m].2 = -1)
    (hc : ∀ k s, b65x_OnCut k (d s).val ↔ ∃ m : Fin w.length, w[m].1 = k ∧ s = u m)
    (ε : ℝ) (hε : 0 < ε)
    (hs : ∀ (m : Fin w.length) (s : unitInterval), |(s : ℝ) - u m| < ε →
      ((s : ℝ) < u m → (w[m].2 : ℝ) * ((d s).val.re - b65x_cutPoint w[m].1) < 0) ∧
      ((u m : ℝ) < s → 0 < (w[m].2 : ℝ) * ((d s).val.re - b65x_cutPoint w[m].1)))
    (m : Fin w.length) (l r : unitInterval)
    (hl : (l : ℝ) < u m) (hr : (u m : ℝ) < r)
    (hisolate : ∀ n : Fin w.length, (l : ℝ) ≤ u n → (u n : ℝ) ≤ r → n = m)
    (a : Path y (d l)) (b : Path (d r) y)
    (ha : ∀ s k, ¬ b65x_OnCut k (a s).val)
    (hb : ∀ s k, ¬ b65x_OnCut k (b s).val) :
    b65x_CrossesAs (a.trans ((d.subpath l r).trans b)) [w[m]] := by
  have hrl : 0 < (r : ℝ) - l := by linarith
  let v : unitInterval := ⟨((u m : ℝ) - l) / ((r : ℝ) - l), by
    constructor
    · exact le_of_lt (div_pos (sub_pos.mpr hl) hrl)
    · apply (div_le_one hrl).mpr; linarith⟩
  have hv : (v : ℝ) * ((r : ℝ) - l) = (u m : ℝ) - l := by
    dsimp [v]; field_simp
  have hv0 : 0 < (v : ℝ) := div_pos (sub_pos.mpr hl) hrl
  have hv1 : (v : ℝ) < 1 := by
    apply (div_lt_one hrl).mpr; linarith
  have hparam (s : unitInterval) :
      ((Set.Icc.convexComb l r s : unitInterval) : ℝ) =
        (l : ℝ) + (s : ℝ) * ((r : ℝ) - l) := by
    simp only [Set.Icc.coe_convexComb]; ring
  refine b65x_stemmed_single a (d.subpath l r) b ha hb w[m].1 w[m].2 (he m) v hv0 hv1
    ?_ (ε / ((r : ℝ) - l)) (div_pos hε hrl) ?_
  · intro k s
    change b65x_OnCut k (d (Set.Icc.convexComb l r s)).val ↔ _
    rw [hc]
    constructor
    · rintro ⟨n, hn, ht⟩
      have htn := congrArg Subtype.val ht
      rw [hparam] at htn
      have hn0 : (l : ℝ) ≤ u n := by nlinarith [s.property.1]
      have hn1 : (u n : ℝ) ≤ r := by nlinarith [s.property.2]
      have hnm := hisolate n hn0 hn1
      subst n
      refine ⟨hn.symm, Subtype.ext ?_⟩
      nlinarith
    · rintro ⟨hk, ht⟩
      refine ⟨m, hk.symm, Subtype.ext ?_⟩
      rw [hparam, ht]
      linarith
  · intro s hnear
    have habs : |((Set.Icc.convexComb l r s : unitInterval) : ℝ) - u m| =
        |(s : ℝ) - v| * ((r : ℝ) - l) := by
      rw [hparam]
      have hrewrite : (l : ℝ) + (s : ℝ) * ((r : ℝ) - l) - u m =
          ((s : ℝ) - v) * ((r : ℝ) - l) := by nlinarith [hv]
      rw [hrewrite, abs_mul, abs_of_pos hrl]
    have hnear' : |((Set.Icc.convexComb l r s : unitInterval) : ℝ) - u m| < ε := by
      rw [habs]
      exact (lt_div_iff₀ hrl).mp hnear
    have h := hs m (Set.Icc.convexComb l r s) hnear'
    change (_ → (w[m].2 : ℝ) * ((d (Set.Icc.convexComb l r s)).val.re - _) < 0) ∧ _
    constructor
    · intro hlt
      apply h.1
      rw [hparam]
      nlinarith [mul_pos (sub_pos.mpr hlt) hrl]
    · intro hlt
      apply h.2
      rw [hparam]
      nlinarith [mul_pos (sub_pos.mpr hlt) hrl]

theorem b65x_crossing_samples {n : ℕ} (hn : 0 < n)
    (u : Fin n → unitInterval) (hu : StrictMono u)
    (hint : ∀ m, 0 < (u m : ℝ) ∧ (u m : ℝ) < 1) :
    ∃ t : Fin (n + 1) → unitInterval, t 0 = 0 ∧ t (Fin.last n) = 1 ∧
      ∀ (i : Fin (n + 1)) (m : Fin n),
        (m.val < i.val → (u m : ℝ) < t i) ∧
        (i.val ≤ m.val → (t i : ℝ) < u m) := by
  let t : Fin (n + 1) → unitInterval := fun i ↦
    if h0 : i.val = 0 then 0 else
    if hlast : i.val = n then 1 else
    ⟨((u ⟨i.val - 1, by omega⟩ : ℝ) + (u ⟨i.val, by omega⟩ : ℝ)) / 2, by
      constructor
      · linarith [(u ⟨i.val - 1, by omega⟩).property.1,
          (u ⟨i.val, by omega⟩).property.1]
      · linarith [(u ⟨i.val - 1, by omega⟩).property.2,
          (u ⟨i.val, by omega⟩).property.2]⟩
  refine ⟨t, ?_, ?_, ?_⟩
  · simp [t]
  · simp [t, ne_of_gt hn]
  · intro i m
    dsimp [t]
    split_ifs with h0 hlast
    · constructor
      · intro hm; omega
      · intro _; exact (hint m).1
    · constructor
      · intro _; exact (hint m).2
      · intro hm; omega
    · let p : Fin n := ⟨i.val - 1, by omega⟩
      let q : Fin n := ⟨i.val, by omega⟩
      have hpq : p < q := by change i.val - 1 < i.val; omega
      have hupq : (u p : ℝ) < u q := hu hpq
      constructor
      · intro hm
        have hmp : m ≤ p := by change m.val ≤ i.val - 1; omega
        have hle : (u m : ℝ) ≤ u p := hu.monotone hmp
        change (u m : ℝ) < ((u p : ℝ) + u q) / 2
        linarith
      · intro hm
        have hqm : q ≤ m := hm
        have hle : (u q : ℝ) ≤ u m := hu.monotone hqm
        change ((u p : ℝ) + u q) / 2 < (u m : ℝ)
        linarith

end HodgeLean.Foundations.Program
