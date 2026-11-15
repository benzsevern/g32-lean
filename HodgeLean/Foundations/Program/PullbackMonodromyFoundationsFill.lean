import HodgeLean.Foundations.Program.PullbackMonodromyFoundationsDefs

/-! # Filling finitely many points of an open set of the sphere

The argument is written for a continuous map `ι : Z' → Z` with a family of good open sets of `Z`
(`b65t_GoodFamily`), and then specialised to the inclusion `X \ F → X`. Surjectivity on
fundamental groups is a continuous induction along the loop. The kernel is the grid argument for a
null-homotopy: a Lebesgue number, grid vertices moved into `Z'`, grid edges replaced by paths of
`Z'` inside the good sets of the adjacent cells, and a telescoping identity in the quotient group.
HC no distance; AV milestone no distance.
-/

noncomputable section
open Set Metric Filter
open scoped Topology
namespace HodgeLean.Foundations.Program

section Main

open scoped unitInterval

section Reparam

variable {Z : Type*} [TopologicalSpace Z]

/-- Two paths of `Z` that factor pointwise through paths with the same endpoints in a simply
connected space are homotopic. -/
theorem b65t_homotopic_of_factor {Y : Type*} [TopologicalSpace Y] [SimplyConnectedSpace Y]
    (f : C(Y, Z)) {u v : Y} (p q : Path u v) {x y : Z} (P Q : Path x y)
    (hP : ∀ s, P s = f (p s)) (hQ : ∀ s, Q s = f (q s)) : P.Homotopic Q := by
  have hx : x = f u := by rw [← P.source, hP, p.source]
  have hy : y = f v := by rw [← P.target, hP, p.target]
  have e1 : P = (p.map f.continuous).cast hx hy := by ext s; exact hP s
  have e2 : Q = (q.map f.continuous).cast hx hy := by ext s; exact hQ s
  rw [e1, e2]
  exact ((SimplyConnectedSpace.paths_homotopic p q).map f).pathCast hx hy

instance b65t_I_simply : SimplyConnectedSpace I :=
  haveI : ContractibleSpace I := (convex_Icc (0 : ℝ) 1).contractibleSpace ⟨0, by simp⟩
  inferInstance

/-- The affine path between two points of the unit interval. -/
def b65t_Ipath (u v : I) : Path u v where
  toFun s := ⟨(1 - (s : ℝ)) * u + s * v, by
    have := s.2.1; have := s.2.2; have := u.2.1; have := u.2.2; have := v.2.1; have := v.2.2
    constructor <;> nlinarith⟩
  continuous_toFun := by fun_prop
  source' := by ext; simp
  target' := by ext; simp

theorem b65t_Ipath_mem (u v s : I) : ((b65t_Ipath u v s : I) : ℝ) ∈ uIcc (u : ℝ) v := by
  have h := s.2
  change (1 - (s : ℝ)) * u + s * v ∈ uIcc (u : ℝ) v
  rw [← segment_eq_uIcc]
  exact ⟨1 - s, s, by linarith [h.2], h.1, by ring, by simp [smul_eq_mul]⟩

/-- The piece of a path between two parameters. -/
def b65t_seg {x y : Z} (γ : Path x y) (u v : I) : Path (γ u) (γ v) :=
  (b65t_Ipath u v).map γ.continuous

/-- The initial piece of a path up to a parameter. -/
def b65t_init {x y : Z} (γ : Path x y) (t : I) : Path x (γ t) :=
  (b65t_seg γ 0 t).cast γ.source.symm rfl

theorem b65t_seg_apply {x y : Z} (γ : Path x y) (u v s : I) :
    b65t_seg γ u v s = γ (b65t_Ipath u v s) := rfl

theorem b65t_init_apply {x y : Z} (γ : Path x y) (t s : I) :
    b65t_init γ t s = γ (b65t_Ipath 0 t s) := rfl

theorem b65t_trans_factor {Y : Type*} [TopologicalSpace Y] (f : C(Y, Z)) {u v w : Y}
    (p : Path u v) (q : Path v w) {x y z : Z} (P : Path x y) (Q : Path y z)
    (hP : ∀ s, P s = f (p s)) (hQ : ∀ s, Q s = f (q s)) (s : I) :
    (P.trans Q) s = f ((p.trans q) s) := by
  rw [Path.trans_apply, Path.trans_apply]
  split_ifs <;> simp [hP, hQ]

theorem b65t_init_trans_seg {x y : Z} (γ : Path x y) (s t : I) :
    ((b65t_init γ s).trans (b65t_seg γ s t)).Homotopic (b65t_init γ t) :=
  b65t_homotopic_of_factor ⟨γ, γ.continuous⟩ ((b65t_Ipath 0 s).trans (b65t_Ipath s t))
    (b65t_Ipath 0 t) _ _
    (b65t_trans_factor ⟨γ, γ.continuous⟩ _ _ _ _ (fun _ ↦ rfl) (fun _ ↦ rfl)) (fun _ ↦ rfl)

theorem b65t_init_zero {x y : Z} (γ : Path x y) :
    (b65t_init γ 0).Homotopic ((Path.refl x).cast rfl γ.source) :=
  b65t_homotopic_of_factor ⟨γ, γ.continuous⟩ (b65t_Ipath 0 0) (Path.refl 0) _ _
    (fun _ ↦ rfl) (fun s ↦ by simp)

theorem b65t_init_one {x y : Z} (γ : Path x y) :
    (b65t_init γ 1).Homotopic (γ.cast rfl γ.target) :=
  b65t_homotopic_of_factor ⟨γ, γ.continuous⟩ (b65t_Ipath 0 1)
    ⟨⟨id, continuous_id⟩, rfl, rfl⟩ _ _ (fun _ ↦ rfl) (fun _ ↦ rfl)

theorem b65t_trans_mem {x y z : Z} {U : Set Z} {p : Path x y} {q : Path y z}
    (hp : ∀ s, p s ∈ U) (hq : ∀ s, q s ∈ U) (s : I) : (p.trans q) s ∈ U := by
  rw [Path.trans_apply]; split_ifs
  · exact hp _
  · exact hq _

theorem b65t_trans_mem_map {Y : Type*} (f : Z → Y) {x y z : Z} {U : Set Y} {p : Path x y}
    {q : Path y z} (hp : ∀ s, f (p s) ∈ U) (hq : ∀ s, f (q s) ∈ U) (s : I) :
    f ((p.trans q) s) ∈ U := by
  rw [Path.trans_apply]; split_ifs
  · exact hp _
  · exact hq _

theorem b65t_symm_mem {x y : Z} {U : Set Z} {p : Path x y} (hp : ∀ s, p s ∈ U) (s : I) :
    p.symm s ∈ U :=
  hp _

theorem b65t_q_cancel {x y z : Z} (B : Path.Homotopic.Quotient x y)
    (C : Path.Homotopic.Quotient x z) : B.trans (B.symm.trans C) = C := by
  rw [← Path.Homotopic.Quotient.trans_assoc, Path.Homotopic.Quotient.trans_symm,
    Path.Homotopic.Quotient.refl_trans]

theorem b65t_dist_of_mem_uIcc {t r r' : I} (h : (r' : ℝ) ∈ uIcc (t : ℝ) r) :
    dist r' t ≤ dist r t := by
  rw [Subtype.dist_eq, Subtype.dist_eq, Real.dist_eq, Real.dist_eq]
  exact abs_sub_left_of_mem_uIcc h

end Reparam

/-- Good open sets for a continuous map `ι : Z' → Z`: open, a basis, path-connected, joined
through `Z'`, meeting the image of `ι`, and simply connected in `Z`.
Source: Hatcher, Algebraic Topology, §1.2, proof of Theorem 1.20 (van Kampen). -/
structure b65t_GoodFamily {Z Z' : Type*} [TopologicalSpace Z] [TopologicalSpace Z']
    (ι : C(Z', Z)) (𝒢 : Set (Set Z)) : Prop where
  isOpen : ∀ U ∈ 𝒢, IsOpen U
  basis : ∀ (z : Z) (W : Set Z), IsOpen W → z ∈ W → ∃ U ∈ 𝒢, z ∈ U ∧ U ⊆ W
  joined : ∀ U ∈ 𝒢, ∀ a ∈ U, ∀ b ∈ U, ∃ p : Path a b, ∀ t, p t ∈ U
  meets : ∀ U ∈ 𝒢, ∀ z ∈ U, ∃ w : Z', ι w ∈ U
  joined' : ∀ U ∈ 𝒢, ∀ a b : Z', ι a ∈ U → ι b ∈ U → ∃ p : Path a b, ∀ t, ι (p t) ∈ U
  homotopic : ∀ U ∈ 𝒢, ∀ {a b : Z} (p q : Path a b), (∀ t, p t ∈ U) → (∀ t, q t ∈ U) →
    p.Homotopic q


/-- In a group, a grid of edge elements whose cells commute has commuting boundary. -/
theorem b65t_grid_prod {Q : Type*} [Group Q] (n m : ℕ) (A B : ℕ → ℕ → Q)
    (hcell : ∀ i < n, ∀ j < m, A i j * B (i + 1) j = B i j * A i (j + 1)) :
    ((List.range n).map (A · 0)).prod * ((List.range m).map (B n ·)).prod =
      ((List.range m).map (B 0 ·)).prod * ((List.range n).map (A · m)).prod := by
  have row : ∀ j < m, ∀ k ≤ n,
      ((List.range k).map (A · j)).prod * B k j = B 0 j * ((List.range k).map (A · (j + 1))).prod := by
    intro j hj k hk
    induction k with
    | zero => simp
    | succ k ih =>
      rw [List.range_succ, List.map_append, List.prod_append, List.map_append, List.prod_append,
        List.map_singleton, List.prod_singleton, List.map_singleton, List.prod_singleton,
        mul_assoc, hcell k (by omega) j hj, ← mul_assoc, ih (by omega), mul_assoc]
  have col : ∀ l ≤ m, ((List.range n).map (A · 0)).prod * ((List.range l).map (B n ·)).prod =
      ((List.range l).map (B 0 ·)).prod * ((List.range n).map (A · l)).prod := by
    intro l hl
    induction l with
    | zero => simp
    | succ l ih =>
      rw [List.range_succ, List.map_append, List.prod_append, List.map_append, List.prod_append,
        List.map_singleton, List.prod_singleton, List.map_singleton, List.prod_singleton,
        ← mul_assoc, ih (by omega), mul_assoc, row l (by omega) n le_rfl, ← mul_assoc]
  exact col m le_rfl

section Phi

open CategoryTheory

variable {Z' : Type*} [TopologicalSpace Z'] {x : Z'}

/-- The arrow of a path in the fundamental groupoid. -/
abbrev b65t_arr {a b : Z'} (p : Path a b) : FundamentalGroupoid.mk a ⟶ FundamentalGroupoid.mk b :=
  FundamentalGroupoid.fromPath (Path.Homotopic.Quotient.mk p)

theorem b65t_arr_trans {a b c : Z'} (p : Path a b) (q : Path b c) :
    b65t_arr (p.trans q) = b65t_arr p ≫ b65t_arr q :=
  Path.Homotopic.Quotient.mk_trans p q

theorem b65t_arr_refl (a : Z') : b65t_arr (Path.refl a) = 𝟙 _ := rfl

theorem b65t_arr_symm {a b : Z'} (p : Path a b) : b65t_arr p.symm = Groupoid.inv (b65t_arr p) :=
  rfl

theorem b65t_inv_comp_assoc {a b c : FundamentalGroupoid Z'} (f : a ⟶ b) (g : b ⟶ c) :
    Groupoid.inv f ≫ f ≫ g = g := by
  rw [← Category.assoc, Groupoid.inv_comp, Category.id_comp]

/-- The chosen class of paths from the base point to a joined point. -/
def b65t_tau {a : Z'} (h : Joined x a) :
    (FundamentalGroupoid.mk x ⟶ FundamentalGroupoid.mk a) :=
  b65t_arr h.somePath

open Classical in
/-- A path of `Z'`, brought to the base point along the chosen paths, in the quotient by `N`. -/
def b65t_Phi (N : Subgroup (FundamentalGroup Z' x)) [N.Normal] {a b : Z'} (p : Path a b) :
    FundamentalGroup Z' x ⧸ N :=
  if h : Joined x a then
    ((End.of (b65t_tau h ≫ b65t_arr p ≫ Groupoid.inv (b65t_tau (h.trans ⟨p⟩))) :
      FundamentalGroup Z' x) : FundamentalGroup Z' x ⧸ N)⁻¹
  else 1

variable (N : Subgroup (FundamentalGroup Z' x)) [N.Normal]

theorem b65t_Phi_trans {a b c : Z'} (p : Path a b) (q : Path b c) :
    b65t_Phi N (p.trans q) = b65t_Phi N p * b65t_Phi N q := by
  by_cases h : Joined x a
  · have hb : Joined x b := h.trans ⟨p⟩
    simp only [b65t_Phi, h, hb, ↓reduceDIte]
    rw [← mul_inv_rev, ← QuotientGroup.mk_mul]
    congr 2
    ext
    simp only [End.mul_asHom, b65t_arr_trans, Category.assoc, b65t_inv_comp_assoc]
  · have hb : ¬ Joined x b := fun hb ↦ h (hb.trans ⟨p.symm⟩)
    simp only [b65t_Phi, h, hb, ↓reduceDIte, mul_one]

theorem b65t_Phi_homotopic {a b : Z'} {p q : Path a b} (hpq : p.Homotopic q) :
    b65t_Phi N p = b65t_Phi N q := by
  have : b65t_arr p = b65t_arr q := Quotient.sound hpq
  simp only [b65t_Phi, this]

theorem b65t_Phi_refl (a : Z') : b65t_Phi N (Path.refl a) = 1 := by
  by_cases h : Joined x a
  · simp only [b65t_Phi, h, ↓reduceDIte, b65t_arr_refl, Category.id_comp, Groupoid.comp_inv]
    rw [inv_eq_one]
    rfl
  · simp only [b65t_Phi, h, ↓reduceDIte]

theorem b65t_Phi_cast {a b a' b' : Z'} (p : Path a b) (ha : a' = a) (hb : b' = b) :
    b65t_Phi N (p.cast ha hb) = b65t_Phi N p := by
  subst ha hb; rfl

end Phi

section Abstract

variable {Z Z' : Type*} [TopologicalSpace Z] [TopologicalSpace Z'] {ι : C(Z', Z)}
  {𝒢 : Set (Set Z)}

theorem b65t_spread (hG : b65t_GoodFamily ι 𝒢) {W : Set Z} {a : Z'} {U : Set Z} (hU : U ∈ 𝒢)
    (hUW : U ⊆ W) {w : Z'} (hw : ι w ∈ U) (hreach : ∃ p : Path a w, ∀ t, ι (p t) ∈ W)
    (w' : Z') (hw' : ι w' ∈ U) : ∃ p : Path a w', ∀ t, ι (p t) ∈ W := by
  obtain ⟨p, hp⟩ := hreach
  obtain ⟨q, hq⟩ := hG.joined' U hU w w' hw hw'
  refine ⟨p.trans q, fun t ↦ ?_⟩
  rw [Path.trans_apply]; split_ifs
  · exact hp _
  · exact hUW (hq _)

/-- Two points of `Z'` joined by a path of `Z` inside an open set `W` are joined by a path of
`Z'` whose image lies in `W`. -/
theorem b65t_joined_in_open (hG : b65t_GoodFamily ι 𝒢) {W : Set Z} (hW : IsOpen W) {a b : Z'}
    (γ : Path (ι a) (ι b)) (hγ : ∀ t, γ t ∈ W) : ∃ p : Path a b, ∀ t, ι (p t) ∈ W := by
  set R : Set Z := {z | ∃ U ∈ 𝒢, z ∈ U ∧ U ⊆ W ∧
    ∀ w : Z', ι w ∈ U → ∃ p : Path a w, ∀ t, ι (p t) ∈ W}
  have hRopen : IsOpen R := by
    rw [isOpen_iff_forall_mem_open]
    rintro z ⟨U, hU, hz, hUW, hall⟩
    exact ⟨U, fun z' hz' ↦ ⟨U, hU, hz', hUW, hall⟩, hG.isOpen U hU, hz⟩
  have hcl : ∀ z ∈ W, z ∉ R → ∃ U ∈ 𝒢, z ∈ U ∧ ∀ z' ∈ U, z' ∉ R := by
    intro z hzW hzR
    obtain ⟨U, hU, hz, hUW⟩ := hG.basis z W hW hzW
    refine ⟨U, hU, hz, fun z' hz' hz'R ↦ hzR ?_⟩
    obtain ⟨U', hU', hz'', -, hall⟩ := hz'R
    obtain ⟨V, hV, hzV, hVsub⟩ := hG.basis z' (U ∩ U')
      ((hG.isOpen U hU).inter (hG.isOpen U' hU')) ⟨hz', hz''⟩
    obtain ⟨w, hw⟩ := hG.meets V hV z' hzV
    exact ⟨U, hU, hz, hUW, b65t_spread hG hU hUW (hVsub hw).1 (hall w (hVsub hw).2)⟩
  have hclopen : IsClopen (γ ⁻¹' R) := by
    refine ⟨?_, hRopen.preimage γ.continuous⟩
    rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
    intro t ht
    obtain ⟨U, hU, hz, hU'⟩ := hcl (γ t) (hγ t) ht
    exact ⟨γ ⁻¹' U, fun s hs ↦ hU' _ hs, (hG.isOpen U hU).preimage γ.continuous, hz⟩
  have h0 : (0 : I) ∈ γ ⁻¹' R := by
    obtain ⟨U, hU, hz, hUW⟩ := hG.basis (γ 0) W hW (hγ 0)
    rw [γ.source] at hz
    refine ⟨U, hU, by show γ 0 ∈ U; rw [γ.source]; exact hz, hUW,
      b65t_spread hG hU hUW hz ⟨Path.refl a, fun _ ↦ hUW hz⟩⟩
  have h1 : (1 : I) ∈ γ ⁻¹' R := by
    rw [hclopen.eq_univ ⟨0, h0⟩]; trivial
  obtain ⟨U, -, hz, -, hall⟩ := h1
  rw [γ.target] at hz
  exact hall b hz

/-- Every path of `Z` between points of `Z'` is homotopic to the image of a path of `Z'`. -/
theorem b65t_lift_path (hG : b65t_GoodFamily ι 𝒢) {a b : Z'} (γ : Path (ι a) (ι b)) :
    ∃ β : Path a b, (β.map ι.continuous).Homotopic γ := by
  let T : Set I := {t | ∃ U ∈ 𝒢, γ t ∈ U ∧ ∀ (w : Z') (κ : Path (γ t) (ι w)), (∀ s, κ s ∈ U) →
    ∃ β : Path a w, (β.map ι.continuous).Homotopic ((b65t_init γ t).trans κ)}
  have step : ∀ s t : I, s ∈ T → ∀ U ∈ 𝒢, (∀ r : I, (r : ℝ) ∈ uIcc (s : ℝ) t → γ r ∈ U) →
      t ∈ T := by
    rintro s t ⟨Us, hUs, hsUs, hPs⟩ U hU hseg
    have hsU : γ s ∈ U := hseg s left_mem_uIcc
    obtain ⟨V, hV, hsV, hVsub⟩ := hG.basis (γ s) (Us ∩ U)
      ((hG.isOpen _ hUs).inter (hG.isOpen _ hU)) ⟨hsUs, hsU⟩
    obtain ⟨w₀, hw₀⟩ := hG.meets V hV _ hsV
    obtain ⟨κ₀, hκ₀⟩ := hG.joined V hV _ hsV _ hw₀
    obtain ⟨β₀, hβ₀⟩ := hPs w₀ κ₀ (fun r ↦ (hVsub (hκ₀ r)).1)
    refine ⟨U, hU, hseg t right_mem_uIcc, fun w κ hκ ↦ ?_⟩
    obtain ⟨π, hπ⟩ := hG.joined' U hU w₀ w (hVsub hw₀).2 (by simpa using hκ 1)
    refine ⟨β₀.trans π, ?_⟩
    have hloc : (π.map ι.continuous).Homotopic ((κ₀.symm.trans (b65t_seg γ s t)).trans κ) :=
      hG.homotopic U hU _ _ (fun r ↦ hπ r)
        (b65t_trans_mem (b65t_trans_mem (b65t_symm_mem fun r ↦ (hVsub (hκ₀ r)).2)
          (fun r ↦ hseg _ (b65t_Ipath_mem s t r))) hκ)
    have hinit := b65t_init_trans_seg γ s t
    rw [← Path.Homotopic.Quotient.eq] at hloc hinit hβ₀ ⊢
    rw [Path.map_trans, Path.Homotopic.Quotient.mk_trans, hβ₀, hloc]
    simp only [Path.Homotopic.Quotient.mk_trans, Path.Homotopic.Quotient.mk_symm] at hinit ⊢
    rw [← hinit]
    simp only [Path.Homotopic.Quotient.trans_assoc, b65t_q_cancel]
  have local_ : ∀ t : I, ∃ ε > 0, ∀ r : I, dist r t < ε → (t ∈ T ↔ r ∈ T) := by
    intro t
    obtain ⟨U, hU, ht, -⟩ := hG.basis (γ t) univ isOpen_univ trivial
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp ((hG.isOpen U hU).preimage γ.continuous) t ht
    refine ⟨ε, hε, fun r hr ↦ ⟨fun h ↦ step t r h U hU fun r' hr' ↦ hball ?_,
      fun h ↦ step r t h U hU fun r' hr' ↦ hball ?_⟩⟩
    · exact lt_of_le_of_lt (b65t_dist_of_mem_uIcc hr') hr
    · rw [uIcc_comm] at hr'
      exact lt_of_le_of_lt (b65t_dist_of_mem_uIcc hr') hr
  have hclopen : IsClopen T := by
    constructor
    · rw [← isOpen_compl_iff, Metric.isOpen_iff]
      intro t ht
      obtain ⟨ε, hε, h⟩ := local_ t
      exact ⟨ε, hε, fun r hr hrT ↦ ht ((h r hr).mpr hrT)⟩
    · rw [Metric.isOpen_iff]
      intro t ht
      obtain ⟨ε, hε, h⟩ := local_ t
      exact ⟨ε, hε, fun r hr ↦ (h r hr).mp ht⟩
  have h0 : (0 : I) ∈ T := by
    obtain ⟨U, hU, h0U, -⟩ := hG.basis (γ 0) univ isOpen_univ trivial
    refine ⟨U, hU, h0U, fun w κ hκ ↦ ?_⟩
    obtain ⟨β, hβ⟩ := hG.joined' U hU a w (by rw [← γ.source]; exact h0U)
      (by simpa using hκ 1)
    exact ⟨β, hG.homotopic U hU _ _ hβ (b65t_trans_mem (fun r ↦ by
      rw [b65t_init_apply, show b65t_Ipath 0 0 r = 0 from by ext; simp [b65t_Ipath]]
      exact h0U) hκ)⟩
  have h1 : (1 : I) ∈ T := by
    rw [hclopen.eq_univ ⟨0, h0⟩]; trivial
  obtain ⟨U, -, h1U, hP⟩ := h1
  obtain ⟨β, hβ⟩ := hP b ((Path.refl (γ 1)).cast rfl γ.target.symm) (fun _ ↦ h1U)
  refine ⟨β, hβ.trans ?_⟩
  exact b65t_homotopic_of_factor ⟨γ, γ.continuous⟩ ((b65t_Ipath 0 1).trans (Path.refl 1))
    ⟨⟨id, continuous_id⟩, rfl, rfl⟩ _ _
    (b65t_trans_factor ⟨γ, γ.continuous⟩ _ _ _ _ (fun _ ↦ rfl) (fun _ ↦ rfl)) (fun _ ↦ rfl)

/-- Surjectivity of `ι` on fundamental groups. -/
theorem b65t_map_surjective (hG : b65t_GoodFamily ι 𝒢) (x : Z') :
    Function.Surjective (FundamentalGroup.map ι x) := by
  intro g
  obtain ⟨γ, hγ⟩ := Quotient.exists_rep g.asHom
  obtain ⟨β, hβ⟩ := b65t_lift_path hG γ
  refine ⟨FundamentalGroup.fromPath ⟦β⟧, ?_⟩
  have hg : g = FundamentalGroup.fromPath ⟦γ⟧ := by
    rw [show (⟦γ⟧ : Path.Homotopic.Quotient (ι x) (ι x)) = g.asHom from hγ]
  rw [hg]
  change FundamentalGroup.fromPath ⟦β.map ι.continuous⟧ = _
  rw [Quotient.sound hβ]

end Abstract

section Kernel

open CategoryTheory

variable {Z Z' : Type*} [TopologicalSpace Z] [TopologicalSpace Z'] {ι : C(Z', Z)}
  {𝒢 : Set (Set Z)} {x : Z'} (N : Subgroup (FundamentalGroup Z' x)) [N.Normal]

/-- Every loop of `Z'` inside a good set, brought to the base point along a path, lies in `N`. -/
def b65t_LocalN (ι : C(Z', Z)) (𝒢 : Set (Set Z)) : Prop :=
  ∀ U ∈ 𝒢, ∀ (a : Z') (δ : Path x a) (ℓ : Path a a), (∀ t, ι (ℓ t) ∈ U) →
    FundamentalGroup.fromPath ⟦(δ.trans ℓ).trans δ.symm⟧ ∈ N

omit [N.Normal] in
theorem b65t_inv_asHom (f : FundamentalGroup Z' x) : f⁻¹.asHom = Groupoid.inv f.asHom := rfl

theorem b65t_Phi_eq_of_mem (hN : b65t_LocalN N ι 𝒢) {U : Set Z} (hU : U ∈ 𝒢) {a b : Z'}
    (p q : Path a b) (hp : ∀ t, ι (p t) ∈ U) (hq : ∀ t, ι (q t) ∈ U) :
    b65t_Phi N p = b65t_Phi N q := by
  by_cases h : Joined x a
  · simp only [b65t_Phi, h, ↓reduceDIte, inv_inj]
    rw [QuotientGroup.eq]
    have hm := hN U hU a h.somePath (q.trans p.symm)
      (fun t ↦ by rw [Path.trans_apply]; split_ifs <;> simp [hp, hq])
    convert hm using 1
    ext
    simp only [End.mul_asHom, b65t_inv_asHom]
    change _ = b65t_arr ((h.somePath.trans (q.trans p.symm)).trans h.somePath.symm)
    simp only [b65t_arr_trans, b65t_arr_symm, Groupoid.inv_eq_inv, IsIso.inv_comp, IsIso.inv_inv,
      Category.assoc, IsIso.inv_hom_id_assoc, b65t_tau]
  · simp only [b65t_Phi, h, ↓reduceDIte]

theorem b65t_Phi_eq_of_mem' (hN : b65t_LocalN N ι 𝒢) {U : Set Z} (hU : U ∈ 𝒢) {a b a' b' : Z'}
    (ha : a = a') (hb : b = b') (p : Path a b) (q : Path a' b') (hp : ∀ t, ι (p t) ∈ U)
    (hq : ∀ t, ι (q t) ∈ U) : b65t_Phi N p = b65t_Phi N q := by
  subst ha hb; exact b65t_Phi_eq_of_mem N hN hU p q hp hq

theorem b65t_Phi_loop (hN : b65t_LocalN N ι 𝒢) {U : Set Z} (hU : U ∈ 𝒢) {a b : Z'}
    (hab : b = a) (p : Path a b) (hp : ∀ t, ι (p t) ∈ U) : b65t_Phi N p = 1 := by
  subst hab
  rw [b65t_Phi_eq_of_mem N hN hU p (Path.refl _) hp (fun _ ↦ by simpa using hp 0),
    b65t_Phi_refl]

theorem b65t_mem_of_Phi (γ : Path x x) (hγ : b65t_Phi N γ = 1) :
    FundamentalGroup.fromPath ⟦γ⟧ ∈ N := by
  have h : Joined x x := Joined.refl x
  simp only [b65t_Phi, h, ↓reduceDIte, inv_eq_one, QuotientGroup.eq_one_iff] at hγ
  set c : FundamentalGroup Z' x := End.of (b65t_tau h)
  have e : (End.of (b65t_tau h ≫ b65t_arr γ ≫ Groupoid.inv (b65t_tau (h.trans ⟨γ⟩))) :
      FundamentalGroup Z' x) = c⁻¹ * FundamentalGroup.fromPath ⟦γ⟧ * c := by
    ext
    simp only [End.mul_asHom, c]
    rfl
  rw [e] at hγ
  have := (inferInstance : N.Normal).conj_mem _ hγ c
  simpa [mul_assoc] using this


/-- A loop of `Z'` whose image is null-homotopic in `Z` lies in `N`: the grid argument. -/
theorem b65t_kernel_mem (hG : b65t_GoodFamily ι 𝒢) (hN : b65t_LocalN N ι 𝒢) (γ : Path x x)
    (hnull : (γ.map ι.continuous).Homotopic (Path.refl (ι x))) :
    FundamentalGroup.fromPath ⟦γ⟧ ∈ N := by
  obtain ⟨H⟩ := hnull
  have hcov : (univ : Set (I × I)) ⊆ ⋃ U : 𝒢, H ⁻¹' (U : Set Z) := fun p _ ↦ by
    obtain ⟨U, hU, hp, -⟩ := hG.basis (H p) univ isOpen_univ trivial
    exact mem_iUnion.mpr ⟨⟨U, hU⟩, hp⟩
  obtain ⟨δ, hδ, hleb⟩ := lebesgue_number_lemma_of_metric isCompact_univ
    (fun U : 𝒢 ↦ (hG.isOpen U U.2).preimage H.continuous) hcov
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hδ
  set m : ℕ := n + 1 with hm
  have hm0 : (0 : ℝ) < m := by positivity
  have hmδ : 1 / (m : ℝ) < δ := by simpa [hm] using hn
  let g : ℕ → I := fun k ↦ Set.projIcc 0 1 zero_le_one (k / m)
  have hg0 : g 0 = 0 := by ext; simp [g]
  have hgm : g m = 1 := by ext; simp [g, hm0.ne']
  have hgs : ∀ k, dist (g (k + 1)) (g k) ≤ 1 / m := by
    intro k
    rw [Subtype.dist_eq, Real.dist_eq]
    refine (Set.abs_projIcc_sub_projIcc _).trans (le_of_eq ?_)
    rw [show ((k + 1 : ℕ) : ℝ) / m - (k : ℝ) / m = 1 / m by push_cast; ring]
    exact abs_of_pos (by positivity)
  have hgp : ∀ k, dist (g k) (g (k - 1)) ≤ 1 / m := by
    intro k
    cases k with
    | zero => simp only [zero_tsub, dist_self]; positivity
    | succ k => simpa using hgs k
  have hself : ∀ k, dist (g k) (g k) ≤ 1 / m := fun k ↦ by rw [dist_self]; positivity
  have hIp : ∀ k (r : I), (r : ℝ) ∈ uIcc (g k : ℝ) (g (k + 1)) → dist r (g k) ≤ 1 / m :=
    fun k r hr ↦ (b65t_dist_of_mem_uIcc hr).trans (hgs k)
  have hUex : ∀ i j : ℕ, ∃ U ∈ 𝒢, ∀ p : I × I, dist p.1 (g i) ≤ 1 / m →
      dist p.2 (g j) ≤ 1 / m → H p ∈ U := by
    intro i j
    obtain ⟨⟨U, hU⟩, hball⟩ := hleb (g i, g j) trivial
    refine ⟨U, hU, fun p h1 h2 ↦ hball ?_⟩
    rw [mem_ball, Prod.dist_eq]
    exact lt_of_le_of_lt (max_le h1 h2) hmδ
  choose U hU𝒢 hUmem using hUex
  let A : ℕ → ℕ → Set Z := fun i j ↦ U (i - 1) (j - 1) ∩ U (i - 1) j ∩ U i (j - 1) ∩ U i j
  have hAopen : ∀ i j, IsOpen (A i j) := fun i j ↦
    (((hG.isOpen _ (hU𝒢 _ _)).inter (hG.isOpen _ (hU𝒢 _ _))).inter
      (hG.isOpen _ (hU𝒢 _ _))).inter (hG.isOpen _ (hU𝒢 _ _))
  have hvA : ∀ i j, H (g i, g j) ∈ A i j := fun i j ↦
    ⟨⟨⟨hUmem _ _ (g i, g j) (hgp i) (hgp j), hUmem _ _ (g i, g j) (hgp i) (hself j)⟩,
      hUmem _ _ (g i, g j) (hself i) (hgp j)⟩, hUmem _ _ (g i, g j) (hself i) (hself j)⟩
  have hH0 : ∀ t, H (0, t) = ι (γ t) := fun t ↦ H.apply_zero t
  have hvtx : ∀ i j : ℕ, ∃ w : Z', ∃ κ : Path (H (g i, g j)) (ι w), (∀ s, κ s ∈ A i j) ∧
      (i = 0 → w = γ (g j)) ∧ (i ≠ 0 → (i = m ∨ j = 0 ∨ j = m) → w = x) := by
    intro i j
    by_cases hi : i = 0
    · refine ⟨γ (g j), (Path.refl _).cast rfl ?_, fun _ ↦ hvA i j, fun _ ↦ rfl,
        fun h ↦ absurd hi h⟩
      rw [hi, hg0, hH0]
    · by_cases hb : i = m ∨ j = 0 ∨ j = m
      · refine ⟨x, (Path.refl _).cast rfl ?_, fun _ ↦ hvA i j, fun h ↦ absurd h hi,
          fun _ _ ↦ rfl⟩
        rcases hb with h | h | h
        · rw [h, hgm]; exact (H.apply_one (g j)).symm
        · rw [h, hg0]; exact (H.source (g i)).symm
        · rw [h, hgm]; exact (H.target (g i)).symm
      · obtain ⟨V, hV, hvV, hVA⟩ := hG.basis _ (A i j) (hAopen i j) (hvA i j)
        obtain ⟨w, hw⟩ := hG.meets V hV _ hvV
        obtain ⟨κ, hκ⟩ := hG.joined V hV _ hvV _ hw
        exact ⟨w, κ, fun s ↦ hVA (hκ s), fun h ↦ absurd h hi, fun _ h ↦ absurd h hb⟩
  choose w κ hκ hw0 hwx using hvtx
  let tpath : ∀ i j, Path (H (g i, g j)) (H (g i, g (j + 1))) := fun i j ↦
    (b65t_Ipath (g j) (g (j + 1))).map (f := fun t ↦ H (g i, t)) (by fun_prop)
  let spath : ∀ i j, Path (H (g i, g j)) (H (g (i + 1), g j)) := fun i j ↦
    (b65t_Ipath (g i) (g (i + 1))).map (f := fun s ↦ H (s, g j)) (by fun_prop)
  have ht : ∀ i j, ∃ π : Path (w i j) (w i (j + 1)), ∀ t, ι (π t) ∈ U (i - 1) j ∩ U i j := by
    intro i j
    refine b65t_joined_in_open hG ((hG.isOpen _ (hU𝒢 _ _)).inter (hG.isOpen _ (hU𝒢 _ _)))
      ((κ i j).symm.trans ((tpath i j).trans (κ i (j + 1)))) ?_
    refine b65t_trans_mem (b65t_symm_mem fun s ↦ ?_) (b65t_trans_mem (fun s ↦ ?_) fun s ↦ ?_)
    · have h := hκ i j s
      exact ⟨h.1.1.2, h.2⟩
    · exact ⟨hUmem _ _ _ (hgp i) (hIp j _ (b65t_Ipath_mem _ _ s)),
        hUmem _ _ _ (hself i) (hIp j _ (b65t_Ipath_mem _ _ s))⟩
    · have h := hκ i (j + 1) s
      simp only [A, Nat.add_sub_cancel] at h
      exact ⟨h.1.1.1, h.1.2⟩
  have hs : ∀ i j, ∃ π : Path (w i j) (w (i + 1) j), ∀ t, ι (π t) ∈ U i (j - 1) ∩ U i j := by
    intro i j
    refine b65t_joined_in_open hG ((hG.isOpen _ (hU𝒢 _ _)).inter (hG.isOpen _ (hU𝒢 _ _)))
      ((κ i j).symm.trans ((spath i j).trans (κ (i + 1) j))) ?_
    refine b65t_trans_mem (b65t_symm_mem fun s ↦ ?_) (b65t_trans_mem (fun s ↦ ?_) fun s ↦ ?_)
    · have h := hκ i j s
      exact ⟨h.1.2, h.2⟩
    · exact ⟨hUmem _ _ (_, g j) (hIp i _ (b65t_Ipath_mem _ _ s)) (hgp j),
        hUmem _ _ (_, g j) (hIp i _ (b65t_Ipath_mem _ _ s)) (hself j)⟩
    · have h := hκ (i + 1) j s
      simp only [A, Nat.add_sub_cancel] at h
      exact ⟨h.1.1.1, h.1.1.2⟩
  choose πt hπt using ht
  choose πs hπs using hs
  have hcell : ∀ i j, b65t_Phi N (πs i j) * b65t_Phi N (πt (i + 1) j) =
      b65t_Phi N (πt i j) * b65t_Phi N (πs i (j + 1)) := by
    intro i j
    rw [← b65t_Phi_trans, ← b65t_Phi_trans]
    refine b65t_Phi_eq_of_mem N hN (hU𝒢 i j) _ _
      (b65t_trans_mem_map ι (fun t ↦ (hπs i j t).2) (fun t ↦ ?_))
      (b65t_trans_mem_map ι (fun t ↦ (hπt i j t).2) (fun t ↦ ?_))
    · simpa using (hπt (i + 1) j t).1
    · simpa using (hπs i (j + 1) t).1
  have hgrid := b65t_grid_prod m m (fun i j ↦ b65t_Phi N (πs i j))
    (fun i j ↦ b65t_Phi N (πt i j)) (fun i _ j _ ↦ hcell i j)
  have hw_i0 : ∀ i, w i 0 = x := by
    intro i
    by_cases hi : i = 0
    · rw [hw0 i 0 hi, hg0, γ.source]
    · exact hwx i 0 hi (Or.inr (Or.inl rfl))
  have hw_im : ∀ i, w i m = x := by
    intro i
    by_cases hi : i = 0
    · rw [hw0 i m hi, hgm, γ.target]
    · exact hwx i m hi (Or.inr (Or.inr rfl))
  have hw_mj : ∀ j, w m j = x := fun j ↦ hwx m j (by omega) (Or.inl rfl)
  have e1 : ((List.range m).map (fun i ↦ b65t_Phi N (πs i 0))).prod = 1 :=
    List.prod_eq_one (by
      simp only [List.mem_map]
      rintro _ ⟨i, -, rfl⟩
      exact b65t_Phi_loop N hN (hU𝒢 i 0) (by rw [hw_i0, hw_i0]) _ (fun t ↦ (hπs i 0 t).2))
  have e2 : ((List.range m).map (fun i ↦ b65t_Phi N (πs i m))).prod = 1 :=
    List.prod_eq_one (by
      simp only [List.mem_map]
      rintro _ ⟨i, -, rfl⟩
      exact b65t_Phi_loop N hN (hU𝒢 i m) (by rw [hw_im, hw_im]) _ (fun t ↦ (hπs i m t).2))
  have e3 : ((List.range m).map (fun j ↦ b65t_Phi N (πt m j))).prod = 1 :=
    List.prod_eq_one (by
      simp only [List.mem_map]
      rintro _ ⟨j, -, rfl⟩
      exact b65t_Phi_loop N hN (hU𝒢 m j) (by rw [hw_mj, hw_mj]) _ (fun t ↦ (hπt m j t).2))
  have hB0 : ∀ j, b65t_Phi N (πt 0 j) = b65t_Phi N (b65t_seg γ (g j) (g (j + 1))) := by
    intro j
    refine b65t_Phi_eq_of_mem' N hN (hU𝒢 0 j) (hw0 0 j rfl) (hw0 0 (j + 1) rfl) _ _
      (fun t ↦ (hπt 0 j t).2) (fun t ↦ ?_)
    have h := hUmem 0 j (g 0, b65t_Ipath _ _ t) (hself 0) (hIp j _ (b65t_Ipath_mem _ _ t))
    rwa [hg0, hH0] at h
  have hzero : ∀ t : I, t = 0 → b65t_Phi N (b65t_init γ t) = 1 := by
    rintro t rfl
    rw [b65t_Phi_homotopic N (b65t_init_zero γ), b65t_Phi_cast, b65t_Phi_refl]
  have hone : ∀ t : I, t = 1 → b65t_Phi N (b65t_init γ t) = b65t_Phi N γ := by
    rintro t rfl
    rw [b65t_Phi_homotopic N (b65t_init_one γ), b65t_Phi_cast]
  have hprod : ∀ k, ((List.range k).map
      (fun j ↦ b65t_Phi N (b65t_seg γ (g j) (g (j + 1))))).prod = b65t_Phi N (b65t_init γ (g k)) := by
    intro k
    induction k with
    | zero => rw [hzero _ hg0]; simp
    | succ k ih =>
      rw [List.range_succ, List.map_append, List.prod_append, ih, List.map_singleton,
        List.prod_singleton, ← b65t_Phi_trans, b65t_Phi_homotopic N (b65t_init_trans_seg γ _ _)]
  have e4 : ((List.range m).map (fun j ↦ b65t_Phi N (πt 0 j))).prod = b65t_Phi N γ := by
    rw [List.map_congr_left (fun j _ ↦ hB0 j), hprod, hone _ hgm]
  rw [e1, e2, e3, e4, mul_one, mul_one] at hgrid
  exact b65t_mem_of_Phi N γ hgrid.symm

end Kernel


end Main

section Sphere

open CategoryTheory

/-- The inversion `z ↦ 1/z` of the sphere, exchanging `0` and `∞`. -/
def b65t_invFun (p : OnePoint ℂ) : OnePoint ℂ :=
  p.elim ((0 : ℂ) : OnePoint ℂ)
    (fun z ↦ if z = 0 then OnePoint.infty else ((z⁻¹ : ℂ) : OnePoint ℂ))

@[simp] theorem b65t_invFun_infty : b65t_invFun OnePoint.infty = ((0 : ℂ) : OnePoint ℂ) := rfl

@[simp] theorem b65t_invFun_zero : b65t_invFun ((0 : ℂ) : OnePoint ℂ) = OnePoint.infty := by
  simp [b65t_invFun]

theorem b65t_invFun_coe {z : ℂ} (hz : z ≠ 0) :
    b65t_invFun (z : OnePoint ℂ) = ((z⁻¹ : ℂ) : OnePoint ℂ) := by
  simp [b65t_invFun, hz]

theorem b65t_invFun_invol : Function.Involutive b65t_invFun := by
  intro p
  induction p using OnePoint.rec with
  | infty => simp
  | coe z =>
    by_cases hz : z = 0
    · subst hz; simp
    · rw [b65t_invFun_coe hz, b65t_invFun_coe (inv_ne_zero hz), inv_inv]

theorem b65t_coclosed : Filter.coclosedCompact ℂ = Bornology.cobounded ℂ := by
  rw [Filter.coclosedCompact_eq_cocompact, Metric.cobounded_eq_cocompact]

theorem b65t_invFun_continuous : Continuous b65t_invFun := by
  rw [OnePoint.continuous_iff]
  refine ⟨?_, ?_⟩
  · rw [b65t_coclosed, b65t_invFun_infty]
    have hne : ∀ᶠ z : ℂ in Bornology.cobounded ℂ, z ≠ 0 :=
      (tendsto_inv₀_cobounded'.eventually self_mem_nhdsWithin).mono fun z hz ↦ by
        simpa using hz
    exact ((OnePoint.continuous_coe.tendsto 0).comp tendsto_inv₀_cobounded).congr'
      (hne.mono fun z hz ↦ (b65t_invFun_coe hz).symm)
  · rw [continuous_iff_continuousAt]
    intro z
    by_cases hz : z = 0
    · subst hz
      show Tendsto _ (𝓝 0) (𝓝 (b65t_invFun ((0 : ℂ) : OnePoint ℂ)))
      rw [b65t_invFun_zero, ← nhdsNE_sup_pure (0 : ℂ)]
      refine Tendsto.sup ?_ ?_
      · have hev : ∀ᶠ w in 𝓝[≠] (0 : ℂ),
            ((w⁻¹ : ℂ) : OnePoint ℂ) = b65t_invFun (w : OnePoint ℂ) :=
          eventually_nhdsWithin_of_forall fun w hw ↦ (b65t_invFun_coe hw).symm
        refine Tendsto.congr' hev ?_
        have h := OnePoint.tendsto_coe_infty (X := ℂ)
        rw [b65t_coclosed] at h
        exact h.comp tendsto_inv₀_nhdsNE_zero
      · rw [tendsto_pure_left]
        intro s hs
        simpa using mem_of_mem_nhds hs
    · have hev : (fun w : ℂ ↦ ((w⁻¹ : ℂ) : OnePoint ℂ)) =ᶠ[𝓝 z]
          fun w : ℂ ↦ b65t_invFun (w : OnePoint ℂ) := by
        filter_upwards [isOpen_ne.mem_nhds hz] with w hw using (b65t_invFun_coe hw).symm
      exact (OnePoint.continuous_coe.continuousAt.comp (continuousAt_inv₀ hz)).congr hev

/-- The inversion of the sphere as a homeomorphism. -/
def b65t_inv : OnePoint ℂ ≃ₜ OnePoint ℂ where
  toEquiv := b65t_invFun_invol.toPerm _
  continuous_toFun := b65t_invFun_continuous
  continuous_invFun := b65t_invFun_continuous

theorem b65t_inv_apply (p : OnePoint ℂ) : b65t_inv p = b65t_invFun p := rfl

theorem b65t_disc_coe (a : ℂ) (r : ℝ) :
    b65t_disc (a : OnePoint ℂ) r = ((↑) : ℂ → OnePoint ℂ) '' ball a r := rfl

theorem b65t_disc_infty_eq {r : ℝ} (hr : 0 < r) :
    b65t_disc OnePoint.infty r = b65t_inv '' b65t_disc ((0 : ℂ) : OnePoint ℂ) r := by
  ext p
  induction p using OnePoint.rec with
  | infty =>
    simp only [b65t_disc, OnePoint.elim_infty, mem_insert_iff, true_or, true_iff]
    exact ⟨((0 : ℂ) : OnePoint ℂ), ⟨0, mem_ball_self hr, rfl⟩, by simp [b65t_inv_apply]⟩
  | coe z =>
    simp only [b65t_disc, OnePoint.elim_infty, mem_insert_iff, OnePoint.coe_ne_infty, false_or,
      mem_image, OnePoint.coe_eq_coe, exists_eq_right, mem_ofPred_eq, OnePoint.elim_some]
    constructor
    · intro hz
      have hz0 : z ≠ 0 := by
        rintro rfl; simp at hz; linarith [inv_pos.mpr hr]
      refine ⟨((z⁻¹ : ℂ) : OnePoint ℂ), ⟨z⁻¹, ?_, rfl⟩, ?_⟩
      · rw [mem_ball_zero_iff, norm_inv]
        exact (inv_lt_comm₀ (norm_pos_iff.mpr hz0) hr).mpr hz
      · rw [b65t_inv_apply, b65t_invFun_coe (inv_ne_zero hz0), inv_inv]
    · rintro ⟨_, ⟨w, hw, rfl⟩, he⟩
      rw [b65t_inv_apply] at he
      by_cases hw0 : w = 0
      · subst hw0; simp at he
      · rw [b65t_invFun_coe hw0, OnePoint.coe_eq_coe] at he
        subst he
        rw [mem_ball_zero_iff] at hw
        rw [norm_inv]
        exact inv_lt_inv₀ hr (norm_pos_iff.mpr hw0) |>.mpr hw

theorem b65t_disc_coe_props (a : ℂ) {r : ℝ} (hr : 0 < r) :
    IsOpen (b65t_disc (a : OnePoint ℂ) r) ∧ (a : OnePoint ℂ) ∈ b65t_disc (a : OnePoint ℂ) r ∧
      Nonempty (ℂ ≃ₜ ↥(b65t_disc (a : OnePoint ℂ) r)) := by
  rw [b65t_disc_coe]
  refine ⟨OnePoint.isOpenEmbedding_coe.isOpenMap _ isOpen_ball, ⟨a, mem_ball_self hr, rfl⟩, ?_⟩
  let u := OpenPartialHomeomorph.univBall (E := ℂ) a r
  exact ⟨(Homeomorph.Set.univ ℂ).symm.trans
    ((Homeomorph.setCongr (OpenPartialHomeomorph.univBall_source (E := ℂ) a r).symm).trans
      (u.toHomeomorphSourceTarget.trans
        ((Homeomorph.setCongr (OpenPartialHomeomorph.univBall_target (E := ℂ) a hr)).trans
          (OnePoint.isOpenEmbedding_coe.isEmbedding.homeomorphImage (ball a r)))))⟩

theorem b65t_disc_props (p : OnePoint ℂ) {r : ℝ} (hr : 0 < r) :
    IsOpen (b65t_disc p r) ∧ p ∈ b65t_disc p r ∧ Nonempty (ℂ ≃ₜ ↥(b65t_disc p r)) := by
  induction p using OnePoint.rec with
  | infty =>
    obtain ⟨ho, hm, ⟨h⟩⟩ := b65t_disc_coe_props 0 hr
    rw [b65t_disc_infty_eq hr]
    refine ⟨b65t_inv.isOpenMap _ ho, ⟨_, hm, by simp [b65t_inv_apply]⟩,
      ⟨h.trans (b65t_inv.image _)⟩⟩
  | coe a => exact b65t_disc_coe_props a hr

theorem b65t_disc_basis (p : OnePoint ℂ) {O : Set (OnePoint ℂ)} (hO : IsOpen O) (hp : p ∈ O) :
    ∃ r > 0, b65t_disc p r ⊆ O := by
  have coe_case : ∀ (a : ℂ) (O : Set (OnePoint ℂ)), IsOpen O → (a : OnePoint ℂ) ∈ O →
      ∃ r > 0, b65t_disc (a : OnePoint ℂ) r ⊆ O := by
    intro a O hO ha
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp (hO.preimage OnePoint.continuous_coe) a ha
    exact ⟨r, hr, by rw [b65t_disc_coe]; rintro _ ⟨z, hz, rfl⟩; exact hball hz⟩
  induction p using OnePoint.rec with
  | infty =>
    obtain ⟨r, hr, hsub⟩ := coe_case 0 (b65t_inv ⁻¹' O) (hO.preimage b65t_inv.continuous)
      (by simpa [b65t_inv_apply] using hp)
    exact ⟨r, hr, by rw [b65t_disc_infty_eq hr]; rintro _ ⟨q, hq, rfl⟩; exact hsub hq⟩
  | coe a => exact coe_case a O hO hp

/-- A set homeomorphic to `ℂ`, minus a finite set, is path-connected. -/
theorem b65t_pathConnected_diff {S : Type*} [TopologicalSpace S] {D : Set S} (h : ℂ ≃ₜ ↥D)
    {F : Set S} (hF : F.Finite) : IsPathConnected (D \ F) := by
  have hinj : Function.Injective (fun z ↦ ((h z : ↥D) : S)) :=
    Subtype.val_injective.comp h.injective
  have hc : ((fun z ↦ ((h z : ↥D) : S)) ⁻¹' F).Countable := (hF.preimage hinj.injOn).countable
  have hpc := hc.isPathConnected_compl_of_one_lt_rank
    (by rw [Complex.rank_real_complex]; norm_num)
  have himg : (fun z ↦ ((h z : ↥D) : S)) '' ((fun z ↦ ((h z : ↥D) : S)) ⁻¹' F)ᶜ = D \ F := by
    ext q
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨(h z).2, hz⟩
    · rintro ⟨hqD, hqF⟩
      refine ⟨h.symm ⟨q, hqD⟩, ?_, ?_⟩ <;> simp [hqF]
  rw [← himg]
  exact hpc.image (continuous_subtype_val.comp h.continuous)

/-- Two paths of a space `T ⊇ D` inside a set `D` homeomorphic to `ℂ` are homotopic. -/
theorem b65t_homotopic_in {S : Type*} [TopologicalSpace S] {D T : Set S} (h : ℂ ≃ₜ ↥D)
    (hDT : D ⊆ T) {a b : ↥T} (p q : Path a b) (hp : ∀ t, (p t : S) ∈ D)
    (hq : ∀ t, (q t : S) ∈ D) : p.Homotopic q := by
  have ha : (a : S) ∈ D := by simpa using hp 0
  have hb : (b : S) ∈ D := by simpa using hp 1
  let f : C(ℂ, ↥T) := ⟨fun z ↦ ⟨(h z : S), hDT (h z).2⟩, by fun_prop⟩
  let chart : ∀ p : Path a b, (∀ t, (p t : S) ∈ D) → Path (h.symm ⟨a, ha⟩) (h.symm ⟨b, hb⟩) :=
    fun p hp ↦ ⟨⟨fun t ↦ h.symm ⟨p t, hp t⟩, by fun_prop⟩, by simp, by simp⟩
  refine b65t_homotopic_of_factor f (chart p hp) (chart q hq) p q (fun s ↦ ?_) (fun s ↦ ?_)
  · ext; simp [f, chart]
  · ext; simp [f, chart]

/-- A path inside `D ⊆ T` between points of `T`, as a path of `T`. -/
theorem b65t_path_in {S : Type*} [TopologicalSpace S] {D T : Set S} (hDT : D ⊆ T) {a b : ↥T}
    (hJ : JoinedIn D (a : S) (b : S)) : ∃ p : Path a b, ∀ t, (p t : S) ∈ D :=
  ⟨⟨⟨fun t ↦ ⟨hJ.somePath t, hDT (hJ.somePath_mem t)⟩, by fun_prop⟩,
    Subtype.ext (by simp), Subtype.ext (by simp)⟩, fun t ↦ hJ.somePath_mem t⟩

/-- The discs of `X` meeting `F` at most in their centre, as subsets of `X`. -/
def b65t_sphereGood (X : Set (OnePoint ℂ)) (F : Finset (OnePoint ℂ)) : Set (Set ↥X) :=
  {V | ∃ p r, 0 < r ∧ b65t_disc p r ⊆ X ∧ (∀ q ∈ F, q ∈ b65t_disc p r → q = p) ∧
    V = Subtype.val ⁻¹' b65t_disc p r}

theorem b65t_sphere_good (X : Set (OnePoint ℂ)) (hX : IsOpen X) (F : Finset (OnePoint ℂ)) :
    b65t_GoodFamily (b65t_fill X F) (b65t_sphereGood X F) where
  isOpen := by
    rintro V ⟨p, r, hr, -, -, rfl⟩
    exact (b65t_disc_props p hr).1.preimage continuous_subtype_val
  basis := by
    classical
    intro z W hW hz
    obtain ⟨O, hO, rfl⟩ := isOpen_induced_iff.mp hW
    have hO' : IsOpen (O ∩ X ∩ ((F.erase z.val : Finset (OnePoint ℂ)) : Set (OnePoint ℂ))ᶜ) :=
      (hO.inter hX).inter (Finset.finite_toSet _).isClosed.isOpen_compl
    obtain ⟨r, hr, hsub⟩ := b65t_disc_basis z.val hO' ⟨⟨hz, z.2⟩, by simp⟩
    refine ⟨Subtype.val ⁻¹' b65t_disc z.val r, ⟨z.val, r, hr, fun q hq ↦ (hsub hq).1.2,
      fun q hqF hq ↦ ?_, rfl⟩, (b65t_disc_props z.val hr).2.1, fun y hy ↦ (hsub hy).1.1⟩
    by_contra hne
    exact (hsub hq).2 (by simp [hqF, hne])
  joined := by
    rintro V ⟨p, r, hr, hDX, -, rfl⟩ a ha b hb
    obtain ⟨h⟩ := (b65t_disc_props p hr).2.2
    have hpc := b65t_pathConnected_diff h (finite_empty (α := OnePoint ℂ))
    rw [sdiff_empty] at hpc
    exact b65t_path_in hDX (hpc.joinedIn _ ha _ hb)
  meets := by
    rintro V ⟨p, r, hr, hDX, -, rfl⟩ z -
    obtain ⟨h⟩ := (b65t_disc_props p hr).2.2
    obtain ⟨w, hwD, hwF⟩ := (b65t_pathConnected_diff h (Finset.finite_toSet F)).nonempty
    exact ⟨⟨w, hDX hwD, hwF⟩, hwD⟩
  joined' := by
    rintro V ⟨p, r, hr, hDX, -, rfl⟩ a b ha hb
    obtain ⟨h⟩ := (b65t_disc_props p hr).2.2
    have hpc := b65t_pathConnected_diff h (Finset.finite_toSet F)
    obtain ⟨π, hπ⟩ := b65t_path_in (T := X \ (F : Set (OnePoint ℂ)))
      (fun q hq ↦ ⟨hDX hq.1, hq.2⟩) (hpc.joinedIn _ ⟨ha, a.2.2⟩ _ ⟨hb, b.2.2⟩)
    exact ⟨π, fun t ↦ (hπ t).1⟩
  homotopic := by
    rintro V ⟨p, r, hr, hDX, -, rfl⟩ a b π₁ π₂ h₁ h₂
    obtain ⟨h⟩ := (b65t_disc_props p hr).2.2
    exact b65t_homotopic_in h hDX π₁ π₂ h₁ h₂

theorem b65t_lasso_one {Y : Type*} [TopologicalSpace Y] {x a : Y} (δ : Path x a) (ℓ : Path a a)
    (h : ℓ.Homotopic (Path.refl a)) :
    FundamentalGroup.fromPath ⟦(δ.trans ℓ).trans δ.symm⟧ = 1 := by
  have hℓ : b65t_arr ℓ = b65t_arr (Path.refl a) := Quotient.sound h
  ext
  change b65t_arr ((δ.trans ℓ).trans δ.symm) = 𝟙 _
  rw [b65t_arr_trans, b65t_arr_trans, hℓ, b65t_arr_refl, Category.comp_id, b65t_arr_symm,
    Groupoid.comp_inv]

theorem b65t_sphere_localN (X : Set (OnePoint ℂ)) (F : Finset (OnePoint ℂ))
    (x : ↥(X \ (F : Set (OnePoint ℂ)))) :
    b65t_LocalN (Subgroup.normalClosure (b65t_peripheral X F x)) (b65t_fill X F)
      (b65t_sphereGood X F) := by
  rintro V ⟨p, r, hr, hDX, honly, rfl⟩ a δ ℓ hℓ
  by_cases hp : p ∈ F
  · exact Subgroup.subset_normalClosure ⟨p, hp, r, hr, hDX, honly, a, δ, ℓ, hℓ, rfl⟩
  · obtain ⟨h⟩ := (b65t_disc_props p hr).2.2
    have hDXF : b65t_disc p r ⊆ X \ (F : Set (OnePoint ℂ)) := fun q hq ↦
      ⟨hDX hq, fun hqF ↦ hp (by rwa [← honly q hqF hq])⟩
    have ha : ((b65t_fill X F a : ↥X) : OnePoint ℂ) ∈ b65t_disc p r := by
      have := hℓ 0; rwa [Path.source] at this
    rw [b65t_lasso_one δ ℓ (b65t_homotopic_in h hDXF ℓ (Path.refl a) hℓ (fun _ ↦ ha))]
    exact Subgroup.one_mem _

theorem b65t_peripheral_ker (X : Set (OnePoint ℂ)) (F : Finset (OnePoint ℂ))
    (x : ↥(X \ (F : Set (OnePoint ℂ)))) :
    b65t_peripheral X F x ⊆ (FundamentalGroup.map (b65t_fill X F) x).ker := by
  rintro c ⟨p, -, r, hr, hDX, -, y, δ, γ, hγ, rfl⟩
  obtain ⟨h⟩ := (b65t_disc_props p hr).2.2
  rw [SetLike.mem_coe, MonoidHom.mem_ker]
  change FundamentalGroup.fromPath ⟦((δ.trans γ).trans δ.symm).map (b65t_fill X F).continuous⟧ = 1
  rw [Path.map_trans, Path.map_trans, ← Path.map_symm]
  have hy : (y : OnePoint ℂ) ∈ b65t_disc p r := by
    have := hγ 0; rwa [Path.source] at this
  exact b65t_lasso_one _ _ (b65t_homotopic_in h hDX _ (Path.refl _) (fun t ↦ hγ t)
    (fun _ ↦ hy))

/-- Filling a finite set in an open set of the sphere: surjectivity, the peripheral kernel and
descent. -/
theorem b65t_puncture_fill_proof (X : Set (OnePoint ℂ)) (hX : IsOpen X)
    (F : Finset (OnePoint ℂ)) (x : ↥(X \ (F : Set (OnePoint ℂ)))) :
    Function.Surjective (FundamentalGroup.map (b65t_fill X F) x) ∧
      (FundamentalGroup.map (b65t_fill X F) x).ker =
        Subgroup.normalClosure (b65t_peripheral X F x) ∧
      ∀ (G : Type) [Group G] (ρ : FundamentalGroup ↥(X \ (F : Set (OnePoint ℂ))) x →* G),
        (∀ c ∈ b65t_peripheral X F x, ρ c = 1) →
          ∃! σ : FundamentalGroup ↥X (b65t_fill X F x) →* G,
            σ.comp (FundamentalGroup.map (b65t_fill X F) x) = ρ := by
  have hG := b65t_sphere_good X hX F
  have hsurj := b65t_map_surjective hG x
  have hker : (FundamentalGroup.map (b65t_fill X F) x).ker =
      Subgroup.normalClosure (b65t_peripheral X F x) := by
    apply le_antisymm
    · intro g hg
      obtain ⟨γ, hγ⟩ := Quotient.exists_rep g.asHom
      have hg' : g = FundamentalGroup.fromPath ⟦γ⟧ := by
        rw [show (⟦γ⟧ : Path.Homotopic.Quotient x x) = g.asHom from hγ]
      rw [hg'] at hg ⊢
      refine b65t_kernel_mem _ hG (b65t_sphere_localN X F x) γ ?_
      rw [MonoidHom.mem_ker] at hg
      have h1 : (⟦γ.map (b65t_fill X F).continuous⟧ :
          Path.Homotopic.Quotient (b65t_fill X F x) (b65t_fill X F x)) = ⟦Path.refl _⟧ :=
        congrArg End.asHom hg
      exact Quotient.exact h1
    · exact Subgroup.normalClosure_le_normal (b65t_peripheral_ker X F x)
  refine ⟨hsurj, hker, fun G _ ρ hρ ↦ ?_⟩
  have hle : (FundamentalGroup.map (b65t_fill X F) x).ker ≤ ρ.ker := by
    rw [hker]
    exact Subgroup.normalClosure_le_normal fun c hc ↦ hρ c hc
  refine ⟨(FundamentalGroup.map (b65t_fill X F) x).liftOfRightInverse (Function.surjInv hsurj)
    (Function.rightInverse_surjInv hsurj) ⟨ρ, hle⟩, ?_, ?_⟩
  · exact MonoidHom.liftOfRightInverse_comp _ _ _ _
  · intro s' hs'
    exact MonoidHom.eq_liftOfRightInverse _ _ _ _ hle s' hs'

end Sphere

end HodgeLean.Foundations.Program
