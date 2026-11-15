import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Topology.UnitInterval

/-! # Interval subdivisions for projective topology
Implication from path homotopies and open covers to finite path comparisons.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory
open scoped unitInterval
namespace HodgeLean.Foundations.Program

/-- The linear path between two points of the unit interval. -/
def s2e_c11_interval_segment (a b : unitInterval) : Path a b where
  toFun := Set.Icc.convexComb a b
  continuous_toFun := Set.Icc.continuous_convexComb a b
  source' := Set.Icc.convexComb_zero a b
  target' := Set.Icc.convexComb_one a b

/-- The path class of an interval segment under a continuous map. -/
def s2e_c11_interval_path_class
    {X : Type*} [TopologicalSpace X] (γ : C(unitInterval, X)) (a b : unitInterval) :
    (⟨γ a⟩ : FundamentalGroupoid X) ⟶ ⟨γ b⟩ :=
  Path.Homotopic.Quotient.mk ((s2e_c11_interval_segment a b).map γ.continuous)

/-- Interval segment classes compose through every intermediate parameter.
Source: Mathlib, convex contractibility and homotopy invariance of path composition. -/
theorem s2e_c11_interval_path_class_comp
    {X : Type*} [TopologicalSpace X] (γ : C(unitInterval, X))
    (a b c : unitInterval) :
    s2e_c11_interval_path_class γ a b ≫ s2e_c11_interval_path_class γ b c =
      s2e_c11_interval_path_class γ a c := by
  have : ContractibleSpace unitInterval :=
    (convex_Icc (0 : ℝ) 1).contractibleSpace ⟨0, by constructor <;> norm_num⟩
  have h := SimplyConnectedSpace.paths_homotopic
    ((s2e_c11_interval_segment a b).trans (s2e_c11_interval_segment b c))
    (s2e_c11_interval_segment a c)
  have hm := h.map γ
  apply Path.Homotopic.Quotient.eq.mpr
  simpa only [Path.map_trans] using hm

/-- Paths contained in one simply connected subset are homotopic in the ambient space.
Source: Mathlib, SimplyConnectedSpace.paths_homotopic and Path.Homotopic.map. -/
theorem s2e_c11_paths_homotopic_in_subset
    {X : Type*} [TopologicalSpace X] {U : Set X} (hU : IsSimplyConnected U)
    {x y : X} (p q : Path x y) (hp : ∀ t, p t ∈ U) (hq : ∀ t, q t ∈ U) :
    p.Homotopic q := by
  have : SimplyConnectedSpace U := hU
  have hx : x ∈ U := p.source ▸ hp 0
  have hy : y ∈ U := p.target ▸ hp 1
  let p' : Path (⟨x, hx⟩ : U) ⟨y, hy⟩ :=
    { toFun := fun t ↦ ⟨p t, hp t⟩
      continuous_toFun := p.continuous.subtype_mk _
      source' := Subtype.ext p.source
      target' := Subtype.ext p.target }
  let q' : Path (⟨x, hx⟩ : U) ⟨y, hy⟩ :=
    { toFun := fun t ↦ ⟨q t, hq t⟩
      continuous_toFun := q.continuous.subtype_mk _
      source' := Subtype.ext q.source
      target' := Subtype.ext q.target }
  exact (SimplyConnectedSpace.paths_homotopic p' q').map
    ⟨Subtype.val, continuous_subtype_val⟩

/-- A stationary interval segment represents the identity path class.
Source: Mathlib, Path.Homotopic.Quotient and Set.Icc.convexComb_eq. -/
theorem s2e_c11_interval_path_class_self
    {X : Type*} [TopologicalSpace X] (γ : C(unitInterval, X)) (a : unitInterval) :
    s2e_c11_interval_path_class γ a a = 𝟙 (⟨γ a⟩ : FundamentalGroupoid X) := by
  change Path.Homotopic.Quotient.mk _ = Path.Homotopic.Quotient.mk _
  congr 1
  ext t
  exact congrArg γ (Set.Icc.convexComb_eq a t)

/-- Local path-class identities on an open cover extend along every continuous interval map.
Source: Mathlib, exists_monotone_Icc_subset_open_cover_unitInterval;
Hatcher, Algebraic Topology, section 1.2, path subdivision. -/
theorem s2e_c11_subdivision_transport
    {X ι : Type*} [TopologicalSpace X] (U : ι → Set X)
    (hopen : ∀ i, IsOpen (U i)) (hcover : ∀ x, ∃ i, x ∈ U i)
    (o : X) (c : ∀ x : X, (⟨o⟩ : FundamentalGroupoid X) ⟶ ⟨x⟩)
    (hlocal : ∀ i, ∀ {x y : X}, ∀ p : Path x y,
      (∀ t, p t ∈ U i) → c x ≫ Path.Homotopic.Quotient.mk p = c y)
    (γ : C(unitInterval, X)) :
    c (γ 0) ≫ s2e_c11_interval_path_class γ 0 1 = c (γ 1) := by
  obtain ⟨t, ht0, hmono, ⟨N, hN⟩, hsub⟩ :=
    exists_monotone_Icc_subset_open_cover_unitInterval
      (c := fun i ↦ γ ⁻¹' U i) (fun i ↦ (hopen i).preimage γ.continuous) (by
        intro z _
        obtain ⟨i, hi⟩ := hcover (γ z)
        exact Set.mem_iUnion.mpr ⟨i, hi⟩)
  have hchain : ∀ n, c (γ (t 0)) ≫ s2e_c11_interval_path_class γ (t 0) (t n) =
      c (γ (t n)) := by
    intro n
    induction n with
    | zero => rw [s2e_c11_interval_path_class_self, Category.comp_id]
    | succ n ih =>
      rw [← s2e_c11_interval_path_class_comp γ (t 0) (t n) (t (n + 1)),
        ← Category.assoc, ih]
      obtain ⟨i, hi⟩ := hsub n
      apply hlocal i ((s2e_c11_interval_segment (t n) (t (n + 1))).map γ.continuous)
      intro u
      apply hi
      exact ⟨Set.Icc.le_convexComb (hmono (Nat.le_succ n)) u,
        Set.Icc.convexComb_le (hmono (Nat.le_succ n)) u⟩
  have hz : t 0 = 0 := by exact_mod_cast ht0
  have hn : t N = 1 := by exact_mod_cast hN N le_rfl
  have hh := hchain N
  generalize ha : t 0 = a at hh
  generalize hb : t N = b at hh
  have ha0 : a = 0 := ha.symm.trans hz
  have hb1 : b = 1 := hb.symm.trans hn
  cases ha0
  cases hb1
  exact hh

/-- Compatible local path classes on an open cover yield simple connectivity.
Source: Hatcher, Algebraic Topology, section 1.2, path subdivision;
Mathlib, simply_connected_iff_paths_homotopic. -/
theorem s2e_c11_simply_connected_of_local_path_classes
    {X ι : Type*} [TopologicalSpace X] [PathConnectedSpace X]
    (U : ι → Set X) (hopen : ∀ i, IsOpen (U i)) (hcover : ∀ x, ∃ i, x ∈ U i)
    (o : X) (c : ∀ x : X, (⟨o⟩ : FundamentalGroupoid X) ⟶ ⟨x⟩)
    (hlocal : ∀ i, ∀ {x y : X}, ∀ p : Path x y,
      (∀ t, p t ∈ U i) → c x ≫ Path.Homotopic.Quotient.mk p = c y) :
    SimplyConnectedSpace X := by
  have hglobal {x y : X} (p : Path x y) :
      c x ≫ Path.Homotopic.Quotient.mk p = c y := by
    rcases p with ⟨γ, hx, hy⟩
    dsimp at hx hy
    subst x
    subst y
    have hh := s2e_c11_subdivision_transport U hopen hcover o c hlocal γ
    have heq : (s2e_c11_interval_segment 0 1).map γ.continuous =
        (⟨γ, rfl, rfl⟩ : Path (γ 0) (γ 1)) := by
      ext t
      exact congrArg γ (Set.Icc.convexComb_zero_one t)
    change c (γ 0) ≫ Path.Homotopic.Quotient.mk _ = c (γ 1) at hh
    rw [heq] at hh
    exact hh
  apply simply_connected_iff_paths_homotopic.mpr
  refine ⟨inferInstance, fun x y ↦ ⟨?_⟩⟩
  intro p q
  induction p using Path.Homotopic.Quotient.ind with
  | mk p =>
    induction q using Path.Homotopic.Quotient.ind with
    | mk q =>
      exact (cancel_epi (c x)).mp ((hglobal p).trans (hglobal q).symm)

/-- Two simply connected open sets with path connected intersection have simply connected union.
Source: Hatcher, Algebraic Topology, section 1.2, the two-open-set van Kampen argument. -/
theorem s2e_c11_simply_connected_two_open_cover
    {X : Type*} [TopologicalSpace X] (U V : Set X)
    (hUopen : IsOpen U) (hVopen : IsOpen V) (hcover : U ∪ V = Set.univ)
    (hU : IsSimplyConnected U) (hV : IsSimplyConnected V)
    (hUV : IsPathConnected (U ∩ V)) : SimplyConnectedSpace X := by
  classical
  obtain ⟨o, ho⟩ := hUV.nonempty
  have hmem (x : X) : x ∈ U ∨ x ∈ V := by
    have : x ∈ U ∪ V := by rw [hcover]; trivial
    exact this
  have : PathConnectedSpace X := pathConnectedSpace_iff_univ.mpr (by
    rw [← hcover]
    exact hU.isPathConnected.union hV.isPathConnected hUV.nonempty)
  let pU (x : X) (hx : x ∈ U) : Path o x :=
    (hU.isPathConnected.joinedIn o ho.1 x hx).somePath
  let pV (x : X) (hx : x ∈ V) : Path o x :=
    (hV.isPathConnected.joinedIn o ho.2 x hx).somePath
  have hpU (x : X) (hx : x ∈ U) (t : unitInterval) : pU x hx t ∈ U :=
    (hU.isPathConnected.joinedIn o ho.1 x hx).somePath_mem t
  have hpV (x : X) (hx : x ∈ V) (t : unitInterval) : pV x hx t ∈ V :=
    (hV.isPathConnected.joinedIn o ho.2 x hx).somePath_mem t
  have hboth (x : X) (hxU : x ∈ U) (hxV : x ∈ V) :
      Path.Homotopic.Quotient.mk (pU x hxU) = Path.Homotopic.Quotient.mk (pV x hxV) := by
    let d := (hUV.joinedIn o ho x ⟨hxU, hxV⟩).somePath
    have hd (t : unitInterval) : d t ∈ U ∩ V :=
      (hUV.joinedIn o ho x ⟨hxU, hxV⟩).somePath_mem t
    apply Path.Homotopic.Quotient.eq.mpr
    exact (s2e_c11_paths_homotopic_in_subset hU (pU x hxU) d
      (hpU x hxU) (fun t ↦ (hd t).1)).trans
      (s2e_c11_paths_homotopic_in_subset hV d (pV x hxV)
        (fun t ↦ (hd t).2) (hpV x hxV))
  let c (x : X) : (⟨o⟩ : FundamentalGroupoid X) ⟶ ⟨x⟩ :=
    if hx : x ∈ U then Path.Homotopic.Quotient.mk (pU x hx)
    else Path.Homotopic.Quotient.mk (pV x ((hmem x).resolve_left hx))
  have hcU (x : X) (hx : x ∈ U) : c x = Path.Homotopic.Quotient.mk (pU x hx) := by
    simp only [c, dif_pos hx]
  have hcV (x : X) (hx : x ∈ V) : c x = Path.Homotopic.Quotient.mk (pV x hx) := by
    by_cases hu : x ∈ U
    · exact (hcU x hu).trans (hboth x hu hx)
    · simp only [c, dif_neg hu]
  have hlocalU {x y : X} (p : Path x y) (hp : ∀ t, p t ∈ U) :
      c x ≫ Path.Homotopic.Quotient.mk p = c y := by
    have hx : x ∈ U := p.source ▸ hp 0
    have hy : y ∈ U := p.target ▸ hp 1
    rw [hcU x hx, hcU y hy]
    apply Path.Homotopic.Quotient.eq.mpr
    apply s2e_c11_paths_homotopic_in_subset hU ((pU x hx).trans p) (pU y hy)
    · intro t
      have ht := Set.mem_range_self (f := (pU x hx).trans p) t
      rw [Path.trans_range] at ht
      rcases ht with ⟨u, hu⟩ | ⟨u, hu⟩
      · exact hu ▸ hpU x hx u
      · exact hu ▸ hp u
    · exact hpU y hy
  have hlocalV {x y : X} (p : Path x y) (hp : ∀ t, p t ∈ V) :
      c x ≫ Path.Homotopic.Quotient.mk p = c y := by
    have hx : x ∈ V := p.source ▸ hp 0
    have hy : y ∈ V := p.target ▸ hp 1
    rw [hcV x hx, hcV y hy]
    apply Path.Homotopic.Quotient.eq.mpr
    apply s2e_c11_paths_homotopic_in_subset hV ((pV x hx).trans p) (pV y hy)
    · intro t
      have ht := Set.mem_range_self (f := (pV x hx).trans p) t
      rw [Path.trans_range] at ht
      rcases ht with ⟨u, hu⟩ | ⟨u, hu⟩
      · exact hu ▸ hpV x hx u
      · exact hu ▸ hp u
    · exact hpV y hy
  refine s2e_c11_simply_connected_of_local_path_classes
    (fun b : Bool ↦ cond b U V) (by intro b; cases b; exact hVopen; exact hUopen)
    (fun x ↦ ?_) o c ?_
  · rcases hmem x with hx | hx
    · exact ⟨true, hx⟩
    · exact ⟨false, hx⟩
  · intro b x y p hp
    cases b
    · exact hlocalV p hp
    · exact hlocalU p hp

/-- A cover by simply connected opens with a common point and path connected pairwise intersections is simply connected.
Source: Hatcher, Algebraic Topology, section 1.2, path-class gluing. -/
theorem s2e_c11_simply_connected_common_point_cover
    {X ι : Type*} [TopologicalSpace X] (U : ι → Set X)
    (hopen : ∀ i, IsOpen (U i)) (hcover : ∀ x, ∃ i, x ∈ U i)
    (hU : ∀ i, IsSimplyConnected (U i))
    (o : X) (ho : ∀ i, o ∈ U i)
    (hinter : ∀ i j, IsPathConnected (U i ∩ U j)) : SimplyConnectedSpace X := by
  classical
  let label (x : X) : ι := (hcover x).choose
  have hlabel (x : X) : x ∈ U (label x) := (hcover x).choose_spec
  let p (i : ι) (x : X) (hx : x ∈ U i) : Path o x :=
    ((hU i).isPathConnected.joinedIn o (ho i) x hx).somePath
  have hp (i : ι) (x : X) (hx : x ∈ U i) (t : unitInterval) : p i x hx t ∈ U i :=
    ((hU i).isPathConnected.joinedIn o (ho i) x hx).somePath_mem t
  have : PathConnectedSpace X := pathConnectedSpace_iff_univ.mpr (by
    refine ⟨o, trivial, fun x _ ↦ ?_⟩
    exact ⟨p (label x) x (hlabel x), fun _ ↦ trivial⟩)
  have hcoh (i j : ι) (x : X) (hi : x ∈ U i) (hj : x ∈ U j) :
      Path.Homotopic.Quotient.mk (p i x hi) = Path.Homotopic.Quotient.mk (p j x hj) := by
    let d := ((hinter i j).joinedIn o ⟨ho i, ho j⟩ x ⟨hi, hj⟩).somePath
    have hd (t : unitInterval) : d t ∈ U i ∩ U j :=
      ((hinter i j).joinedIn o ⟨ho i, ho j⟩ x ⟨hi, hj⟩).somePath_mem t
    apply Path.Homotopic.Quotient.eq.mpr
    exact (s2e_c11_paths_homotopic_in_subset (hU i) (p i x hi) d
      (hp i x hi) (fun t ↦ (hd t).1)).trans
      (s2e_c11_paths_homotopic_in_subset (hU j) d (p j x hj)
        (fun t ↦ (hd t).2) (hp j x hj))
  let c (x : X) : (⟨o⟩ : FundamentalGroupoid X) ⟶ ⟨x⟩ :=
    Path.Homotopic.Quotient.mk (p (label x) x (hlabel x))
  have hc (i : ι) (x : X) (hx : x ∈ U i) : c x = Path.Homotopic.Quotient.mk (p i x hx) :=
    hcoh (label x) i x (hlabel x) hx
  apply s2e_c11_simply_connected_of_local_path_classes U hopen hcover o c
  intro i x y q hq
  have hx : x ∈ U i := q.source ▸ hq 0
  have hy : y ∈ U i := q.target ▸ hq 1
  rw [hc i x hx, hc i y hy]
  apply Path.Homotopic.Quotient.eq.mpr
  apply s2e_c11_paths_homotopic_in_subset (hU i) ((p i x hx).trans q) (p i y hy)
  · intro t
    have ht := Set.mem_range_self (f := (p i x hx).trans q) t
    rw [Path.trans_range] at ht
    rcases ht with ⟨u, hu⟩ | ⟨u, hu⟩
    · exact hu ▸ hp i x hx u
    · exact hu ▸ hq u
  · exact hp i y hy

end HodgeLean.Foundations.Program
