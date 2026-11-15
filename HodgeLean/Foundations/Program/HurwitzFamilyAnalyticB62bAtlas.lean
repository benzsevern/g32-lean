import HodgeLean.Foundations.Program.HurwitzFamilyAnalyticB62bTopology
import HodgeLean.Foundations.Program.HurwitzFamilyAnalyticB62bRoot
import HodgeLean.Foundations.Program.HurwitzFamilyAnalyticB62bStationary

noncomputable section

namespace HodgeLean.Foundations.Program

def b6a_IsMarked (b : Fin 10 → ℂ) {C : Type} (f : C → OnePoint ℂ) (x : C) : Prop :=
  ∃ j : Fin 13, f x = b6_branch b j

theorem b6a_branch_or_open_locus (b : Fin 10 → ℂ) (U C : Type)
    [TopologicalSpace U] [TopologicalSpace C] (f : C → OnePoint ℂ) (ι : U → C)
    (hrange : Set.range ι = f ⁻¹' (Set.range (b6_branch b))ᶜ) (x : C) :
    (∃ j : Fin 13, f x = b6_branch b j) ∨ ∃ u : U, ι u = x := by
  by_cases hx : f x ∈ Set.range (b6_branch b)
  · left
    obtain ⟨j, hj⟩ := hx
    exact ⟨j, hj.symm⟩
  · right
    have hx' : x ∈ f ⁻¹' (Set.range (b6_branch b))ᶜ := hx
    rw [← hrange] at hx'
    exact hx'

theorem b6a_isMarked_smul_iff (b : Fin 10 → ℂ) (G C : Type)
    [Group G] [MulAction G C] (f : C → OnePoint ℂ)
    (hgal : b4_IsGaloisCover G f) (g : G) (x : C) :
    b6a_IsMarked b f (g • x) ↔ b6a_IsMarked b f x := by
  simp only [b6a_IsMarked, hgal.1 g x]

theorem b6a_smul_branch_value (b : Fin 10 → ℂ) (G C : Type)
    [Group G] [MulAction G C] (f : C → OnePoint ℂ)
    (hgal : b4_IsGaloisCover G f) (g : G) (x : C) (j : Fin 13)
    (hx : f x = b6_branch b j) :
    f (g • x) = b6_branch b j := by
  rw [hgal.1 g x, hx]

noncomputable def b6a_markIndex (b : Fin 10 → ℂ) {C : Type}
    (f : C → OnePoint ℂ) (x : C) (hx : b6a_IsMarked b f x) : Fin 13 :=
  hx.choose

theorem b6a_markIndex_eq (b : Fin 10 → ℂ) {C : Type}
    (f : C → OnePoint ℂ) (x : C) (hx : b6a_IsMarked b f x) :
    f x = b6_branch b (b6a_markIndex b f x hx) :=
  hx.choose_spec

noncomputable def b6a_openPoint (b : Fin 10 → ℂ) (U C : Type)
    [TopologicalSpace U] [TopologicalSpace C] (f : C → OnePoint ℂ) (ι : U → C)
    (hrange : Set.range ι = f ⁻¹' (Set.range (b6_branch b))ᶜ)
    (x : C) (hx : ¬ b6a_IsMarked b f x) : U :=
  (b6a_branch_or_open_locus b U C f ι hrange x).resolve_left hx |>.choose

theorem b6a_openPoint_eq (b : Fin 10 → ℂ) (U C : Type)
    [TopologicalSpace U] [TopologicalSpace C] (f : C → OnePoint ℂ) (ι : U → C)
    (hrange : Set.range ι = f ⁻¹' (Set.range (b6_branch b))ᶜ)
    (x : C) (hx : ¬ b6a_IsMarked b f x) :
    ι (b6a_openPoint b U C f ι hrange x hx) = x :=
  (b6a_branch_or_open_locus b U C f ι hrange x).resolve_left hx |>.choose_spec

noncomputable def b6a_markChart (b : Fin 10 → ℂ) (G C : Type)
    [Group G] [TopologicalSpace C] [MulAction G C] [ChartedSpace ℂ C]
    (f : C → OnePoint ℂ) (n : C → ℕ)
    (hlocal : ∀ x (j : Fin 13), f x = b6_branch b j →
      ∃ P : OpenPartialHomeomorph C ℂ,
        x ∈ P.source ∧ P ∈ atlas ℂ C ∧ P x = 0 ∧
        (∀ y ∈ P.source, f y = b6a_value b j (P y ^ n x)) ∧
        ∀ g : MulAction.stabilizer G x, ∃ ζ : ℂ, ζ ^ n x = 1 ∧
          Set.MapsTo (fun y : C ↦ (g : G) • y) P.source P.source ∧
          ∀ y ∈ P.source, P ((g : G) • y) = ζ * P y)
    (x : C) (hx : b6a_IsMarked b f x) : OpenPartialHomeomorph C ℂ :=
  (hlocal x (b6a_markIndex b f x hx) (b6a_markIndex_eq b f x hx)).choose

theorem b6a_markChart_spec (b : Fin 10 → ℂ) (G C : Type)
    [Group G] [TopologicalSpace C] [MulAction G C] [ChartedSpace ℂ C]
    (f : C → OnePoint ℂ) (n : C → ℕ)
    (hlocal : ∀ x (j : Fin 13), f x = b6_branch b j →
      ∃ P : OpenPartialHomeomorph C ℂ,
        x ∈ P.source ∧ P ∈ atlas ℂ C ∧ P x = 0 ∧
        (∀ y ∈ P.source, f y = b6a_value b j (P y ^ n x)) ∧
        ∀ g : MulAction.stabilizer G x, ∃ ζ : ℂ, ζ ^ n x = 1 ∧
          Set.MapsTo (fun y : C ↦ (g : G) • y) P.source P.source ∧
          ∀ y ∈ P.source, P ((g : G) • y) = ζ * P y)
    (x : C) (hx : b6a_IsMarked b f x) :
    x ∈ (b6a_markChart b G C f n hlocal x hx).source ∧
      b6a_markChart b G C f n hlocal x hx ∈ atlas ℂ C ∧
      b6a_markChart b G C f n hlocal x hx x = 0 ∧
      (∀ y ∈ (b6a_markChart b G C f n hlocal x hx).source,
        f y = b6a_value b (b6a_markIndex b f x hx)
          (b6a_markChart b G C f n hlocal x hx y ^ n x)) ∧
      ∀ g : MulAction.stabilizer G x, ∃ ζ : ℂ, ζ ^ n x = 1 ∧
        Set.MapsTo (fun y : C ↦ (g : G) • y)
          (b6a_markChart b G C f n hlocal x hx).source
          (b6a_markChart b G C f n hlocal x hx).source ∧
        ∀ y ∈ (b6a_markChart b G C f n hlocal x hx).source,
          b6a_markChart b G C f n hlocal x hx ((g : G) • y) =
            ζ * b6a_markChart b G C f n hlocal x hx y :=
  (hlocal x (b6a_markIndex b f x hx) (b6a_markIndex_eq b f x hx)).choose_spec

noncomputable def b6a_restrictedMarkChart (b : Fin 10 → ℂ) (G C : Type)
    [Group G] [TopologicalSpace C] [MulAction G C] [ChartedSpace ℂ C]
    (f : C → OnePoint ℂ) (n : C → ℕ)
    (hlocal : ∀ x (j : Fin 13), f x = b6_branch b j →
      ∃ P : OpenPartialHomeomorph C ℂ,
        x ∈ P.source ∧ P ∈ atlas ℂ C ∧ P x = 0 ∧
        (∀ y ∈ P.source, f y = b6a_value b j (P y ^ n x)) ∧
        ∀ g : MulAction.stabilizer G x, ∃ ζ : ℂ, ζ ^ n x = 1 ∧
          Set.MapsTo (fun y : C ↦ (g : G) • y) P.source P.source ∧
          ∀ y ∈ P.source, P ((g : G) • y) = ζ * P y)
    (x : C) (hx : b6a_IsMarked b f x) : OpenPartialHomeomorph C ℂ :=
  (b6a_markChart b G C f n hlocal x hx).trans
    (OpenPartialHomeomorph.ofSet (b6a_rootCoordOpen b (n x))
      (b6a_rootCoordOpen_isOpen b (n x)))

theorem b6a_mem_restrictedMarkChart_source (b : Fin 10 → ℂ) (hb : b ∈ b6_chart)
    (G C : Type) [Group G] [TopologicalSpace C] [MulAction G C] [ChartedSpace ℂ C]
    (f : C → OnePoint ℂ) (n : C → ℕ)
    (hlocal : ∀ x (j : Fin 13), f x = b6_branch b j →
      ∃ P : OpenPartialHomeomorph C ℂ,
        x ∈ P.source ∧ P ∈ atlas ℂ C ∧ P x = 0 ∧
        (∀ y ∈ P.source, f y = b6a_value b j (P y ^ n x)) ∧
        ∀ g : MulAction.stabilizer G x, ∃ ζ : ℂ, ζ ^ n x = 1 ∧
          Set.MapsTo (fun y : C ↦ (g : G) • y) P.source P.source ∧
          ∀ y ∈ P.source, P ((g : G) • y) = ζ * P y)
    (hn : ∀ x, 0 < n x) (x : C) (hx : b6a_IsMarked b f x) :
    x ∈ (b6a_restrictedMarkChart b G C f n hlocal x hx).source := by
  have hs := (b6a_markChart_spec b G C f n hlocal x hx).1
  have hz := (b6a_markChart_spec b G C f n hlocal x hx).2.2.1
  simp [b6a_restrictedMarkChart, hs, b6a_rootCoordOpen, hz,
    Nat.ne_of_gt (hn x), (b6t_discs_aux b hb).1]

theorem b6a_restrictedMarkChart_self (b : Fin 10 → ℂ) (G C : Type)
    [Group G] [TopologicalSpace C] [MulAction G C] [ChartedSpace ℂ C]
    (f : C → OnePoint ℂ) (n : C → ℕ)
    (hlocal : ∀ x (j : Fin 13), f x = b6_branch b j →
      ∃ P : OpenPartialHomeomorph C ℂ,
        x ∈ P.source ∧ P ∈ atlas ℂ C ∧ P x = 0 ∧
        (∀ y ∈ P.source, f y = b6a_value b j (P y ^ n x)) ∧
        ∀ g : MulAction.stabilizer G x, ∃ ζ : ℂ, ζ ^ n x = 1 ∧
          Set.MapsTo (fun y : C ↦ (g : G) • y) P.source P.source ∧
          ∀ y ∈ P.source, P ((g : G) • y) = ζ * P y)
    (x : C) (hx : b6a_IsMarked b f x) :
    b6a_restrictedMarkChart b G C f n hlocal x hx x = 0 := by
  simp [b6a_restrictedMarkChart, (b6a_markChart_spec b G C f n hlocal x hx).2.2.1]

noncomputable def b6a_totalMovingMarkChart (b : Fin 10 → ℂ) (hb : b ∈ b6_chart)
    (C : Type) [TopologicalSpace C] (P : OpenPartialHomeomorph C ℂ)
    (t : b6t_polydisc b) (i : Fin 10) (n : ℕ) (hn : 0 < n) :
    OpenPartialHomeomorph (b6t_polydisc b × C) ((Fin 10 → ℂ) × ℂ) :=
  (((OpenPartialHomeomorph.refl (b6t_polydisc b)).prod P).trans
    (b6a_movingRootHom b hb t i n hn)).trans
      ((b6a_parameterChart b hb).prod (OpenPartialHomeomorph.refl ℂ))

theorem b6a_totalMovingMarkChart_apply (b : Fin 10 → ℂ) (hb : b ∈ b6_chart)
    (C : Type) [TopologicalSpace C] (P : OpenPartialHomeomorph C ℂ)
    (t : b6t_polydisc b) (i : Fin 10) (n : ℕ) (hn : 0 < n)
    (u : b6a_rootParamOpen b t i) (y : C) :
    b6a_totalMovingMarkChart b hb C P t i n hn (u.val, y) =
      (u.val.val, b6a_movingRoot n (P y) (u.val.val i - b i) (b6t_radius b)) := by
  rw [b6a_totalMovingMarkChart, OpenPartialHomeomorph.trans_apply,
    OpenPartialHomeomorph.trans_apply]
  change (b6a_parameterChart b hb).prod (OpenPartialHomeomorph.refl ℂ)
    (b6a_movingRootHom b hb t i n hn (u.val, P y)) = _
  rw [b6a_movingRootHom_apply b hb t i n hn (u, P y)]
  rfl

theorem b6a_mem_totalMovingMarkChart_source (b : Fin 10 → ℂ) (hb : b ∈ b6_chart)
    (C : Type) [TopologicalSpace C] (P : OpenPartialHomeomorph C ℂ)
    (t : b6t_polydisc b) (i : Fin 10) (n : ℕ) (hn : 0 < n)
    (x : C) (hx : x ∈ P.source) (hzero : P x = 0) :
    (t, x) ∈ (b6a_totalMovingMarkChart b hb C P t i n hn).source := by
  simp [b6a_totalMovingMarkChart, hx, hzero, b6a_mem_movingRootHom_source]

theorem b6a_totalMovingMarkChart_source (b : Fin 10 → ℂ) (hb : b ∈ b6_chart)
    (C : Type) [TopologicalSpace C] (P : OpenPartialHomeomorph C ℂ)
    (t : b6t_polydisc b) (i : Fin 10) (n : ℕ) (hn : 0 < n) :
    (b6a_totalMovingMarkChart b hb C P t i n hn).source =
      (b6a_rootParamOpen b t i : Set (b6t_polydisc b)) ×ˢ P.source := by
  ext q
  simp [b6a_totalMovingMarkChart, b6a_movingRootHom_source, and_comm]

theorem b6a_totalMovingMarkChart_apply_of_mem (b : Fin 10 → ℂ) (hb : b ∈ b6_chart)
    (C : Type) [TopologicalSpace C] (P : OpenPartialHomeomorph C ℂ)
    (t : b6t_polydisc b) (i : Fin 10) (n : ℕ) (hn : 0 < n)
    (q : b6t_polydisc b × C)
    (hq : q ∈ (b6a_totalMovingMarkChart b hb C P t i n hn).source) :
    b6a_totalMovingMarkChart b hb C P t i n hn q =
      (q.1.val, b6a_movingRoot n (P q.2) (q.1.val i - b i) (b6t_radius b)) := by
  rw [b6a_totalMovingMarkChart_source] at hq
  exact b6a_totalMovingMarkChart_apply b hb C P t i n hn ⟨q.1, hq.1⟩ q.2

theorem b6a_totalMovingMarkChart_self (b : Fin 10 → ℂ) (hb : b ∈ b6_chart)
    (C : Type) [TopologicalSpace C] (P : OpenPartialHomeomorph C ℂ)
    (t : b6t_polydisc b) (i : Fin 10) (n : ℕ) (hn : 0 < n)
    (x : C) (hzero : P x = 0) :
    (b6a_totalMovingMarkChart b hb C P t i n hn (t, x)).2 = 0 := by
  let u : b6a_rootParamOpen b t i := ⟨t, b6a_mem_rootParamOpen b t i⟩
  rw [show t = u.val by rfl, b6a_totalMovingMarkChart_apply]
  simp [hzero, b6a_movingRoot]

theorem b6a_totalMovingMarkChart_power (b : Fin 10 → ℂ) (hb : b ∈ b6_chart)
    (C : Type) [TopologicalSpace C] (P : OpenPartialHomeomorph C ℂ)
    (f : C → OnePoint ℂ) (t : b6t_polydisc b) (i : Fin 10)
    (n : ℕ) (hn : 0 < n)
    (hf : ∀ x ∈ P.source, f x = ((b i + P x ^ n : ℂ) : OnePoint ℂ))
    (hr : ∀ x ∈ P.source, ‖P x‖ ^ n < b6t_radius b)
    (q : b6t_polydisc b × C)
    (hq : q ∈ (b6a_totalMovingMarkChart b hb C P t i n hn).source) :
    b6a_map b f q =
      ((q.1.val i + (b6a_totalMovingMarkChart b hb C P t i n hn q).2 ^ n : ℂ) :
        OnePoint ℂ) := by
  have hx : q.2 ∈ P.source := by
    rw [b6a_totalMovingMarkChart_source] at hq
    exact hq.2
  rw [b6a_totalMovingMarkChart_apply_of_mem b hb C P t i n hn q hq]
  simp only [b6a_map, hf q.2 hx]
  change ((b6t_plane b q.1.val (b i + P q.2 ^ n) : ℂ) : OnePoint ℂ) = _
  congr 1
  rw [b6a_movingRoot_pow n hn]
  have h := b6a_plane_near_branch b q.1.val hb i n (P q.2) (hr q.2 hx)
  linear_combination h

noncomputable def b6a_familyChart (b : Fin 10 → ℂ) (hb : b ∈ b6_chart)
    (G U C : Type) [Group G] [TopologicalSpace U] [MulAction G U]
    [TopologicalSpace C] [Nonempty U] [MulAction G C] [ChartedSpace ℂ C]
    (π : U → b6t_punctured b) (hπ : IsQuotientCoveringMap π G)
    (f : C → OnePoint ℂ) (ι : U → C) (hι : Topology.IsOpenEmbedding ι)
    (hrange : Set.range ι = f ⁻¹' (Set.range (b6_branch b))ᶜ) (n : C → ℕ)
    (hn : ∀ x, 0 < n x)
    (hlocal : ∀ x (j : Fin 13), f x = b6_branch b j →
      ∃ P : OpenPartialHomeomorph C ℂ,
        x ∈ P.source ∧ P ∈ atlas ℂ C ∧ P x = 0 ∧
        (∀ y ∈ P.source, f y = b6a_value b j (P y ^ n x)) ∧
        ∀ g : MulAction.stabilizer G x, ∃ ζ : ℂ, ζ ^ n x = 1 ∧
          Set.MapsTo (fun y : C ↦ (g : G) • y) P.source P.source ∧
          ∀ y ∈ P.source, P ((g : G) • y) = ζ * P y)
    (q : b6t_polydisc b × C) :
    OpenPartialHomeomorph (b6t_polydisc b × C) ((Fin 10 → ℂ) × ℂ) := by
  classical
  exact if hx : b6a_IsMarked b f q.2 then
    let j := b6a_markIndex b f q.2 hx
    let P := b6a_restrictedMarkChart b G C f n hlocal q.2 hx
    if hj : j.val < 10 then
      b6a_totalMovingMarkChart b hb C P q.1 ⟨j.val, hj⟩ (n q.2) (hn q.2)
    else b6a_productChart b hb C (b6a_fixedMarkChart b j (n q.2) P)
  else
    b6a_totalUnramifiedChart b hb G U C π hπ ι hι
      (b6a_openPoint b U C f ι hrange q.2 hx)

theorem b6a_mem_familyChart_source (b : Fin 10 → ℂ) (hb : b ∈ b6_chart)
    (G U C : Type) [Group G] [TopologicalSpace U] [MulAction G U]
    [TopologicalSpace C] [Nonempty U] [MulAction G C] [ChartedSpace ℂ C]
    (π : U → b6t_punctured b) (hπ : IsQuotientCoveringMap π G)
    (f : C → OnePoint ℂ) (ι : U → C) (hι : Topology.IsOpenEmbedding ι)
    (hrange : Set.range ι = f ⁻¹' (Set.range (b6_branch b))ᶜ) (n : C → ℕ)
    (hn : ∀ x, 0 < n x)
    (hlocal : ∀ x (j : Fin 13), f x = b6_branch b j →
      ∃ P : OpenPartialHomeomorph C ℂ,
        x ∈ P.source ∧ P ∈ atlas ℂ C ∧ P x = 0 ∧
        (∀ y ∈ P.source, f y = b6a_value b j (P y ^ n x)) ∧
        ∀ g : MulAction.stabilizer G x, ∃ ζ : ℂ, ζ ^ n x = 1 ∧
          Set.MapsTo (fun y : C ↦ (g : G) • y) P.source P.source ∧
          ∀ y ∈ P.source, P ((g : G) • y) = ζ * P y)
    (q : b6t_polydisc b × C) :
    q ∈ (b6a_familyChart b hb G U C π hπ f ι hι hrange n hn hlocal q).source := by
  classical
  by_cases hx : b6a_IsMarked b f q.2
  · let j := b6a_markIndex b f q.2 hx
    let P := b6a_restrictedMarkChart b G C f n hlocal q.2 hx
    have hPs : q.2 ∈ P.source := b6a_mem_restrictedMarkChart_source
      b hb G C f n hlocal hn q.2 hx
    have hP0 : P q.2 = 0 := b6a_restrictedMarkChart_self b G C f n hlocal q.2 hx
    by_cases hj : j.val < 10
    · rw [b6a_familyChart, dif_pos hx, dif_pos hj]
      exact b6a_mem_totalMovingMarkChart_source b hb C P q.1 ⟨j.val, hj⟩
        (n q.2) (hn q.2) q.2 hPs hP0
    · rw [b6a_familyChart, dif_pos hx, dif_neg hj]
      exact ⟨Set.mem_univ _,
        b6a_mem_fixedMarkChart_source b hb j hj (n q.2) (hn q.2) P q.2 hPs hP0⟩
  · rw [b6a_familyChart, dif_neg hx]
    let u := b6a_openPoint b U C f ι hrange q.2 hx
    have hu := b6a_mem_unramifiedChart_source b G U C π hπ ι hι u
    have heq : ι u = q.2 := b6a_openPoint_eq b U C f ι hrange q.2 hx
    have hmem : q.2 ∈ (b6a_unramifiedChart b G U C π hπ ι hι u).source := by
      rw [← heq]
      exact hu
    have hcomplex : q.2 ∈ (b6a_unramifiedComplexChart b G U C π hπ ι hι u).source := by
      simp [b6a_unramifiedComplexChart, hmem]
    simp [u, b6a_totalUnramifiedChart, hcomplex]

theorem b6a_familyChart_fst (b : Fin 10 → ℂ) (hb : b ∈ b6_chart)
    (G U C : Type) [Group G] [TopologicalSpace U] [MulAction G U]
    [TopologicalSpace C] [Nonempty U] [MulAction G C] [ChartedSpace ℂ C]
    (π : U → b6t_punctured b) (hπ : IsQuotientCoveringMap π G)
    (f : C → OnePoint ℂ) (ι : U → C) (hι : Topology.IsOpenEmbedding ι)
    (hrange : Set.range ι = f ⁻¹' (Set.range (b6_branch b))ᶜ) (n : C → ℕ)
    (hn : ∀ x, 0 < n x)
    (hlocal : ∀ x (j : Fin 13), f x = b6_branch b j →
      ∃ P : OpenPartialHomeomorph C ℂ,
        x ∈ P.source ∧ P ∈ atlas ℂ C ∧ P x = 0 ∧
        (∀ y ∈ P.source, f y = b6a_value b j (P y ^ n x)) ∧
        ∀ g : MulAction.stabilizer G x, ∃ ζ : ℂ, ζ ^ n x = 1 ∧
          Set.MapsTo (fun y : C ↦ (g : G) • y) P.source P.source ∧
          ∀ y ∈ P.source, P ((g : G) • y) = ζ * P y)
    (q y : b6t_polydisc b × C)
    (hy : y ∈ (b6a_familyChart b hb G U C π hπ f ι hι hrange n hn hlocal q).source) :
    (b6a_familyChart b hb G U C π hπ f ι hι hrange n hn hlocal q y).1 = y.1.val := by
  classical
  by_cases hx : b6a_IsMarked b f q.2
  · rw [b6a_familyChart, dif_pos hx] at hy ⊢
    dsimp only at hy ⊢
    by_cases hj : (b6a_markIndex b f q.2 hx).val < 10
    · rw [dif_pos hj] at hy ⊢
      rw [b6a_totalMovingMarkChart_apply_of_mem b hb C _ _ _ _ _ y hy]
    · rw [dif_neg hj]
      rfl
  · simp [b6a_familyChart, hx, b6a_totalUnramifiedChart]

noncomputable def b6a_familyChartedSpace (b : Fin 10 → ℂ) (C : Type)
    [TopologicalSpace C]
    (A : (b6t_polydisc b × C) →
      OpenPartialHomeomorph (b6t_polydisc b × C) ((Fin 10 → ℂ) × ℂ))
    (hA : ∀ q, q ∈ (A q).source) :
    ChartedSpace ((Fin 10 → ℂ) × ℂ) (b6t_polydisc b × C) where
  atlas := Set.range A
  chartAt := A
  mem_chart_source := hA
  chart_mem_atlas q := ⟨q, rfl⟩

noncomputable def b6a_totalChart (b : Fin 10 → ℂ) (hb : b ∈ b6_chart)
    (G U C : Type) [Group G] [TopologicalSpace U] [MulAction G U]
    [TopologicalSpace C] [Nonempty U] [MulAction G C] [ChartedSpace ℂ C]
    (π : U → b6t_punctured b) (hπ : IsQuotientCoveringMap π G)
    (f : C → OnePoint ℂ) (ι : U → C) (hι : Topology.IsOpenEmbedding ι)
    (hrange : Set.range ι = f ⁻¹' (Set.range (b6_branch b))ᶜ) (n : C → ℕ)
    (hlocal : ∀ x (j : Fin 13), f x = b6_branch b j →
      ∃ P : OpenPartialHomeomorph C ℂ,
        x ∈ P.source ∧ P ∈ atlas ℂ C ∧ P x = 0 ∧
        (∀ y ∈ P.source, f y = b6a_value b j (P y ^ n x)) ∧
        ∀ g : MulAction.stabilizer G x, ∃ ζ : ℂ, ζ ^ n x = 1 ∧
          Set.MapsTo (fun y : C ↦ (g : G) • y) P.source P.source ∧
          ∀ y ∈ P.source, P ((g : G) • y) = ζ * P y)
    (q : b6t_polydisc b × C) :
    OpenPartialHomeomorph (b6t_polydisc b × C) ((Fin 10 → ℂ) × ℂ) := by
  classical
  exact if hx : b6a_IsMarked b f q.2 then
      b6a_productChart b hb C (b6a_markChart b G C f n hlocal q.2 hx)
    else
      b6a_totalUnramifiedChart b hb G U C π hπ ι hι
        (b6a_openPoint b U C f ι hrange q.2 hx)

theorem b6a_totalChart_of_marked (b : Fin 10 → ℂ) (hb : b ∈ b6_chart)
    (G U C : Type) [Group G] [TopologicalSpace U] [MulAction G U]
    [TopologicalSpace C] [Nonempty U] [MulAction G C] [ChartedSpace ℂ C]
    (π : U → b6t_punctured b) (hπ : IsQuotientCoveringMap π G)
    (f : C → OnePoint ℂ) (ι : U → C) (hι : Topology.IsOpenEmbedding ι)
    (hrange : Set.range ι = f ⁻¹' (Set.range (b6_branch b))ᶜ) (n : C → ℕ)
    (hlocal : ∀ x (j : Fin 13), f x = b6_branch b j →
      ∃ P : OpenPartialHomeomorph C ℂ,
        x ∈ P.source ∧ P ∈ atlas ℂ C ∧ P x = 0 ∧
        (∀ y ∈ P.source, f y = b6a_value b j (P y ^ n x)) ∧
        ∀ g : MulAction.stabilizer G x, ∃ ζ : ℂ, ζ ^ n x = 1 ∧
          Set.MapsTo (fun y : C ↦ (g : G) • y) P.source P.source ∧
          ∀ y ∈ P.source, P ((g : G) • y) = ζ * P y)
    (q : b6t_polydisc b × C) (hq : b6a_IsMarked b f q.2) :
    b6a_totalChart b hb G U C π hπ f ι hι hrange n hlocal q =
      b6a_productChart b hb C (b6a_markChart b G C f n hlocal q.2 hq) := by
  simp [b6a_totalChart, hq]

theorem b6a_totalChart_of_open (b : Fin 10 → ℂ) (hb : b ∈ b6_chart)
    (G U C : Type) [Group G] [TopologicalSpace U] [MulAction G U]
    [TopologicalSpace C] [Nonempty U] [MulAction G C] [ChartedSpace ℂ C]
    (π : U → b6t_punctured b) (hπ : IsQuotientCoveringMap π G)
    (f : C → OnePoint ℂ) (ι : U → C) (hι : Topology.IsOpenEmbedding ι)
    (hrange : Set.range ι = f ⁻¹' (Set.range (b6_branch b))ᶜ) (n : C → ℕ)
    (hlocal : ∀ x (j : Fin 13), f x = b6_branch b j →
      ∃ P : OpenPartialHomeomorph C ℂ,
        x ∈ P.source ∧ P ∈ atlas ℂ C ∧ P x = 0 ∧
        (∀ y ∈ P.source, f y = b6a_value b j (P y ^ n x)) ∧
        ∀ g : MulAction.stabilizer G x, ∃ ζ : ℂ, ζ ^ n x = 1 ∧
          Set.MapsTo (fun y : C ↦ (g : G) • y) P.source P.source ∧
          ∀ y ∈ P.source, P ((g : G) • y) = ζ * P y)
    (q : b6t_polydisc b × C) (hq : ¬ b6a_IsMarked b f q.2) :
    b6a_totalChart b hb G U C π hπ f ι hι hrange n hlocal q =
      b6a_totalUnramifiedChart b hb G U C π hπ ι hι
        (b6a_openPoint b U C f ι hrange q.2 hq) := by
  simp [b6a_totalChart, hq]

theorem b6a_mem_totalChart_source (b : Fin 10 → ℂ) (hb : b ∈ b6_chart)
    (G U C : Type) [Group G] [TopologicalSpace U] [MulAction G U]
    [TopologicalSpace C] [Nonempty U] [MulAction G C] [ChartedSpace ℂ C]
    (π : U → b6t_punctured b) (hπ : IsQuotientCoveringMap π G)
    (f : C → OnePoint ℂ) (ι : U → C) (hι : Topology.IsOpenEmbedding ι)
    (hrange : Set.range ι = f ⁻¹' (Set.range (b6_branch b))ᶜ) (n : C → ℕ)
    (hlocal : ∀ x (j : Fin 13), f x = b6_branch b j →
      ∃ P : OpenPartialHomeomorph C ℂ,
        x ∈ P.source ∧ P ∈ atlas ℂ C ∧ P x = 0 ∧
        (∀ y ∈ P.source, f y = b6a_value b j (P y ^ n x)) ∧
        ∀ g : MulAction.stabilizer G x, ∃ ζ : ℂ, ζ ^ n x = 1 ∧
          Set.MapsTo (fun y : C ↦ (g : G) • y) P.source P.source ∧
          ∀ y ∈ P.source, P ((g : G) • y) = ζ * P y)
    (q : b6t_polydisc b × C) :
    q ∈ (b6a_totalChart b hb G U C π hπ f ι hι hrange n hlocal q).source := by
  classical
  by_cases hq : b6a_IsMarked b f q.2
  · rw [b6a_totalChart_of_marked b hb G U C π hπ f ι hι hrange n hlocal q hq]
    simp [b6a_markChart_spec b G C f n hlocal q.2 hq |>.1]
  · rw [b6a_totalChart_of_open b hb G U C π hπ f ι hι hrange n hlocal q hq]
    let u := b6a_openPoint b U C f ι hrange q.2 hq
    have hu := b6a_mem_unramifiedChart_source b G U C π hπ ι hι u
    have heq : ι u = q.2 := b6a_openPoint_eq b U C f ι hrange q.2 hq
    have hmem : q.2 ∈ (b6a_unramifiedChart b G U C π hπ ι hι u).source := by
      rw [← heq]
      exact hu
    have hcomplex : q.2 ∈ (b6a_unramifiedComplexChart b G U C π hπ ι hι
        u).source := by
      simp [b6a_unramifiedComplexChart, hmem]
    simpa [u, b6a_totalUnramifiedChart, hcomplex]

end HodgeLean.Foundations.Program
