import HodgeLean.Foundations.Program.HurwitzPrymRexG32Core

namespace HodgeLean.Foundations.Program

-- A finite transition table checks products by subgroup generators.
def g32p_transitionCheck {n k : ℕ}
    (nodes : Fin n → HurwitzPrymRex_Mat) (gens : Fin k → HurwitzPrymRex_Mat)
    (next : Fin n → Fin k → Fin n) : Bool :=
  decide (∀ i s, HurwitzPrymRex_mmul (nodes i) (gens s) = nodes (next i s))

theorem g32p_transitionCheck_sound {n k : ℕ}
    (nodes : Fin n → HurwitzPrymRex_Mat) (gens : Fin k → HurwitzPrymRex_Mat)
    (next : Fin n → Fin k → Fin n) (w : ℂ) (hw : w ^ 2 + w + 1 = 0)
    (h : g32p_transitionCheck nodes gens next = true) (i : Fin n) (s : Fin k) :
    HurwitzPrymRex_evM w (nodes i) * HurwitzPrymRex_evM w (gens s) =
      HurwitzPrymRex_evM w (nodes (next i s)) := by
  rw [← HurwitzPrymRex_evM_mmul hw]
  exact congrArg (HurwitzPrymRex_evM w) ((of_decide_eq_true h) i s)

theorem g32p_subgroupEnumeration {G : Type*} [Group G] [Finite G] {n k : ℕ}
    (gens : Fin k → G) (nodes : Fin n → G) (origin : Fin n)
    (next : Fin n → Fin k → Fin n)
    (hinj : Function.Injective nodes) (h1 : nodes origin = 1)
    (hmem : ∀ i, nodes i ∈ Subgroup.closure (Set.range gens))
    (hstep : ∀ i s, nodes i * gens s = nodes (next i s)) :
    ∃ e : Fin n ≃ Subgroup.closure (Set.range gens), ∀ i, (e i : G) = nodes i := by
  let T : Submonoid G :=
    { carrier := {g | ∀ i, ∃ j, nodes i * g = nodes j}
      one_mem' := fun i => ⟨i, mul_one _⟩
      mul_mem' := by
        intro a b ha hb i
        obtain ⟨j, hj⟩ := ha i
        obtain ⟨l, hl⟩ := hb j
        exact ⟨l, by rw [← mul_assoc, hj, hl]⟩ }
  have hT : Submonoid.closure (Set.range gens) ≤ T := by
    apply Submonoid.closure_le.mpr
    rintro _ ⟨s, rfl⟩ i
    exact ⟨next i s, hstep i s⟩
  let f : Fin n → Subgroup.closure (Set.range gens) := fun i => ⟨nodes i, hmem i⟩
  have hf : Function.Bijective f := by
    refine ⟨fun i j hij => hinj (congrArg Subtype.val hij), ?_⟩
    intro g
    have hg : (g : G) ∈ Submonoid.closure (Set.range gens) := by
      rw [← Subgroup.closure_toSubmonoid_of_finite]
      exact g.property
    obtain ⟨j, hj⟩ := hT hg origin
    refine ⟨j, Subtype.ext ?_⟩
    simpa only [h1, one_mul] using hj.symm
  exact ⟨Equiv.ofBijective f hf, fun _ => rfl⟩

theorem g32p_generatorSteps_multiplicative {G K : Type*} [Group G] [Finite G]
    [Monoid K] {k : ℕ} (gens : Fin k → G)
    (hgen : Subgroup.closure (Set.range gens) = ⊤)
    (f : G → K) (h1 : f 1 = 1)
    (hstep : ∀ x s, f (x * gens s) = f x * f (gens s)) :
    ∀ x y, f (x * y) = f x * f y := by
  intro x y
  have hy : y ∈ Submonoid.closure (Set.range gens) := by
    rw [← Subgroup.closure_toSubmonoid_of_finite, hgen]
    trivial
  have hmul : ∀ z ∈ Submonoid.closure (Set.range gens),
      ∀ a, f (a * z) = f a * f z := by
    intro z hz
    induction hz using Submonoid.closure_induction with
    | mem z hz =>
      obtain ⟨s, rfl⟩ := hz
      exact fun a => hstep a s
    | one => intro a; simp only [mul_one, h1]
    | mul a b ha hb iha ihb =>
      intro c
      rw [← mul_assoc, ihb, iha, ihb a, mul_assoc]
  exact hmul y hy x

theorem g32p_matrixPathEnumeration {G M : Type*} [Group G] [Finite G] [Monoid M]
    {n k : ℕ} (φ : G →* M) (hφ : Function.Injective φ)
    (evaluate : HurwitzPrymRex_Mat → M)
    (he1 : evaluate HurwitzPrymRex_mone = 1)
    (hemul : ∀ a b, evaluate (HurwitzPrymRex_mmul a b) = evaluate a * evaluate b)
    (hein : Function.Injective evaluate)
    (gens : Fin k → G) (matrices : Fin k → HurwitzPrymRex_Mat)
    (hgens : ∀ s, φ (gens s) = evaluate (matrices s))
    (nodes : Fin n → HurwitzPrymRex_Mat) (origin : Fin n)
    (parent : Fin n → Fin n) (label : Fin n → Fin k) (height : Fin n → ℕ)
    (next : Fin n → Fin k → Fin n)
    (hinj : Function.Injective nodes) (h1 : nodes origin = HurwitzPrymRex_mone)
    (hheight : ∀ i, i ≠ origin → height (parent i) < height i)
    (hpath : ∀ i, i ≠ origin →
      nodes i = HurwitzPrymRex_mmul (nodes (parent i)) (matrices (label i)))
    (hstep : ∀ i s, HurwitzPrymRex_mmul (nodes i) (matrices s) = nodes (next i s)) :
    ∃ e : Fin n ≃ Subgroup.closure (Set.range gens),
      ∀ i, φ (e i : G) = evaluate (nodes i) := by
  classical
  have hnode : ∀ a : ℕ, ∀ i, height i = a →
      ∃ g : G, g ∈ Subgroup.closure (Set.range gens) ∧ φ g = evaluate (nodes i) := by
    intro a
    induction a using Nat.strong_induction_on with
    | h a ih =>
      intro i hi
      by_cases hz : i = origin
      · subst i
        exact ⟨1, (Subgroup.closure _).one_mem, by rw [map_one, h1, he1]⟩
      · obtain ⟨g, hg, he⟩ := ih (height (parent i))
          (hi ▸ hheight i hz) (parent i) rfl
        refine ⟨g * gens (label i), (Subgroup.closure _).mul_mem hg
          (Subgroup.subset_closure (Set.mem_range_self _)), ?_⟩
        rw [map_mul, he, hgens, hpath i hz, hemul]
  choose actual hmem hactual using fun i => hnode (height i) i rfl
  have hactual_inj : Function.Injective actual := by
    intro i j hij
    apply hinj
    apply hein
    rw [← hactual i, ← hactual j, hij]
  have hactual_one : actual origin = 1 := by
    apply hφ
    rw [hactual, h1, he1, map_one]
  have hactual_step (i : Fin n) (s : Fin k) :
      actual i * gens s = actual (next i s) := by
    apply hφ
    rw [map_mul, hactual, hactual, hgens, ← hemul, hstep]
  obtain ⟨e, he⟩ := g32p_subgroupEnumeration gens actual origin next
    hactual_inj hactual_one hmem hactual_step
  exact ⟨e, fun i => by rw [he, hactual]⟩

noncomputable def g32p_homOfFiniteTransitions {G K : Type*} [Group G] [Finite G]
    [Monoid K] {n k : ℕ} (gens : Fin k → G)
    (hgen : Subgroup.closure (Set.range gens) = ⊤)
    (e : Fin n ≃ G) (origin : Fin n) (h1 : e origin = 1)
    (next : Fin n → Fin k → Fin n)
    (hstep : ∀ i s, e (next i s) = e i * gens s)
    (values : Fin n → K) (hzero : values origin = 1)
    (hvalues : ∀ i s, values (next i s) = values i * values (e.symm (gens s))) :
    G →* K where
  toFun x := values (e.symm x)
  map_one' := by rw [← h1, e.symm_apply_apply]; exact hzero
  map_mul' := by
    apply g32p_generatorSteps_multiplicative gens hgen
      (fun x => values (e.symm x))
    · rw [← h1, e.symm_apply_apply]
      exact hzero
    · intro x s
      conv_lhs => rw [← e.apply_symm_apply x, ← hstep, e.symm_apply_apply]
      exact hvalues (e.symm x) s

end HodgeLean.Foundations.Program
