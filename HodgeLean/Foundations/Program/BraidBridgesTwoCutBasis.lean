import HodgeLean.Foundations.Program.BraidBridgesTwoDefs
import HodgeLean.Foundations.Program.RigidStartingSystemPeripheralClasses

/-! # Once-crossing cut loops of the downstairs plane

Complex conjugation carries the upward-slit cut loops of the Riemann–Roch topology section to
loops crossing the downward cuts from 5, minus seven and zero once from left to right. They form
a free basis and have the printed local classes. HC no distance; AV milestone no distance.
-/

noncomputable section
namespace HodgeLean.Foundations.Program

theorem b65x_cb_notMem (z : ℂ) : z ∉ b65r_sourcePoles ↔ z ≠ 0 ∧ z ≠ 5 ∧ z ≠ -7 := by
  simp [b65r_sourcePoles]

theorem b65x_cb_conj_eq (z w : ℂ) : (starRingEnd ℂ) z = w ↔ z = (starRingEnd ℂ) w :=
  ⟨fun h ↦ by rw [← h, Complex.conj_conj], fun h ↦ by rw [h, Complex.conj_conj]⟩

theorem b65x_cb_conj_notMem (z : ℂ) :
    (starRingEnd ℂ) z ∉ b65r_sourcePoles ↔ z ≠ 0 ∧ z ≠ 5 ∧ z ≠ -7 := by
  rw [b65x_cb_notMem]
  simp only [ne_eq, b65x_cb_conj_eq, map_zero, map_neg, map_ofNat]

/-- Complex conjugation from the plane minus the source poles to the downstairs plane.
Source: elementary plane geometry; the source poles 0, 5 and minus seven are real. -/
def b65x_cbConj : {z : ℂ // z ∉ b65r_sourcePoles} ≃ₜ b65x_Down where
  toFun z := ⟨(starRingEnd ℂ) z.val, (b65x_cb_notMem _).mp ((b65x_cb_conj_notMem z.val).mpr
    ((b65x_cb_notMem z.val).mp z.property))⟩
  invFun z := ⟨(starRingEnd ℂ) z.val, (b65x_cb_conj_notMem z.val).mpr z.property⟩
  left_inv z := Subtype.ext (Complex.conj_conj z.val)
  right_inv z := Subtype.ext (Complex.conj_conj z.val)
  continuous_toFun := (Complex.continuous_conj.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (Complex.continuous_conj.comp continuous_subtype_val).subtype_mk _

theorem b65x_cbConj_val (z : {z : ℂ // z ∉ b65r_sourcePoles}) :
    (b65x_cbConj z).val = (starRingEnd ℂ) z.val := rfl

theorem b65x_cb_pole (j : Fin 3) : ((b65r_sourcePole j : ℂ)) = (b65x_cutPoint j : ℂ) := by
  fin_cases j <;> simp [b65r_sourcePole, b65r_centres, b65x_cutPoint]

theorem b65x_cb_mem_cases {b : ℂ} (hb : b ∈ b65r_sourcePoles) :
    ∃ k : Fin 3, b = (b65x_cutPoint k : ℂ) := by
  simp only [b65r_sourcePoles, Set.mem_insert_iff, Set.mem_singleton_iff] at hb
  rcases hb with rfl | rfl | rfl
  · exact ⟨2, by simp [b65x_cutPoint]⟩
  · exact ⟨0, by simp [b65x_cutPoint]⟩
  · exact ⟨1, by simp [b65x_cutPoint]⟩

theorem b65x_cutPoint_injective : Function.Injective b65x_cutPoint := by
  intro i j h
  fin_cases i <;> fin_cases j <;> first | rfl | (norm_num [b65x_cutPoint] at h)

/-- A based loop made of a cut-free path, a path meeting only cut `j` once from left to right,
and a cut-free return path has crossing word `[(j, 1)]`.
Source: `b65x_CrossesAs`; Path.trans reparametrization. -/
theorem b65x_cb_crosses {y p q : b65x_Down} (α : Path y p) (σ : Path p q) (β : Path q y)
    (j : Fin 3) (t0 : ℝ) (h0 : 0 < t0) (h1 : t0 < 1)
    (hα : ∀ t k, ¬ b65x_OnCut k (α t).val) (hβ : ∀ t k, ¬ b65x_OnCut k (β t).val)
    (hσ : ∀ t k, b65x_OnCut k (σ t).val ↔ k = j ∧ (t : ℝ) = t0)
    (hlt : ∀ t : unitInterval, (t : ℝ) < t0 → (σ t).val.re < b65x_cutPoint j)
    (hgt : ∀ t : unitInterval, t0 < (t : ℝ) → b65x_cutPoint j < (σ t).val.re) :
    b65x_CrossesAs ((α.trans σ).trans β) [(j, 1)] := by
  have hu0 : (0 : ℝ) ≤ (1 + t0) / 4 := by linarith
  have hu1 : (1 + t0) / 4 ≤ 1 := by linarith
  let u : Fin 1 → unitInterval := fun _ ↦ ⟨(1 + t0) / 4, hu0, hu1⟩
  have hval : ∀ s : unitInterval, (1/4 : ℝ) < s → (s : ℝ) ≤ 1/2 →
      ∃ t : unitInterval, (t : ℝ) = 4 * s - 1 ∧ ((α.trans σ).trans β) s = σ t := by
    intro s hs1 hs2
    refine ⟨⟨4 * s - 1, by constructor <;> linarith⟩, rfl, ?_⟩
    rw [Path.trans_apply, dite_eq_left hs2, Path.trans_apply, dite_eq_right (by push_cast; linarith)]
    congr 1
    apply Subtype.ext
    push_cast
    ring
  have hout : ∀ s : unitInterval, ((s : ℝ) ≤ 1/4 ∨ 1/2 < (s : ℝ)) → ∀ k,
      ¬ b65x_OnCut k (((α.trans σ).trans β) s).val := by
    intro s hs k
    rw [Path.trans_apply]
    split_ifs with h
    · rw [Path.trans_apply, dite_eq_left (by push_cast; linarith [hs.resolve_right (by linarith)])]
      exact hα _ k
    · exact hβ _ k
  have hsub : ∀ a b : Fin [(j, (1 : ℤ))].length, a = b := fun a b ↦
    Fin.ext (by have := a.2; have := b.2; simp only [List.length_singleton] at *; omega)
  refine ⟨u, fun a b h ↦ absurd h (by rw [hsub a b]; exact lt_irrefl _),
    fun _ ↦ ⟨by simp [u]; linarith, by simp [u]; linarith⟩,
    fun m ↦ by rw [hsub m ⟨0, by simp⟩]; left; rfl, ?_, ?_⟩
  · intro k s
    constructor
    · intro hk
      by_cases hs : (1/4 : ℝ) < s ∧ (s : ℝ) ≤ 1/2
      · obtain ⟨t, ht, he⟩ := hval s hs.1 hs.2
        rw [he] at hk
        obtain ⟨rfl, ht0⟩ := (hσ t k).mp hk
        refine ⟨⟨0, by simp⟩, rfl, Subtype.ext ?_⟩
        simp only [u]
        linarith
      · exact absurd hk (hout s (by
          rcases not_and_or.mp hs with h | h
          · exact Or.inl (not_lt.mp h)
          · exact Or.inr (not_le.mp h)) k)
    · rintro ⟨m, hm, rfl⟩
      have hm0 : m = ⟨0, by simp⟩ := hsub _ _
      subst hm0
      obtain ⟨t, ht, he⟩ := hval (u ⟨0, by simp⟩) (by simp [u]; linarith) (by simp [u]; linarith)
      rw [he, hσ]
      refine ⟨hm.symm, ?_⟩
      rw [ht]
      simp [u]
      ring
  · refine ⟨min (t0 / 4) ((1 - t0) / 4), lt_min (by linarith) (by linarith), ?_⟩
    intro m s hs
    have hm0 : m = ⟨0, by simp⟩ := hsub _ _
    subst hm0
    have hs' := abs_lt.mp hs
    have hmin1 := min_le_left (t0 / 4) ((1 - t0) / 4)
    have hmin2 := min_le_right (t0 / 4) ((1 - t0) / 4)
    simp only [u] at hs'
    obtain ⟨t, ht, he⟩ := hval s (by linarith) (by linarith)
    have hw : ([(j, (1 : ℤ))][(⟨0, by simp⟩ : Fin [(j, (1 : ℤ))].length)] : Fin 3 × ℤ) =
      (j, 1) := rfl
    simp only [hw, u, Int.cast_one, one_mul, he]
    constructor
    · intro h
      have := hlt t (by rw [ht]; linarith)
      linarith
    · intro h
      have := hgt t (by rw [ht]; linarith)
      linarith


/-- Two paths with values in a convex subset of the punctured plane are homotopic.
Source: Mathlib, Convex.contractibleSpace and SimplyConnectedSpace.paths_homotopic. -/
theorem b65x_cb_convex_homotopic {A U : Set ℂ} (hU : Convex ℝ U) (hUA : ∀ z ∈ U, z ∉ A)
    {p q : {z : ℂ // z ∉ A}} (δ σ : Path p q) (hδ : ∀ t, (δ t : ℂ) ∈ U)
    (hσ : ∀ t, (σ t : ℂ) ∈ U) : δ.Homotopic σ := by
  have : ContractibleSpace U := hU.contractibleSpace ⟨_, hδ 0⟩
  let i : C(U, {z : ℂ // z ∉ A}) :=
    ⟨fun z ↦ ⟨z.1, hUA z.1 z.2⟩, continuous_subtype_val.subtype_mk _⟩
  have hp : (p : ℂ) ∈ U := by simpa using hδ 0
  have hq : (q : ℂ) ∈ U := by simpa using hδ 1
  let lift : (c : Path p q) → (∀ t, (c t : ℂ) ∈ U) →
      Path (⟨p, hp⟩ : U) ⟨q, hq⟩ := fun c hc ↦
    { toFun := fun t ↦ ⟨c t, hc t⟩
      continuous_toFun := (continuous_subtype_val.comp c.continuous).subtype_mk _
      source' := Subtype.ext (by simp)
      target' := Subtype.ext (by simp) }
  have h := (SimplyConnectedSpace.paths_homotopic (lift δ hδ) (lift σ hσ)).map i
  have h1 : (lift δ hδ).map i.continuous = δ := by ext t; rfl
  have h2 : (lift σ hσ).map i.continuous = σ := by ext t; rfl
  rwa [h1, h2] at h

/-- The straight segment between two points of the punctured plane, when it avoids the punctures.
Source: elementary plane geometry. -/
def b65x_cbSeg {A : Set ℂ} (p q : {z : ℂ // z ∉ A})
    (h : ∀ t : unitInterval, (p : ℂ) + ((t : ℝ) : ℂ) * ((q : ℂ) - p) ∉ A) : Path p q where
  toFun t := ⟨(p : ℂ) + ((t : ℝ) : ℂ) * ((q : ℂ) - p), h t⟩
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    fun_prop
  source' := Subtype.ext (by simp)
  target' := Subtype.ext (by simp)

theorem b65x_cbSeg_val {A : Set ℂ} (p q : {z : ℂ // z ∉ A}) (h) (t : unitInterval) :
    ((b65x_cbSeg p q h t : {z : ℂ // z ∉ A}) : ℂ) = (p : ℂ) + ((t : ℝ) : ℂ) * ((q : ℂ) - p) := rfl

theorem b65x_cb_pole_im {b : ℂ} (hb : b ∈ b65r_sourcePoles) : b.im = 0 := by
  obtain ⟨k, rfl⟩ := b65x_cb_mem_cases hb
  simp

theorem b65x_cb_cut_mem (k : Fin 3) : ((b65x_cutPoint k : ℝ) : ℂ) ∈ b65r_sourcePoles := by
  fin_cases k <;> simp [b65x_cutPoint, b65r_sourcePoles]

/-- Conjugating a positive circle about a real centre and reversing it gives the positive circle
about the same centre with conjugate radius vector.
Source: elementary plane geometry. -/
theorem b65x_cb_conj_circle (a : ℝ) (w : ℂ) (t : ℝ) :
    (starRingEnd ℂ) ((a : ℂ) + Complex.exp ((((1 - t) * (2 * Real.pi) : ℝ) : ℂ) * Complex.I) * w) =
      (a : ℂ) + Complex.exp ((((t : ℝ) * (2 * Real.pi) : ℝ) : ℂ) * Complex.I) *
        (starRingEnd ℂ) w := by
  rw [map_add, map_mul, Complex.conj_ofReal, ← Complex.exp_conj, map_mul, Complex.conj_ofReal,
    Complex.conj_I]
  congr 2
  have h : ((((1 - t) * (2 * Real.pi) : ℝ) : ℂ) * -Complex.I) =
      (((t * (2 * Real.pi) : ℝ) : ℂ) * Complex.I) - 2 * Real.pi * Complex.I := by
    push_cast
    ring
  rw [h, Complex.exp_sub, Complex.exp_two_pi_mul_I, div_one]


theorem b65x_cb_convex_pos {X Y t : ℝ} (hX : 0 < X) (hY : 0 < Y) (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    0 < (1 - t) * X + t * Y := by
  rcases h0.eq_or_lt with h | h
  · subst h; simpa using hX
  · nlinarith [mul_pos h hY, mul_nonneg (sub_nonneg.2 h1) hX.le]

/-- Conjugated cut loops of the upward slit system give once-crossing loops of the downward cuts,
a free basis and the printed local classes, with the outer relation in cut order 5, 0, minus seven.
Source: Hatcher, Algebraic Topology, §1.2; RiemannRochTop_cut_loops_universal_property,
RiemannRochTop_cut_inverse_positive_circle, RiemannRochTop_cut_family_outer_relation;
b65r_finite_peripheral_class and b65r_infinite_peripheral_class. -/
theorem b65x_cutBasis (x : {z : ℂ // z ∉ b65r_sourcePoles})
    (hx : ∀ b ∈ b65r_sourcePoles, (x : ℂ).re = b.re → (x : ℂ).im < b.im) :
    ∃ ℓ : Fin 3 → Path (b65x_cbConj x) (b65x_cbConj x),
      (∀ j, b65x_CrossesAs (ℓ j) [(j, 1)]) ∧
      (∀ (G : Type) [Group G] (v : Fin 3 → G),
        ∃! φ : FundamentalGroup b65x_Down (b65x_cbConj x) →* G,
          ∀ j, φ (FundamentalGroup.fromPath ⟦ℓ j⟧) = v j) ∧
      ∀ (M : FundamentalGroup b65x_Down (b65x_cbConj x) →*
          ((Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ))ˣ),
        (∀ p : Path (b65x_cbConj x) (b65x_cbConj x), (M (FundamentalGroup.fromPath ⟦p⟧)).val =
          b65f_transport (Fin 4 → ℂ) b65r_A (fun t ↦ (p.extend t).val)) →
        (∀ j, IsConj (b65r_printedOperatorHom (b4b_generators j.castSucc))
          (M (FundamentalGroup.fromPath ⟦ℓ j⟧))) ∧
        IsConj (b65r_printedOperatorHom (b4b_generators 3))
          (M (FundamentalGroup.fromPath ⟦ℓ 0⟧ * FundamentalGroup.fromPath ⟦ℓ 2⟧ *
            FundamentalGroup.fromPath ⟦ℓ 1⟧)⁻¹) := by
  have hA := b65r_sourcePoles_finite
  have hi := b65r_sourcePoles_re_inj
  have hne : b65r_sourcePoles.Nonempty := ⟨0, by simp [b65r_sourcePoles]⟩
  obtain ⟨ε, hε, hiso, γ₀, hgeom, -, hu⟩ :=
    RiemannRochTop_cut_loops_universal_property b65r_sourcePoles hA hi x hx
  obtain ⟨E, hE⟩ := RiemannRochTop_homeomorph_pi1_map b65x_cbConj x
  have hgeom' := hgeom
  choose p q α δ β hα hδ hβ hp hq hcl using hgeom'
  have hpb : ∀ a, |(p a : ℂ).re - (a : ℂ).re| < ε a ∧ (a : ℂ).im < (p a : ℂ).im := by
    intro a; simpa using hδ a 0
  have hqb : ∀ a, |(q a : ℂ).re - (a : ℂ).re| < ε a ∧ (a : ℂ).im < (q a : ℂ).im := by
    intro a; simpa using hδ a 1
  have hsegb : ∀ a (t : unitInterval),
      |((p a : ℂ) + ((t : ℝ) : ℂ) * ((q a : ℂ) - p a)).re - (a : ℂ).re| < ε a ∧
        (a : ℂ).im < ((p a : ℂ) + ((t : ℝ) : ℂ) * ((q a : ℂ) - p a)).im := by
    intro a t
    have ht0 := t.2.1
    have ht1 := t.2.2
    obtain ⟨hp1, hp2⟩ := hpb a
    obtain ⟨hq1, hq2⟩ := hqb a
    rw [abs_lt] at hp1 hq1 ⊢
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.sub_re, Complex.sub_im, zero_mul, sub_zero, Complex.add_im, Complex.mul_im,
      add_zero]
    have c1 := b65x_cb_convex_pos (by linarith : 0 < (p a : ℂ).re - (a : ℂ).re + ε a)
      (by linarith : 0 < (q a : ℂ).re - (a : ℂ).re + ε a) ht0 ht1
    have c2 := b65x_cb_convex_pos (by linarith : 0 < ε a - ((p a : ℂ).re - (a : ℂ).re))
      (by linarith : 0 < ε a - ((q a : ℂ).re - (a : ℂ).re)) ht0 ht1
    have c3 := b65x_cb_convex_pos (by linarith : 0 < (p a : ℂ).im - (a : ℂ).im)
      (by linarith : 0 < (q a : ℂ).im - (a : ℂ).im) ht0 ht1
    refine ⟨⟨by linarith, by linarith⟩, by linarith⟩
  have hsegA : ∀ a (t : unitInterval),
      (p a : ℂ) + ((t : ℝ) : ℂ) * ((q a : ℂ) - p a) ∉ b65r_sourcePoles := by
    intro a t hz
    have h := hiso a _ hz (hsegb a t).1
    have h2 := (hsegb a t).2
    rw [h] at h2
    exact lt_irrefl _ h2
  let σ : ∀ a, Path (p a) (q a) := fun a ↦ b65x_cbSeg (p a) (q a) (hsegA a)
  have hhom : ∀ a, (δ a).Homotopic (σ a) := by
    intro a
    refine b65x_cb_convex_homotopic (A := b65r_sourcePoles)
      (U := {z : ℂ | |z.re - (a : ℂ).re| < ε a ∧ (a : ℂ).im < z.im}) ?_ ?_ (δ a) (σ a)
      (hδ a) (hsegb a)
    · intro z hz w hw s r hs hr hsr
      simp only [Set.mem_ofPred_eq, abs_lt] at hz hw ⊢
      simp only [Complex.add_re, Complex.smul_re, Complex.add_im, Complex.smul_im, smul_eq_mul]
      have hr' : s = 1 - r := by linarith
      subst hr'
      have c1 := b65x_cb_convex_pos (by linarith : 0 < z.re - (a : ℂ).re + ε a)
        (by linarith : 0 < w.re - (a : ℂ).re + ε a) hr (by linarith)
      have c2 := b65x_cb_convex_pos (by linarith : 0 < ε a - (z.re - (a : ℂ).re))
        (by linarith : 0 < ε a - (w.re - (a : ℂ).re)) hr (by linarith)
      have c3 := b65x_cb_convex_pos (by linarith : 0 < z.im - (a : ℂ).im)
        (by linarith : 0 < w.im - (a : ℂ).im) hr (by linarith)
      refine ⟨⟨by linarith, by linarith⟩, by linarith⟩
    · intro z hz hzA
      have h := hiso a z hzA hz.1
      have h2 := hz.2
      rw [h] at h2
      exact lt_irrefl _ h2
  have hcl' : ∀ a, FundamentalGroup.fromPath ⟦((α a).trans (σ a)).trans (β a)⟧ = γ₀ a := by
    intro a
    rw [← hcl a]
    exact congrArg FundamentalGroup.fromPath (Quotient.sound
      (((Path.Homotopic.refl (α a)).hcomp (hhom a)).hcomp (Path.Homotopic.refl (β a))).symm)
  let H := b65x_cbConj
  let ℓ : Fin 3 → Path (H x) (H x) := fun j ↦
    (((α (b65r_sourcePole j)).trans (σ (b65r_sourcePole j))).trans
      (β (b65r_sourcePole j))).map H.continuous
  have hℓ : ∀ j, FundamentalGroup.fromPath ⟦ℓ j⟧ = E (γ₀ (b65r_sourcePole j)) := by
    intro j
    rw [← hcl', hE]
  let e3 := Equiv.ofBijective b65r_sourcePole b65r_sourcePole_bijective
  refine ⟨ℓ, ?_, ?_, ?_⟩
  · intro j
    set a := b65r_sourcePole j with ha
    have haj : (a : ℂ) = (b65x_cutPoint j : ℂ) := b65x_cb_pole j
    have hare : (a : ℂ).re = b65x_cutPoint j := by rw [haj]; simp
    have haim : (a : ℂ).im = 0 := by rw [haj]; simp
    have hdp : 0 < (q a : ℂ).re - (p a : ℂ).re := by linarith [hp a, hq a]
    change b65x_CrossesAs ((((α a).trans (σ a)).trans (β a)).map H.continuous) [(j, 1)]
    rw [Path.map_trans, Path.map_trans]
    have hre : ∀ t : unitInterval, (((σ a).map H.continuous) t).val.re =
        (p a : ℂ).re + (t : ℝ) * ((q a : ℂ).re - (p a : ℂ).re) := by
      intro t
      change ((starRingEnd ℂ) ((p a : ℂ) + ((t : ℝ) : ℂ) * ((q a : ℂ) - p a))).re = _
      simp
    have him : ∀ t : unitInterval, (((σ a).map H.continuous) t).val.im < 0 := by
      intro t
      have h := (hsegb a t).2
      rw [haim] at h
      change ((starRingEnd ℂ) ((p a : ℂ) + ((t : ℝ) : ℂ) * ((q a : ℂ) - p a))).im < 0
      rw [Complex.conj_im]
      linarith
    refine b65x_cb_crosses _ _ _ j (((a : ℂ).re - (p a : ℂ).re) / ((q a : ℂ).re - (p a : ℂ).re))
      (div_pos (by linarith [hp a]) hdp) ((div_lt_one hdp).mpr (by linarith [hq a])) ?_ ?_ ?_ ?_ ?_
    · intro t k hk
      obtain ⟨hk1, hk2⟩ := hk
      change ((starRingEnd ℂ) (α a t : ℂ)).re = _ at hk1
      change ((starRingEnd ℂ) (α a t : ℂ)).im < 0 at hk2
      have h := hα a t _ (b65x_cb_cut_mem k) (by simpa using hk1)
      simp only [Complex.conj_im, Complex.ofReal_im] at hk2 h
      linarith
    · intro t k hk
      obtain ⟨hk1, hk2⟩ := hk
      change ((starRingEnd ℂ) (β a t : ℂ)).re = _ at hk1
      change ((starRingEnd ℂ) (β a t : ℂ)).im < 0 at hk2
      have h := hβ a t _ (b65x_cb_cut_mem k) (by simpa using hk1)
      simp only [Complex.conj_im, Complex.ofReal_im] at hk2 h
      linarith
    · intro t k
      unfold b65x_OnCut
      rw [hre t]
      constructor
      · rintro ⟨h1, -⟩
        have hb := (hsegb a t).1
        have hre' : ((p a : ℂ) + ((t : ℝ) : ℂ) * ((q a : ℂ) - p a)).re =
            (p a : ℂ).re + (t : ℝ) * ((q a : ℂ).re - (p a : ℂ).re) := by simp
        rw [hre', h1] at hb
        have hk := hiso a _ (b65x_cb_cut_mem k) (by simpa using hb)
        rw [haj] at hk
        have hkj : k = j := b65x_cutPoint_injective (by exact_mod_cast hk)
        refine ⟨hkj, ?_⟩
        subst hkj
        rw [eq_div_iff hdp.ne', hare]
        linarith
      · rintro ⟨rfl, ht⟩
        refine ⟨?_, him t⟩
        rw [ht, ← hare]
        field_simp
        ring
    · intro t ht
      rw [hre t, ← hare]
      rw [lt_div_iff₀ hdp] at ht
      linarith
    · intro t ht
      rw [hre t, ← hare]
      rw [div_lt_iff₀ hdp] at ht
      linarith
  · intro G _ v
    obtain ⟨φ, hφ, huniq⟩ := hu G (fun a ↦ v (e3.symm a))
    refine ⟨φ.comp E.symm.toMonoidHom, ?_, ?_⟩
    · intro j
      change φ (E.symm (FundamentalGroup.fromPath ⟦ℓ j⟧)) = v j
      rw [hℓ, MulEquiv.symm_apply_apply, hφ]
      exact congrArg v (e3.symm_apply_apply j)
    · intro ψ hψ
      have heq : ψ.comp E.toMonoidHom = φ := by
        apply huniq
        intro a
        obtain ⟨j, rfl⟩ := e3.surjective a
        simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
        change ψ (E (γ₀ (b65r_sourcePole j))) = v (e3.symm (e3 j))
        rw [← hℓ, hψ, e3.symm_apply_apply]
      ext g
      have h := congrArg (fun f ↦ f (E.symm g)) heq
      simpa using h
  · intro M hM
    refine ⟨fun j ↦ ?_, ?_⟩
    · obtain ⟨w, hw, hnorm, hdisk, y', k, c, -, hc, hclass⟩ :=
        RiemannRochTop_cut_inverse_positive_circle b65r_sourcePoles hA (b65r_sourcePole j)
          (b65r_sourcePole j).2 (ε (b65r_sourcePole j)) (hε _)
          (fun b hb h ↦ hiso _ b hb h) (α _) (δ _) (β _) (fun t b hb ↦ hα _ t b hb) (hδ _)
          (fun t b hb ↦ hβ _ t b hb) (hp _) (hq _)
      rw [hcl] at hclass
      let k' := k.map H.continuous
      let c' := c.map H.continuous
      have hcls : FundamentalGroup.fromPath ⟦ℓ j⟧ =
          FundamentalGroup.fromPath ⟦(k'.trans c'.symm).trans k'.symm⟧ := by
        rw [RiemannRochTop_based_reverse_class, hℓ, ← inv_inv (γ₀ (b65r_sourcePole j)),
          ← hclass, map_inv, hE, Path.map_trans, Path.map_trans, Path.map_symm]
      refine b65r_finite_peripheral_class (H x) M hM j _ ⟨ε (b65r_sourcePole j),
        (starRingEnd ℂ) w, (map_ne_zero _).mpr hw, by rwa [Complex.norm_conj], hdisk, H y', k',
        c'.symm, ?_, hcls.symm⟩
      intro t
      change (starRingEnd ℂ) (c (unitInterval.symm t) : ℂ) = _
      rw [hc, unitInterval.coe_symm_eq, b65x_cb_pole]
      exact b65x_cb_conj_circle _ w t
    · obtain ⟨n, e, R, L, hR, hRL, hbound, he, x', k, c, -, hc, hclass⟩ :=
        RiemannRochTop_cut_family_outer_relation b65r_sourcePoles hA hne hi ε hε hiso x hx γ₀
          hgeom
      have hcard : Nat.card b65r_sourcePoles = 3 := by
        rw [Nat.card_coe_set_eq]
        exact Set.ncard_eq_three.mpr ⟨0, 5, -7, by norm_num, by norm_num, by norm_num, rfl⟩
      have hn : n + 1 = 3 := by
        rw [← hcard, ← Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_fin]
      obtain rfl : n = 2 := by omega
      have hmem : ∀ i, (e i : ℂ) = 0 ∨ (e i : ℂ) = 5 ∨ (e i : ℂ) = -7 := by
        intro i
        have := (e i).2
        simp only [b65r_sourcePoles, Set.mem_insert_iff, Set.mem_singleton_iff] at this
        exact this
      have h01 := he (show (0 : Fin 3) < 1 by decide)
      have h12 := he (show (1 : Fin 3) < 2 by decide)
      simp only at h01 h12
      have hvals : (e 0 : ℂ) = -7 ∧ (e 1 : ℂ) = 0 ∧ (e 2 : ℂ) = 5 := by
        rcases hmem 0 with h0 | h0 | h0 <;> rcases hmem 1 with h1 | h1 | h1 <;>
          rcases hmem 2 with h2 | h2 | h2 <;> first | exact ⟨h0, h1, h2⟩ |
            (revert h01 h12; norm_num [h0, h1, h2])
      have he0 : e 0 = b65r_sourcePole 1 := Subtype.ext (by
        rw [hvals.1, b65x_cb_pole]; simp [b65x_cutPoint])
      have he1 : e 1 = b65r_sourcePole 2 := Subtype.ext (by
        rw [hvals.2.1, b65x_cb_pole]; simp [b65x_cutPoint])
      have he2 : e 2 = b65r_sourcePole 0 := Subtype.ext (by
        rw [hvals.2.2, b65x_cb_pole]; simp [b65x_cutPoint])
      simp only [List.ofFn_succ, List.ofFn_zero, Fin.succ_zero_eq_one, Fin.succ_one_eq_two,
        List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
        List.prod_cons, List.prod_nil, mul_one, he0, he1, he2] at hclass
      let k' := k.map H.continuous
      let d := (c.map H.continuous).symm
      have hcls : FundamentalGroup.fromPath ⟦(k'.trans d).trans k'.symm⟧ =
          FundamentalGroup.fromPath ⟦ℓ 0⟧ * FundamentalGroup.fromPath ⟦ℓ 2⟧ *
            FundamentalGroup.fromPath ⟦ℓ 1⟧ := by
        have h := congrArg E hclass
        rw [hE, Path.map_trans, Path.map_trans, ← Path.map_symm, ← Path.map_symm] at h
        rw [hℓ, hℓ, hℓ, mul_assoc, ← map_mul, ← map_mul]
        exact h
      refine b65r_infinite_peripheral_class (H x) M hM _ R L hR hRL hbound (H x') k' d ?_ ?_
      · intro t
        change (starRingEnd ℂ) (c (unitInterval.symm t) : ℂ) = _
        rw [hc, unitInterval.coe_symm_eq]
        have h := b65x_cb_conj_circle 0 (L : ℂ) t
        simpa using h
      · exact (RiemannRochTop_based_reverse_class k' d).trans (by rw [hcls])

/-- A conjugated base point off the downward cuts lies off the upward slits.
Source: `b65x_OnCut`; the source poles are real. -/
theorem b65x_cb_offCut (x : {z : ℂ // z ∉ b65r_sourcePoles})
    (hy : ∀ k, ¬ b65x_OnCut k (b65x_cbConj x).val) :
    ∀ b ∈ b65r_sourcePoles, (x : ℂ).re = b.re → (x : ℂ).im < b.im := by
  intro b hb hre
  obtain ⟨k, rfl⟩ := b65x_cb_mem_cases hb
  have hk := hy k
  simp only [b65x_OnCut, b65x_cbConj_val, Complex.conj_re, Complex.conj_im, not_and,
    not_lt] at hk
  have hre' : (x : ℂ).re = b65x_cutPoint k := by simpa using hre
  have him := hk hre'
  simp only [Complex.ofReal_im]
  rcases (neg_nonneg.mp him).lt_or_eq with h | h
  · exact h
  · exfalso
    have hxk : (x : ℂ) = (b65x_cutPoint k : ℂ) :=
      Complex.ext (by simpa using hre') (by simpa using h)
    have hm := b65x_cb_cut_mem k
    rw [← hxk] at hm
    exact x.property hm

end HodgeLean.Foundations.Program
