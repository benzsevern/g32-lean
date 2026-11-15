import HodgeLean.Foundations.AppellHumbertDefs

/-! Proof obligations for the frozen Appell--Humbert core spec. -/

noncomputable section

namespace HodgeLean.Foundations.AppellHumbert

section Lattice

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]

omit [FiniteDimensional ℂ V] in
theorem spec_appellHumbert_factor_cocycle_aux (D : Datum (V := V)) (l m : D.lattice) (v : V) :
    factor D (l + m) v = factor D l (v + m) * factor D m v := by
  obtain ⟨n, hn⟩ := D.integral l m
  have hsymm : D.hermitian.toFun (m : V) l = star (D.hermitian.toFun l m) :=
    (D.hermitian.conj_symm m l).symm
  unfold factor
  rw [D.semicharacter_add, Submodule.coe_add, Circle.coe_mul, Circle.coe_mul, Circle.coe_exp,
    D.hermitian.add_right, D.hermitian.add_left, D.hermitian.add_left, D.hermitian.add_right,
    D.hermitian.add_right, hsymm]
  have key : ∀ a b c d : ℂ, a * Complex.exp b * Complex.exp c * Complex.exp d =
      a * Complex.exp (b + c + d) := by
    intro a b c d; rw [Complex.exp_add, Complex.exp_add]; ring
  calc _ = (D.semicharacter l : ℂ) * (D.semicharacter m : ℂ) * Complex.exp
        (↑(Real.pi * D.hermitian.imaginary l m) * Complex.I +
          (↑Real.pi * (D.hermitian.toFun v l + D.hermitian.toFun v m) +
            ↑Real.pi / 2 * (D.hermitian.toFun l l + D.hermitian.toFun l m +
              (star (D.hermitian.toFun l m) + D.hermitian.toFun m m)))) := by
          rw [mul_assoc _ (Complex.exp _), ← Complex.exp_add]
    _ = (D.semicharacter l : ℂ) * (D.semicharacter m : ℂ) * Complex.exp
        ((↑Real.pi * (D.hermitian.toFun v l + star (D.hermitian.toFun l m)) +
            ↑Real.pi / 2 * D.hermitian.toFun l l) +
          (↑Real.pi * D.hermitian.toFun v m + ↑Real.pi / 2 * D.hermitian.toFun m m) +
          n * (2 * Real.pi * Complex.I)) := by
          congr 2
          rw [HermitianForm.imaginary] at hn ⊢
          apply Complex.ext <;>
            simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
              Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.star_def,
              Complex.conj_re, Complex.conj_im, Complex.div_ofNat_re, Complex.div_ofNat_im,
              Complex.intCast_re, Complex.intCast_im, Complex.re_ofNat, Complex.im_ofNat, hn] <;>
            ring
    _ = _ := by
          rw [Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one, Complex.exp_add]
          ring

theorem spec_rational11_clear_denominators_aux (L : Submodule ℤ V) [DiscreteTopology L]
    (hL : IsZLattice ℝ L) (E : V → V → ℝ)
    (hadd₁ : ∀ x y z, E (x + y) z = E x z + E y z)
    (hsmul₁ : ∀ (r : ℝ) x y, E (r • x) y = r * E x y)
    (hadd₂ : ∀ x y z, E x (y + z) = E x y + E x z)
    (hsmul₂ : ∀ (r : ℝ) x y, E x (r • y) = r * E x y)
    (halt : ∀ x, E x x = 0)
    (hrat : ∀ l m : L, ∃ q : ℚ, E l m = q) (h11 : IsTypeOneOne E) :
    ∃ N : ℕ, 0 < N ∧ (∀ l m : L, ∃ n : ℤ, (N : ℝ) * E l m = n) ∧
      IsTypeOneOne (fun v w ↦ (N : ℝ) * E v w) := by
  have : Module.Free ℤ L := ZLattice.module_free ℝ L
  have : Module.Finite ℤ L := ZLattice.module_finite ℝ L
  let b := Module.Free.chooseBasis ℤ L
  choose q hq using fun i j ↦ hrat (b i) (b j)
  refine ⟨∏ i, ∏ j, (q i j).den, ?_, ?_, ?_⟩
  · exact Finset.prod_pos fun i _ ↦ Finset.prod_pos fun j _ ↦ (q i j).den_pos
  · set N := ∏ i, ∏ j, (q i j).den
    have hzl : ∀ y, E 0 y = 0 := fun y ↦ by simpa using hsmul₁ 0 0 y
    have hzr : ∀ x, E x 0 = 0 := fun x ↦ by simpa using hsmul₂ 0 x 0
    have hzs₁ : ∀ (k : ℤ) (x : L) y, E ((k • x : L) : V) y = k * E x y := fun k x y ↦ by
      rw [Submodule.coe_smul, ← Int.cast_smul_eq_zsmul ℝ, hsmul₁]
    have hzs₂ : ∀ (k : ℤ) x (y : L), E x ((k • y : L) : V) = k * E x y := fun k x y ↦ by
      rw [Submodule.coe_smul, ← Int.cast_smul_eq_zsmul ℝ, hsmul₂]
    have hbasis : ∀ i j, ∃ n : ℤ, (N : ℝ) * E (b i) (b j) = n := by
      intro i j
      obtain ⟨k, hk⟩ : (q i j).den ∣ N :=
        (Finset.dvd_prod_of_mem _ (Finset.mem_univ j)).trans
          (Finset.dvd_prod_of_mem (fun i ↦ ∏ j, (q i j).den) (Finset.mem_univ i))
      refine ⟨k * (q i j).num, ?_⟩
      rw [hq, hk]
      have := Rat.mul_den_eq_num (q i j)
      have h' : ((q i j : ℝ) * (q i j).den) = (q i j).num := by exact_mod_cast this
      push_cast
      rw [← h']; ring
    have hspan : ∀ x : L, x ∈ Submodule.span ℤ (Set.range b) := fun x ↦ by
      rw [b.span_eq]; trivial
    intro l m
    induction hspan l using Submodule.span_induction generalizing m with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      induction hspan m using Submodule.span_induction with
      | mem y hy => obtain ⟨j, rfl⟩ := hy; exact hbasis i j
      | zero => exact ⟨0, by simp [hzr]⟩
      | add y z _ _ hy hz =>
        obtain ⟨a, ha⟩ := hy; obtain ⟨c, hc⟩ := hz
        exact ⟨a + c, by rw [Submodule.coe_add, hadd₂]; push_cast; rw [← ha, ← hc]; ring⟩
      | smul k y _ hy =>
        obtain ⟨a, ha⟩ := hy
        exact ⟨k * a, by rw [hzs₂]; push_cast; rw [← ha]; ring⟩
    | zero => exact ⟨0, by simp [hzl]⟩
    | add x y _ _ hx hy =>
      obtain ⟨a, ha⟩ := hx m; obtain ⟨c, hc⟩ := hy m
      exact ⟨a + c, by rw [Submodule.coe_add, hadd₁]; push_cast; rw [← ha, ← hc]; ring⟩
    | smul k x _ hx =>
      obtain ⟨a, ha⟩ := hx m
      exact ⟨k * a, by rw [hzs₁]; push_cast; rw [← ha]; ring⟩
  · intro v w
    simp only [h11 v w]

end Lattice

section Forms

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [Module ℂ V]
  [IsScalarTower ℝ ℂ V]

omit [Module ℝ V] [IsScalarTower ℝ ℂ V] in
/-- The imaginary part of a Hermitian form is invariant under the complex structure. -/
theorem isTypeOneOne_imaginary (H : HermitianForm (V := V)) : IsTypeOneOne H.imaginary := by
  intro v w
  simp only [HermitianForm.imaginary, H.smul_left, H.smul_right, ← mul_assoc,
    Complex.star_def, Complex.conj_I, neg_mul, Complex.I_mul_I, neg_neg, one_mul]

/-- A complex scalar acts as its real part plus its imaginary part times `i`. -/
theorem complex_smul_eq (c : ℂ) (x : V) :
    c • x = c.re • x + c.im • (Complex.I • x) := by
  conv_lhs => rw [← Complex.re_add_im c]
  have h : ∀ (r : ℝ) (y : V), (r : ℂ) • y = r • y := fun r y ↦ by
    rw [← algebraMap_smul ℂ r y]; rfl
  rw [add_smul, mul_smul, h, h]

omit [Module ℝ V] [IsScalarTower ℝ ℂ V] in
/-- Applying the complex structure twice is negation. -/
theorem I_smul_I_smul (x : V) : Complex.I • Complex.I • x = -x := by
  rw [smul_smul, Complex.I_mul_I, neg_one_smul]

theorem spec_appellHumbert_riemann_relations_aux (E : V → V → ℝ)
    (hadd₁ : ∀ x y z, E (x + y) z = E x z + E y z)
    (hsmul₁ : ∀ (r : ℝ) x y, E (r • x) y = r * E x y)
    (hadd₂ : ∀ x y z, E x (y + z) = E x y + E x z)
    (hsmul₂ : ∀ (r : ℝ) x y, E x (r • y) = r * E x y)
    (halt : ∀ x, E x x = 0) :
    (∃ H : HermitianForm (V := V), H.imaginary = E) ↔ IsTypeOneOne E := by
  constructor
  · rintro ⟨H, rfl⟩
    exact isTypeOneOne_imaginary H
  · intro h11
    have hneg₁ : ∀ x y, E (-x) y = -E x y := fun x y ↦ by
      simpa using hsmul₁ (-1) x y
    have hneg₂ : ∀ x y, E x (-y) = -E x y := fun x y ↦ by
      simpa using hsmul₂ (-1) x y
    have hanti : ∀ x y, E y x = -E x y := fun x y ↦ by
      have := halt (x + y)
      rw [hadd₁, hadd₂, hadd₂, halt, halt] at this
      linarith
    have hIl : ∀ x y, E (Complex.I • x) y = -E x (Complex.I • y) := fun x y ↦ by
      rw [← h11, I_smul_I_smul, hneg₁]
    have hcl : ∀ (c : ℂ) x y, E (c • x) y = c.re * E x y + c.im * E (Complex.I • x) y :=
      fun c x y ↦ by rw [complex_smul_eq, hadd₁, hsmul₁, hsmul₁]
    have hcr : ∀ (c : ℂ) x y, E x (c • y) = c.re * E x y + c.im * E x (Complex.I • y) :=
      fun c x y ↦ by rw [complex_smul_eq, hadd₂, hsmul₂, hsmul₂]
    have hIc : ∀ (c : ℂ) (x : V), Complex.I • c • x = c • Complex.I • x := fun c x ↦ by
      rw [smul_smul, smul_smul, mul_comm]
    refine ⟨{
      toFun := fun v w ↦ ⟨-E (Complex.I • v) w, E v w⟩
      add_left := fun x y z ↦ by
        apply Complex.ext <;> simp only [smul_add, hadd₁, Complex.add_re, Complex.add_im]
        ring
      smul_left := fun c x y ↦ by
        apply Complex.ext <;>
          simp only [Complex.mul_re, Complex.mul_im, Complex.star_def, Complex.conj_re,
            Complex.conj_im]
        · rw [hIc, hcl c (Complex.I • x) y, I_smul_I_smul, hneg₁]; ring
        · rw [hcl c x y]; ring
      add_right := fun x y z ↦ by
        apply Complex.ext <;> simp only [hadd₂, Complex.add_re, Complex.add_im]
        ring
      smul_right := fun c x y ↦ by
        apply Complex.ext <;> simp only [Complex.mul_re, Complex.mul_im]
        · rw [hcr c (Complex.I • x) y, h11]; ring
        · rw [hcr c x y, hIl]; ring
      conj_symm := fun x y ↦ by
        apply Complex.ext <;>
          simp only [Complex.star_def, Complex.conj_re, Complex.conj_im]
        · rw [hIl y x, hanti (Complex.I • x) y]; ring
        · rw [hanti x y]; ring }, ?_⟩
    rfl

omit [Module ℝ V] [IsScalarTower ℝ ℂ V] in
theorem spec_positive_imaginary_nondegenerate_aux (H : HermitianForm (V := V))
    (hH : H.IsPositiveDefinite) : IsNondegenerate H.imaginary := by
  intro v hv
  by_contra hne
  have h1 := hv (Complex.I • v)
  rw [HermitianForm.imaginary, H.smul_right, Complex.mul_im, Complex.I_re, Complex.I_im] at h1
  have h2 := hH v hne
  simp only [zero_mul, one_mul, zero_add] at h1
  linarith

theorem spec_degenerate_semipositive_counterexample_aux :
    (∀ v, 0 ≤ (degenerateForm.toFun v v).re) ∧ ¬ degenerateForm.IsPositiveDefinite ∧
      ¬ IsNondegenerate degenerateForm.imaginary := by
  have hv : (![0, 1] : Fin 2 → ℂ) ≠ 0 := fun h ↦ by
    simpa using congrFun h 1
  refine ⟨fun v ↦ ?_, fun h ↦ ?_, fun h ↦ ?_⟩
  · show 0 ≤ (star (v 0) * v 0).re
    rw [Complex.star_def, mul_comm, Complex.mul_conj, Complex.ofReal_re]
    exact Complex.normSq_nonneg _
  · have := h _ hv
    simp [degenerateForm] at this
  · exact hv (h _ fun w ↦ by simp [degenerateForm, HermitianForm.imaginary])

theorem spec_form_nondegenerate_to_symplectic_aux
    {W : Type*} [AddCommGroup W] [Module ℝ W] [FiniteDimensional ℝ W]
    (E : Module.Dual ℝ W → Module.Dual ℝ W → ℝ) (ω : ⋀[ℝ]^2 W)
    (hmodel : ∀ φ ψ, E φ ψ = ψ (Symplectic.contract ω φ))
    (hE : IsNondegenerate E) : Symplectic.IsNondegenerate ω := by
  have hinj : Function.Injective (Symplectic.contract ω) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro φ hφ
    exact hE φ fun ψ ↦ by rw [hmodel, hφ, map_zero]
  exact ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (Subspace.dual_finrank_eq)).mp hinj⟩

theorem spec_nonRiemann_form_counterexample_aux :
    let E : (Fin 2 → ℂ) → (Fin 2 → ℂ) → ℝ :=
      fun v w ↦ (v 0).re * (w 1).re - (v 1).re * (w 0).re
    (∀ v, E v v = 0) ∧ ¬ IsTypeOneOne E ∧
      ¬ ∃ H : HermitianForm (V := Fin 2 → ℂ), H.imaginary = E := by
  intro E
  have hnot : ¬ IsTypeOneOne E := fun h ↦ by
    have := h ![1, 0] ![0, 1]
    simp [E] at this
  refine ⟨fun v ↦ by simp only [E]; ring, hnot, ?_⟩
  rintro ⟨H, hH⟩
  exact hnot (hH ▸ isTypeOneOne_imaginary H)

theorem spec_elliptic_degree_one_aux :
    let E : ℂ → ℂ → ℝ := fun z w ↦ z.re * w.im - z.im * w.re
    IsTypeOneOne E ∧ E 1 Complex.I = 1 := by
  intro E
  refine ⟨fun z w ↦ ?_, by simp [E]⟩
  simp only [E, smul_eq_mul, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
  ring

end Forms

end HodgeLean.Foundations.AppellHumbert
