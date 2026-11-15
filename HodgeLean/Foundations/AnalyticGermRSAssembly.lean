import HodgeLean.Foundations.AnalyticGermRSAssemblyProofs

/-! # Homogeneous cone projection and vertex extension

Implication from punctured homogeneous analytic cone data to a finite pure
cover of the cone, from a pure cone to a surjective finite proper whole-cone
projection, and from such a projection to vertex analyticity, glued over the
finite cover. The six confinement and sheet interfaces and the attained
dimension projection are preserved.
HC no distance; AV milestone no distance.
-/

noncomputable section
open Set Filter Topology Polynomial
open HodgeLean.Foundations.AnalyticDivisorAlgebraic6
namespace HodgeLean.Foundations

/-- Source: Demailly, Complex Analytic and Differential Geometry (2012), II, Theorem 5.9, p. 104. -/
theorem adim9_compact_analytic_finite (n : ℕ) (K : Set (Fin n → ℂ))
    (hK : IsCompact K)
    (hloc : ∀ x ∈ K, ∃ U : Set (Fin n → ℂ), IsOpen U ∧ x ∈ U ∧
      ∃ (m : ℕ) (f : Fin m → (Fin n → ℂ) → ℂ),
        (∀ j, AnalyticOnNhd ℂ (f j) U) ∧
        ∀ z ∈ U, (z ∈ K ↔ ∀ j, f j z = 0)) :
    K.Finite :=
  adim9_compact_analytic_finite_aux n K hK hloc

/-- The boundary input concerns the missing origin, not a germ at a point of A.
Source: Demailly, Complex Analytic and Differential Geometry (2012),
II, proof of Theorem 8.7, pp. 119--120, boundary separation and compact fibres. -/
theorem adim9_punctured_confinement (n d : ℕ) (A : Set (Fin n → ℂ))
    (hzero : (0 : Fin n → ℂ) ∉ A)
    (hclosed : IsClosed {z : {z : Fin n → ℂ // z ≠ 0} | z.val ∈ A})
    (hloc : ∀ x ∈ A, ∃ U : Set (Fin n → ℂ), IsOpen U ∧ x ∈ U ∧
      U ⊆ {z | z ≠ 0} ∧ ∃ (m : ℕ) (f : Fin m → (Fin n → ℂ) → ℂ),
        (∀ j, AnalyticOnNhd ℂ (f j) U) ∧
        ∀ z ∈ U, (z ∈ A ↔ ∀ j, f j z = 0))
    (π : (Fin n → ℂ) →L[ℂ] (Fin d → ℂ)) (R : ℝ) (hR : 0 < R)
    (hboundary : ∀ z ∈ closure A, ‖z‖ = R → π z ≠ 0) :
    ∃ ε : ℝ, 0 < ε ∧
      ∃ p : {z : Fin n → ℂ // z ∈ A ∧ ‖z‖ < R ∧ ‖π z‖ < ε ∧ π z ≠ 0} →
        {w : Fin d → ℂ // ‖w‖ < ε ∧ w ≠ 0},
        (∀ z, (p z).val = π z.val) ∧ IsProperMap p ∧
        ∀ w, (p ⁻¹' {w}).Finite :=
  adim9_punctured_confinement_aux n d A hzero hclosed hloc π R hR hboundary

/-- The polynomial is constructed from the actual finite fibre, without a global root labeling.
Source: Gunning--Rossi, III.C, symmetric functions of local sheets;
Demailly, Complex Analytic and Differential Geometry (2012), II, proof of Theorem 8.7, p. 120. -/
theorem adim9_sheet_coefficients (n d k : ℕ) (D : Set (Fin d → ℂ))
    (s : (Fin d → ℂ) → Finset (Fin n → ℂ))
    (hsheets : ∀ x ∈ D, ∃ (W : Set (Fin d → ℂ))
      (r : Fin k → (Fin d → ℂ) → (Fin n → ℂ)),
      IsOpen W ∧ x ∈ W ∧ W ⊆ D ∧ (∀ j, AnalyticOnNhd ℂ (r j) W) ∧
      ∀ y ∈ W, Function.Injective (fun j ↦ r j y) ∧
        ∀ z, z ∈ s y ↔ ∃ j, r j y = z)
    (ℓ : (Fin n → ℂ) →L[ℂ] ℂ) (R : ℝ) (hR : 0 ≤ R)
    (hbound : ∀ x ∈ D, ∀ z ∈ s x, ‖ℓ z‖ ≤ R) :
    (∀ i : ℕ, AnalyticOnNhd ℂ (fun x ↦ (adim9_fibrePolynomial n (s x) ℓ).coeff i) D) ∧
    ∀ x ∈ D, (adim9_fibrePolynomial n (s x) ℓ).Monic ∧
      (adim9_fibrePolynomial n (s x) ℓ).natDegree = k ∧
      (∀ i : ℕ, ‖(adim9_fibrePolynomial n (s x) ℓ).coeff i‖ ≤ (1 + R) ^ k) ∧
      ∀ t : ℂ, (adim9_fibrePolynomial n (s x) ℓ).eval t = 0 ↔
        ∃ z ∈ s x, ℓ z = t :=
  adim9_sheet_coefficients_aux n d k D s hsheets ℓ R hR hbound

/-- A clopen part of a finite analytic cover has a constant number of sheets on a connected base.
Source: Gunning--Rossi, III.C, unramified local parametrization and monodromy. -/
theorem adim9_clopen_sheet_selection (n d k : ℕ) (D : Set (Fin d → ℂ))
    (hconn : IsConnected D) (s : (Fin d → ℂ) → Finset (Fin n → ℂ))
    (hsheets : ∀ x ∈ D, ∃ (W : Set (Fin d → ℂ))
      (r : Fin k → (Fin d → ℂ) → (Fin n → ℂ)),
      IsOpen W ∧ x ∈ W ∧ W ⊆ D ∧ (∀ j, AnalyticOnNhd ℂ (r j) W) ∧
      ∀ y ∈ W, Function.Injective (fun j ↦ r j y) ∧
        ∀ z, z ∈ s y ↔ ∃ j, r j y = z)
    (S : Set ((Fin d → ℂ) × (Fin n → ℂ)))
    (hS : IsClopen (((↑) : {p : (Fin d → ℂ) × (Fin n → ℂ) |
      p.1 ∈ D ∧ p.2 ∈ s p.1} → (Fin d → ℂ) × (Fin n → ℂ)) ⁻¹' S)) :
    ∃ l : ℕ, l ≤ k ∧ ∀ x ∈ D, ∃ (W : Set (Fin d → ℂ))
      (r : Fin l → (Fin d → ℂ) → (Fin n → ℂ)),
      IsOpen W ∧ x ∈ W ∧ W ⊆ D ∧ (∀ j, AnalyticOnNhd ℂ (r j) W) ∧
      ∀ y ∈ W, Function.Injective (fun j ↦ r j y) ∧
        ∀ z, (z ∈ s y ∧ (y, z) ∈ S) ↔ ∃ j, r j y = z :=
  adim9_clopen_sheet_selection_aux n d k D hconn s hsheets S hS

/-- Using all linear observables retains the coupling between fibre coordinates.
Source: Demailly, Complex Analytic and Differential Geometry (2012),
II, proof of Theorem 8.7, p. 120; finite avoidance of proper linear hyperplanes. -/
theorem adim9_linear_observables_separate (n : ℕ) (s : Finset (Fin n → ℂ)) (z : Fin n → ℂ) :
    (∀ ℓ : (Fin n → ℂ) →L[ℂ] ℂ,
      (adim9_fibrePolynomial n s ℓ).eval (ℓ z) = 0) ↔ z ∈ s :=
  adim9_linear_observables_separate_aux n s z

/-- Source: Chirka, Complex Analytic Sets, §§3--4, generic linear projections;
Baire category applied to the dual of a finite-dimensional complex vector space. -/
theorem adim9_countable_linear_avoidance (n : ℕ) (S : Set (Fin n → ℂ))
    (hcount : S.Countable) (hzero : (0 : Fin n → ℂ) ∉ S) :
    ∃ ℓ : (Fin n → ℂ) →L[ℂ] ℂ, ∀ z ∈ S, ℓ z ≠ 0 :=
  adim9_countable_linear_avoidance_aux n S hcount hzero

/-- W1: two distinct points are the zeros of a quadratic on the complex line.
Source: Demailly, II, Theorem 5.9. -/
example : ({0, 1} : Set (Fin 1 → ℂ)).Finite := by
  apply adim9_compact_analytic_finite 1 {0, 1}
    (isCompact_singleton.insert 0)
  intro x hx
  refine ⟨univ, isOpen_univ, mem_univ x, 1,
    (fun _ z ↦ z 0 * (z 0 - 1)), ?_, ?_⟩
  · intro j
    have h := (ContinuousLinearMap.proj (R := ℂ)
      (φ := fun _ : Fin 1 ↦ ℂ) 0).analyticOnNhd univ
    exact h.mul (h.sub analyticOnNhd_const)
  · intro z _
    simp only [mem_insert_iff, mem_singleton_iff, mul_eq_zero, sub_eq_zero]
    constructor
    · rintro (rfl | rfl) j
      · exact Or.inl rfl
      · exact Or.inr rfl
    · intro h
      rcases h 0 with h | h
      · left; ext i; fin_cases i; exact h
      · right; ext i; fin_cases i; exact h

/-- W2: coefficients of the cusp parametrization on the unit parameter disc.
This tests actual analytic sheets, not an ambient linear projection for the cusp.
Source: the cusp parametrization s ↦ (s²,s³), Gunning--Rossi, III.C. -/
example : ∀ i : ℕ, AnalyticOnNhd ℂ
    (fun x : Fin 1 → ℂ ↦
      (adim9_fibrePolynomial 2 {![x 0 ^ 2, x 0 ^ 3]}
        (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 2 ↦ ℂ) 1)).coeff i)
    (Metric.ball 0 1) := by
  classical
  have hcoord := (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 1 ↦ ℂ) 0).analyticOnNhd
    (Metric.ball (0 : Fin 1 → ℂ) 1)
  have hr : AnalyticOnNhd ℂ (fun x : Fin 1 → ℂ ↦ (![x 0 ^ 2, x 0 ^ 3] : Fin 2 → ℂ))
      (Metric.ball 0 1) := by
    apply analyticOnNhd_pi_iff.mpr
    intro i
    fin_cases i
    · exact hcoord.pow 2
    · exact hcoord.pow 3
  have H := adim9_sheet_coefficients 2 1 1 (Metric.ball 0 1)
    (fun x ↦ {![x 0 ^ 2, x 0 ^ 3]})
    (by
      intro x hx
      refine ⟨Metric.ball 0 1, (fun _ y ↦ ![y 0 ^ 2, y 0 ^ 3]),
        Metric.isOpen_ball, hx, subset_rfl, (fun _ ↦ hr), ?_⟩
      intro y hy
      refine ⟨fun _ _ _ ↦ Subsingleton.elim _ _, ?_⟩
      intro z
      simp only [Finset.mem_singleton]
      constructor
      · intro hz
        exact ⟨0, hz.symm⟩
      · rintro ⟨j, hj⟩
        exact hj.symm)
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 2 ↦ ℂ) 1)
    1 (by norm_num)
    (by
      intro x hx z hz
      simp only [Finset.mem_singleton] at hz
      subst z
      change ‖x 0 ^ 3‖ ≤ 1
      rw [norm_pow]
      apply pow_le_one₀ (norm_nonneg _)
      exact (norm_le_pi_norm x 0).trans (by simpa using (Metric.mem_ball.mp hx).le))
  exact H.1

/-- W3: a fibre of the node has two compatible points; mixed signs are excluded.
Source: direct substitution and finite linear separation. -/
example : ¬ (∀ ℓ : (Fin 2 → ℂ) →L[ℂ] ℂ,
    (adim9_fibrePolynomial 2 {![1, 1], ![-1, -1]} ℓ).eval (ℓ ![1, -1]) = 0) := by
  classical
  rw [adim9_linear_observables_separate]
  simp only [Finset.mem_insert, Finset.mem_singleton]
  rintro (h | h)
  · have he := congrFun h 1
    norm_num at he
  · have he := congrFun h 0
    norm_num at he

/-- W4: the cone over the plane conic t²=xy, parametrized by (u²,v²,uv).
The full sheet is a clopen selection over a connected parameter space.
Source: the quadratic Veronese parametrization and Gunning--Rossi, III.C. -/
example : ∃ l : ℕ, l ≤ 1 ∧ ∀ x : Fin 2 → ℂ,
    ∃ (W : Set (Fin 2 → ℂ)) (r : Fin l → (Fin 2 → ℂ) → (Fin 3 → ℂ)),
      IsOpen W ∧ x ∈ W ∧ W ⊆ univ ∧ (∀ j, AnalyticOnNhd ℂ (r j) W) ∧
      ∀ y ∈ W, Function.Injective (fun j ↦ r j y) ∧
        ∀ z, z = ![y 0 ^ 2, y 1 ^ 2, y 0 * y 1] ↔ ∃ j, r j y = z := by
  classical
  have h0 := (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 2 ↦ ℂ) 0).analyticOnNhd univ
  have h1 := (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 2 ↦ ℂ) 1).analyticOnNhd univ
  have hr : AnalyticOnNhd ℂ
      (fun y : Fin 2 → ℂ ↦ (![y 0 ^ 2, y 1 ^ 2, y 0 * y 1] : Fin 3 → ℂ)) univ := by
    apply analyticOnNhd_pi_iff.mpr
    intro i
    fin_cases i
    · exact h0.pow 2
    · exact h1.pow 2
    · exact h0.mul h1
  have H := adim9_clopen_sheet_selection 3 2 1 univ isConnected_univ
    (fun y ↦ {![y 0 ^ 2, y 1 ^ 2, y 0 * y 1]})
    (by
      intro x hx
      refine ⟨univ, (fun _ y ↦ ![y 0 ^ 2, y 1 ^ 2, y 0 * y 1]),
        isOpen_univ, hx, subset_rfl, (fun _ ↦ hr), ?_⟩
      intro y hy
      refine ⟨fun _ _ _ ↦ Subsingleton.elim _ _, ?_⟩
      intro z
      simp only [Finset.mem_singleton]
      constructor
      · intro hz
        exact ⟨0, hz.symm⟩
      · rintro ⟨j, hj⟩
        exact hj.symm)
    univ (by simpa only [preimage_univ] using
      (isClopen_univ : IsClopen (univ : Set {p : (Fin 2 → ℂ) × (Fin 3 → ℂ) |
        p.1 ∈ univ ∧ p.2 ∈ ({![p.1 0 ^ 2, p.1 1 ^ 2, p.1 0 * p.1 1]} : Finset (Fin 3 → ℂ))})))
  simpa only [mem_univ, forall_true_left, Finset.mem_singleton, and_true] using H

/-- W4b: every point of the preceding parametrization lies on the quadratic cone.
Source: direct polynomial substitution. -/
example (u v : ℂ) : (u * v) ^ 2 = u ^ 2 * v ^ 2 := by ring

/-- W5: two generating directions on the distinct planes t=x and t=-x.
Source: finite dual hyperplane avoidance. -/
example : ∃ ℓ : (Fin 3 → ℂ) →L[ℂ] ℂ,
    ℓ ![1, 0, 1] ≠ 0 ∧ ℓ ![1, 0, -1] ≠ 0 := by
  have H := adim9_countable_linear_avoidance 3 {![1, 0, 1], ![1, 0, -1]}
    ((Set.finite_singleton _).insert _).countable
    (by
      simp only [mem_insert_iff, mem_singleton_iff]
      rintro (h | h) <;> have he := congrFun h 0 <;> norm_num at he)
  obtain ⟨ℓ, hℓ⟩ := H
  exact ⟨ℓ, hℓ _ (by simp), hℓ _ (by simp)⟩

/-- W6: the punctured node, projected onto its first coordinate at the missing origin.
Source: Demailly, II, proof of Theorem 8.7, compact-boundary confinement. -/
example :
    let A : Set (Fin 2 → ℂ) := {z | z 1 ^ 2 = z 0 ^ 2 ∧ z ≠ 0}
    let π : (Fin 2 → ℂ) →L[ℂ] (Fin 1 → ℂ) :=
      ContinuousLinearMap.pi (fun _ ↦ ContinuousLinearMap.proj 0)
    ∃ ε : ℝ, 0 < ε ∧
      ∃ p : {z : Fin 2 → ℂ // z ∈ A ∧ ‖z‖ < 1 ∧ ‖π z‖ < ε ∧ π z ≠ 0} →
        {w : Fin 1 → ℂ // ‖w‖ < ε ∧ w ≠ 0},
        (∀ z, (p z).val = π z.val) ∧ IsProperMap p ∧
        ∀ w, (p ⁻¹' {w}).Finite := by
  dsimp only
  let A : Set (Fin 2 → ℂ) := {z | z 1 ^ 2 = z 0 ^ 2 ∧ z ≠ 0}
  let π : (Fin 2 → ℂ) →L[ℂ] (Fin 1 → ℂ) :=
    ContinuousLinearMap.pi (fun _ ↦ ContinuousLinearMap.proj 0)
  apply adim9_punctured_confinement 2 1 A (by simp [A])
    (by
      have h : IsClosed {z : {z : Fin 2 → ℂ // z ≠ 0} | z.val 1 ^ 2 = z.val 0 ^ 2} :=
        isClosed_eq (((continuous_apply 1).comp continuous_subtype_val).pow 2)
          (((continuous_apply 0).comp continuous_subtype_val).pow 2)
      convert h using 1
      ext z
      simp only [mem_ofPred_eq, A, and_iff_left_iff_imp]
      exact fun _ ↦ z.property)
    (by
      intro x hx
      refine ⟨{z | z ≠ 0}, isOpen_compl_singleton, hx.2, subset_rfl,
        1, (fun _ z ↦ z 1 ^ 2 - z 0 ^ 2), ?_, ?_⟩
      · intro j
        exact (((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 2 ↦ ℂ) 1).analyticOnNhd _).pow 2).sub
          (((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 2 ↦ ℂ) 0).analyticOnNhd _).pow 2)
      · intro z hz
        change z ≠ 0 at hz
        change (z 1 ^ 2 = z 0 ^ 2 ∧ z ≠ 0) ↔ ∀ j : Fin 1, z 1 ^ 2 - z 0 ^ 2 = 0
        constructor
        · intro h j
          exact sub_eq_zero.mpr h.1
        · intro h
          exact ⟨sub_eq_zero.mp (h 0), hz⟩)
    π 1 (by norm_num)
  intro z hz hnorm hπ
  have hsub : A ⊆ {z : Fin 2 → ℂ | z 1 ^ 2 = z 0 ^ 2} := fun _ h ↦ h.1
  have he : z 1 ^ 2 = z 0 ^ 2 :=
    closure_minimal hsub (isClosed_eq (by fun_prop) (by fun_prop)) hz
  have hz0 : z 0 = 0 := congrFun hπ 0
  have hz1 : z 1 = 0 := by simpa only [hz0, zero_pow (by decide : 2 ≠ 0), pow_eq_zero_iff (by decide : 2 ≠ 0)] using he
  have hzall : z = 0 := by ext i; fin_cases i <;> assumption
  norm_num [hzall] at hnorm


/-- W7: both sheets of t²=x² over the punctured unit disc contribute to the bound.
Source: Gunning--Rossi, III.C, finite sheet symmetric functions. -/
example :
    let D : Set (Fin 1 → ℂ) := Metric.ball 0 1 \ {0}
    let s : (Fin 1 → ℂ) → Finset (Fin 2 → ℂ) := fun x ↦ {![x 0, x 0], ![x 0, -x 0]}
    let ℓ := ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 2 ↦ ℂ) 1
    (∀ i : ℕ, AnalyticOnNhd ℂ (fun x ↦ (adim9_fibrePolynomial 2 (s x) ℓ).coeff i) D) ∧
    ∀ x ∈ D, ∀ i : ℕ, ‖(adim9_fibrePolynomial 2 (s x) ℓ).coeff i‖ ≤ 4 := by
  classical
  dsimp only
  let D : Set (Fin 1 → ℂ) := Metric.ball 0 1 \ {0}
  let s : (Fin 1 → ℂ) → Finset (Fin 2 → ℂ) := fun x ↦ {![x 0, x 0], ![x 0, -x 0]}
  have hc := (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 1 ↦ ℂ) 0).analyticOnNhd D
  have H := adim9_sheet_coefficients 2 1 2 D s
    (by
      intro x hx
      refine ⟨D, (fun j y ↦ (![![y 0, y 0], ![y 0, -y 0]] : Fin 2 → Fin 2 → ℂ) j),
        Metric.isOpen_ball.sdiff isClosed_singleton, hx, subset_rfl, ?_, ?_⟩
      · intro j
        apply analyticOnNhd_pi_iff.mpr
        intro i
        fin_cases j <;> fin_cases i
        · exact hc
        · exact hc
        · exact hc
        · exact hc.neg
      · intro y hy
        have hy0 : y 0 ≠ 0 := by
          intro h
          apply hy.2
          change y = 0
          ext i
          fin_cases i
          exact h
        constructor
        · intro i j he
          fin_cases i <;> fin_cases j
          · rfl
          · exfalso
            apply hy0
            have hv : y 0 = -y 0 := congrFun he 1
            linear_combination (1 / 2 : ℂ) * hv
          · exfalso
            apply hy0
            have hv : -y 0 = y 0 := congrFun he 1
            linear_combination -(1 / 2 : ℂ) * hv
          · rfl
        · intro z
          change z ∈ ({![y 0, y 0], ![y 0, -y 0]} : Finset (Fin 2 → ℂ)) ↔ _
          simp only [Finset.mem_insert, Finset.mem_singleton]
          constructor
          · rintro (h | h)
            · exact ⟨0, h.symm⟩
            · exact ⟨1, h.symm⟩
          · rintro ⟨j, hj⟩
            fin_cases j
            · exact Or.inl hj.symm
            · exact Or.inr hj.symm)
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 2 ↦ ℂ) 1)
    1 (by norm_num)
    (by
      intro x hx z hz
      have hb : ‖x 0‖ ≤ 1 :=
        (norm_le_pi_norm x 0).trans (by simpa using (Metric.mem_ball.mp hx.1).le)
      change z ∈ ({![x 0, x 0], ![x 0, -x 0]} : Finset (Fin 2 → ℂ)) at hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl
      · exact hb
      · simpa only [ContinuousLinearMap.proj_apply, Matrix.cons_val_one, Matrix.cons_val_zero, norm_neg] using hb)
  refine ⟨H.1, ?_⟩
  intro x hx i
  convert (H.2 x hx).2.2.1 i using 1
  norm_num

/-- The target dimension is the attained maximum of the local component dimensions.
The projection is defined on the whole cone, including its vertex.
On the consumer path `adim9_cone_pure_projection` supersedes this statement.
Source: Griffiths--Harris, Principles of Algebraic Geometry, Chapter 1 §3,
proof of Chow's theorem by linear projection of a homogeneous cone;
Chirka, Complex Analytic Sets, §§3--4, dimension and generic projections. -/
theorem adim9_cone_finite_projection (n : ℕ) (C : Set (Fin (n + 1) → ℂ))
    (hzero : (0 : Fin (n + 1) → ℂ) ∉ C) (hne : C.Nonempty)
    (hclosed : IsClosed {z : {z : Fin (n + 1) → ℂ // z ≠ 0} | z.val ∈ C})
    (hscale : ∀ (t : ℂ), t ≠ 0 → ∀ z ∈ C, t • z ∈ C)
    (hloc : ∀ x ∈ C, ∃ U : Set (Fin (n + 1) → ℂ), IsOpen U ∧ x ∈ U ∧
      U ⊆ {z | z ≠ 0} ∧ ∃ (m : ℕ) (f : Fin m → (Fin (n + 1) → ℂ) → ℂ),
        (∀ j, AnalyticOnNhd ℂ (f j) U) ∧
        ∀ z ∈ U, (z ∈ C ↔ ∀ j, f j z = 0)) :
    ∃ r : ℕ, r ≤ n ∧
      (∀ x ∈ C,
        ∀ P ∈ (adim2_ideal (n + 1) (adim2_germ (n + 1) C x)).minimalPrimes,
          ringKrullDim (AnalyticGerm (n + 1) ⧸ P) ≤ ((r + 1 : ℕ) : WithBot ℕ∞)) ∧
      (∃ x ∈ C, ∃ P ∈ (adim2_ideal (n + 1) (adim2_germ (n + 1) C x)).minimalPrimes,
        ringKrullDim (AnalyticGerm (n + 1) ⧸ P) = ((r + 1 : ℕ) : WithBot ℕ∞)) ∧
      ∃ L : (Fin (n + 1) → ℂ) →L[ℂ] (Fin (r + 1) → ℂ),
        Function.Surjective L ∧
        IsProperMap (fun z : {z : Fin (n + 1) → ℂ // z ∈ insert 0 C} ↦ L z.val) ∧
        (∀ w, {z : Fin (n + 1) → ℂ | z ∈ insert 0 C ∧ L z = w}.Finite) ∧
        (L ⁻¹' {0}) ∩ insert 0 C = {0} :=
  adim9_cone_finite_projection_aux n C hzero hne hclosed hscale hloc

/-- W9: a punctured coordinate line supplies all geometric projection premises.
The output retains its local dimension certificate and its central fibre.
Source: Griffiths--Harris, Chapter 1 §3, linear cones. -/
example :
    let C : Set (Fin 2 → ℂ) := {z | z ≠ 0 ∧ z 1 = 0}
    ∃ r : ℕ, r ≤ 1 ∧
      (∀ x ∈ C,
        ∀ P ∈ (adim2_ideal 2 (adim2_germ 2 C x)).minimalPrimes,
          ringKrullDim (AnalyticGerm 2 ⧸ P) ≤ ((r + 1 : ℕ) : WithBot ℕ∞)) ∧
      (∃ x ∈ C, ∃ P ∈ (adim2_ideal 2 (adim2_germ 2 C x)).minimalPrimes,
        ringKrullDim (AnalyticGerm 2 ⧸ P) = ((r + 1 : ℕ) : WithBot ℕ∞)) ∧
      ∃ L : (Fin 2 → ℂ) →L[ℂ] (Fin (r + 1) → ℂ),
        Function.Surjective L ∧
        IsProperMap (fun z : {z : Fin 2 → ℂ // z ∈ insert 0 C} ↦ L z.val) ∧
        (∀ w, {z : Fin 2 → ℂ | z ∈ insert 0 C ∧ L z = w}.Finite) ∧
        (L ⁻¹' {0}) ∩ insert 0 C = {0} := by
  dsimp only
  have hclosed : IsClosed {z : {z : Fin 2 → ℂ // z ≠ 0} |
      z.val ∈ {w : Fin 2 → ℂ | w ≠ 0 ∧ w 1 = 0}} := by
    have he : IsClosed {z : {z : Fin 2 → ℂ // z ≠ 0} | z.val 1 = 0} :=
      isClosed_eq ((continuous_apply (1 : Fin 2) :
        Continuous (fun z : Fin 2 → ℂ ↦ z 1)).comp continuous_subtype_val) continuous_const
    convert he using 1
    ext z
    exact and_iff_right z.property
  have hscale : ∀ (t : ℂ), t ≠ 0 → ∀ z ∈ {w : Fin 2 → ℂ | w ≠ 0 ∧ w 1 = 0},
      t • z ∈ {w : Fin 2 → ℂ | w ≠ 0 ∧ w 1 = 0} := by
    intro t ht z hz
    exact ⟨smul_ne_zero ht hz.1, by simp [Pi.smul_apply, hz.2]⟩
  have hloc : ∀ x ∈ {w : Fin 2 → ℂ | w ≠ 0 ∧ w 1 = 0},
      ∃ U : Set (Fin 2 → ℂ), IsOpen U ∧ x ∈ U ∧ U ⊆ {z | z ≠ 0} ∧
        ∃ (m : ℕ) (f : Fin m → (Fin 2 → ℂ) → ℂ),
          (∀ j, AnalyticOnNhd ℂ (f j) U) ∧
          ∀ z ∈ U, (z ∈ {w : Fin 2 → ℂ | w ≠ 0 ∧ w 1 = 0} ↔ ∀ j, f j z = 0) := by
    intro x hx
    refine ⟨{z | z ≠ 0}, isOpen_ne, hx.1,
      subset_rfl, 1, fun _ z ↦ z 1, ?_, ?_⟩
    · exact fun _ ↦ (ContinuousLinearMap.proj (R := ℂ)
        (φ := fun _ : Fin 2 ↦ ℂ) 1).analyticOnNhd _
    · intro z hz
      exact ⟨fun h _ ↦ h.2, fun h ↦ ⟨hz, h 0⟩⟩
  apply adim9_cone_finite_projection 1 _ (by simp) _ hclosed hscale hloc
  refine ⟨![1, 0], ?_, by simp⟩
  intro h
  have he := congrFun h 0
  norm_num at he

/-- Finitely many pure-dimensional punctured homogeneous cones cover the cone.
Each part keeps all cone premises, and every minimal prime of every local
germ of the part has the same Krull dimension.
Source: Gunning--Rossi, III.C and III.D, decomposition of an analytic set into
irreducible components and its pure-dimensional parts; Chirka, Complex Analytic
Sets, §5.4, pure-dimensional parts; Griffiths--Harris, Chapter 1 §3, cones. -/
theorem adim9_cone_pure_cover (n : ℕ) (C : Set (Fin (n + 1) → ℂ))
    (hzero : (0 : Fin (n + 1) → ℂ) ∉ C) (hne : C.Nonempty)
    (hclosed : IsClosed {z : {z : Fin (n + 1) → ℂ // z ≠ 0} | z.val ∈ C})
    (hscale : ∀ (t : ℂ), t ≠ 0 → ∀ z ∈ C, t • z ∈ C)
    (hloc : ∀ x ∈ C, ∃ U : Set (Fin (n + 1) → ℂ), IsOpen U ∧ x ∈ U ∧
      U ⊆ {z | z ≠ 0} ∧ ∃ (m : ℕ) (f : Fin m → (Fin (n + 1) → ℂ) → ℂ),
        (∀ j, AnalyticOnNhd ℂ (f j) U) ∧
        ∀ z ∈ U, (z ∈ C ↔ ∀ j, f j z = 0)) :
    ∃ (k : ℕ) (Cι : Fin k → Set (Fin (n + 1) → ℂ)) (dι : Fin k → ℕ),
      insert 0 C = ⋃ i, insert 0 (Cι i) ∧
      ∀ i, Cι i ⊆ C ∧ dι i ≤ n ∧
        (0 : Fin (n + 1) → ℂ) ∉ Cι i ∧ (Cι i).Nonempty ∧
        IsClosed {z : {z : Fin (n + 1) → ℂ // z ≠ 0} | z.val ∈ Cι i} ∧
        (∀ (t : ℂ), t ≠ 0 → ∀ z ∈ Cι i, t • z ∈ Cι i) ∧
        (∀ x ∈ Cι i, ∃ U : Set (Fin (n + 1) → ℂ), IsOpen U ∧ x ∈ U ∧
          U ⊆ {z | z ≠ 0} ∧ ∃ (m : ℕ) (f : Fin m → (Fin (n + 1) → ℂ) → ℂ),
            (∀ j, AnalyticOnNhd ℂ (f j) U) ∧
            ∀ z ∈ U, (z ∈ Cι i ↔ ∀ j, f j z = 0)) ∧
        ∀ x ∈ Cι i,
          ∀ P ∈ (adim2_ideal (n + 1) (adim2_germ (n + 1) (Cι i) x)).minimalPrimes,
            ringKrullDim (AnalyticGerm (n + 1) ⧸ P) = ((dι i + 1 : ℕ) : WithBot ℕ∞) :=
  adim9_cone_pure_cover_aux n C hzero hne hclosed hscale hloc

/-- A pure-dimensional punctured homogeneous cone has a finite proper linear
projection of the whole cone onto affine space of its own dimension.
On the consumer path this supersedes `adim9_cone_finite_projection`.
Source: Griffiths--Harris, Principles of Algebraic Geometry, Chapter 1 §3,
projection of a homogeneous cone from a disjoint linear centre;
Chirka, Complex Analytic Sets, §§3--4, dimension and generic projections. -/
theorem adim9_cone_pure_projection (n : ℕ) (C : Set (Fin (n + 1) → ℂ))
    (hzero : (0 : Fin (n + 1) → ℂ) ∉ C) (hne : C.Nonempty)
    (hclosed : IsClosed {z : {z : Fin (n + 1) → ℂ // z ≠ 0} | z.val ∈ C})
    (hscale : ∀ (t : ℂ), t ≠ 0 → ∀ z ∈ C, t • z ∈ C)
    (hloc : ∀ x ∈ C, ∃ U : Set (Fin (n + 1) → ℂ), IsOpen U ∧ x ∈ U ∧
      U ⊆ {z | z ≠ 0} ∧ ∃ (m : ℕ) (f : Fin m → (Fin (n + 1) → ℂ) → ℂ),
        (∀ j, AnalyticOnNhd ℂ (f j) U) ∧
        ∀ z ∈ U, (z ∈ C ↔ ∀ j, f j z = 0))
    (d : ℕ)
    (hpure : ∀ x ∈ C,
      ∀ P ∈ (adim2_ideal (n + 1) (adim2_germ (n + 1) C x)).minimalPrimes,
        ringKrullDim (AnalyticGerm (n + 1) ⧸ P) = ((d + 1 : ℕ) : WithBot ℕ∞)) :
    ∃ L : (Fin (n + 1) → ℂ) →L[ℂ] (Fin (d + 1) → ℂ),
      Function.Surjective L ∧
      Function.Surjective
        (fun z : {z : Fin (n + 1) → ℂ // z ∈ insert 0 C} ↦ L z.val) ∧
      IsProperMap (fun z : {z : Fin (n + 1) → ℂ // z ∈ insert 0 C} ↦ L z.val) ∧
      (∀ w, {z : Fin (n + 1) → ℂ | z ∈ insert 0 C ∧ L z = w}.Finite) ∧
      (L ⁻¹' {0}) ∩ insert 0 C = {0} :=
  adim9_cone_pure_projection_aux n C hzero hne hclosed hscale hloc d hpure

/-- Implication from a finite proper linear projection of the whole homogeneous
cone to vertex extension. Linearity supplies compatibility with scalar multiplication.
The cone is pure of the target dimension, and the projection maps the cone onto the target.
Source: Griffiths--Harris, Principles of Algebraic Geometry, Chapter 1 §3,
cone proof of Chow; Demailly, Complex Analytic and Differential Geometry (2012),
II, proof of Theorem 8.7, pp. 119--120, bounded symmetric sheet coefficients. -/
theorem adim9_cone_vertex_extension (n : ℕ) (C : Set (Fin (n + 1) → ℂ))
    (hzero : (0 : Fin (n + 1) → ℂ) ∉ C) (hne : C.Nonempty)
    (hclosed : IsClosed {z : {z : Fin (n + 1) → ℂ // z ≠ 0} | z.val ∈ C})
    (hscale : ∀ (t : ℂ), t ≠ 0 → ∀ z ∈ C, t • z ∈ C)
    (hloc : ∀ x ∈ C, ∃ U : Set (Fin (n + 1) → ℂ), IsOpen U ∧ x ∈ U ∧
      U ⊆ {z | z ≠ 0} ∧ ∃ (m : ℕ) (f : Fin m → (Fin (n + 1) → ℂ) → ℂ),
        (∀ j, AnalyticOnNhd ℂ (f j) U) ∧
        ∀ z ∈ U, (z ∈ C ↔ ∀ j, f j z = 0))
    (d : ℕ) (L : (Fin (n + 1) → ℂ) →L[ℂ] (Fin (d + 1) → ℂ))
    (hpure : ∀ x ∈ C,
      ∀ P ∈ (adim2_ideal (n + 1) (adim2_germ (n + 1) C x)).minimalPrimes,
        ringKrullDim (AnalyticGerm (n + 1) ⧸ P) = ((d + 1 : ℕ) : WithBot ℕ∞))
    (honto : Function.Surjective
      (fun z : {z : Fin (n + 1) → ℂ // z ∈ insert 0 C} ↦ L z.val))
    (hsurj : Function.Surjective L)
    (hproper : IsProperMap
      (fun z : {z : Fin (n + 1) → ℂ // z ∈ insert 0 C} ↦ L z.val))
    (hfib : ∀ w, {z : Fin (n + 1) → ℂ | z ∈ insert 0 C ∧ L z = w}.Finite)
    (hcentral : (L ⁻¹' {0}) ∩ insert 0 C = {0}) :
    IsClosedAnalytic (Fin (n + 1) → ℂ) (insert 0 C) :=
  adim9_cone_vertex_extension_aux n C hzero hne hclosed hscale hloc d L hpure honto
    hsurj hproper hfib hcentral

/-- Finitely many cones closed analytic through the vertex have a closed analytic union.
With no pieces the cover premise is contradictory, since it puts the vertex in the empty set.
Source: Schnell, Complex Manifolds (lecture notes), Definition 3.2;
finite unions of analytic sets, `IsClosedAnalytic.biUnion_finset`. -/
theorem adim9_cone_vertex_extension_finite_union (n k : ℕ) (C : Set (Fin (n + 1) → ℂ))
    (Cι : Fin k → Set (Fin (n + 1) → ℂ))
    (hcover : insert 0 C = ⋃ i, insert 0 (Cι i))
    (hext : ∀ i, IsClosedAnalytic (Fin (n + 1) → ℂ) (insert 0 (Cι i))) :
    IsClosedAnalytic (Fin (n + 1) → ℂ) (insert 0 C) :=
  adim9_cone_vertex_extension_finite_union_aux n k C Cι hcover hext

/-- W10: the punctured coordinate line extends through its vertex by the pure
cover, the per-piece projection, vertex extension and the finite union.
Source: Griffiths--Harris, Chapter 1 §3, linear cones. -/
example : IsClosedAnalytic (Fin 2 → ℂ)
    (insert 0 {z : Fin 2 → ℂ | z ≠ 0 ∧ z 1 = 0}) := by
  have hclosed : IsClosed {z : {z : Fin 2 → ℂ // z ≠ 0} |
      z.val ∈ {w : Fin 2 → ℂ | w ≠ 0 ∧ w 1 = 0}} := by
    have he : IsClosed {z : {z : Fin 2 → ℂ // z ≠ 0} | z.val 1 = 0} :=
      isClosed_eq ((continuous_apply (1 : Fin 2) :
        Continuous (fun z : Fin 2 → ℂ ↦ z 1)).comp continuous_subtype_val) continuous_const
    convert he using 1
    ext z
    exact and_iff_right z.property
  have hscale : ∀ (t : ℂ), t ≠ 0 → ∀ z ∈ {w : Fin 2 → ℂ | w ≠ 0 ∧ w 1 = 0},
      t • z ∈ {w : Fin 2 → ℂ | w ≠ 0 ∧ w 1 = 0} := by
    intro t ht z hz
    exact ⟨smul_ne_zero ht hz.1, by simp [Pi.smul_apply, hz.2]⟩
  have hloc : ∀ x ∈ {w : Fin 2 → ℂ | w ≠ 0 ∧ w 1 = 0},
      ∃ U : Set (Fin 2 → ℂ), IsOpen U ∧ x ∈ U ∧ U ⊆ {z | z ≠ 0} ∧
        ∃ (m : ℕ) (f : Fin m → (Fin 2 → ℂ) → ℂ),
          (∀ j, AnalyticOnNhd ℂ (f j) U) ∧
          ∀ z ∈ U, (z ∈ {w : Fin 2 → ℂ | w ≠ 0 ∧ w 1 = 0} ↔ ∀ j, f j z = 0) := by
    intro x hx
    refine ⟨{z | z ≠ 0}, isOpen_ne, hx.1,
      subset_rfl, 1, fun _ z ↦ z 1, ?_, ?_⟩
    · exact fun _ ↦ (ContinuousLinearMap.proj (R := ℂ)
        (φ := fun _ : Fin 2 ↦ ℂ) 1).analyticOnNhd _
    · intro z hz
      exact ⟨fun h _ ↦ h.2, fun h ↦ ⟨hz, h 0⟩⟩
  have hne : ({z : Fin 2 → ℂ | z ≠ 0 ∧ z 1 = 0} : Set (Fin 2 → ℂ)).Nonempty := by
    refine ⟨![1, 0], ?_, by simp⟩
    intro h
    have he := congrFun h 0
    norm_num at he
  obtain ⟨k, Cι, dι, hcover, hpiece⟩ :=
    adim9_cone_pure_cover 1 _ (by simp) hne hclosed hscale hloc
  refine adim9_cone_vertex_extension_finite_union 1 k _ Cι hcover (fun i ↦ ?_)
  obtain ⟨_, _, hz, hn, hc, hs, hl, hp⟩ := hpiece i
  obtain ⟨L, hsurj, honto, hproper, hfib, hcentral⟩ :=
    adim9_cone_pure_projection 1 (Cι i) hz hn hc hs hl (dι i) hp
  exact adim9_cone_vertex_extension 1 (Cι i) hz hn hc hs hl (dι i) L hp honto
    hsurj hproper hfib hcentral

/-- W11: the finite union accepts a cover with a repeated piece.
Source: finite unions of analytic sets. -/
example (n : ℕ) (C : Set (Fin (n + 1) → ℂ))
    (hC : IsClosedAnalytic (Fin (n + 1) → ℂ) (insert 0 C)) :
    IsClosedAnalytic (Fin (n + 1) → ℂ) (insert 0 C) :=
  adim9_cone_vertex_extension_finite_union n 2 C (fun _ ↦ C)
    (by simp only [iUnion_const]) (fun _ ↦ hC)

/-- W12: with no pieces the cover premise is contradictory.
Source: the vertex lies in `insert 0 C` but not in the empty union. -/
example (n : ℕ) (C : Set (Fin (n + 1) → ℂ)) (Cι : Fin 0 → Set (Fin (n + 1) → ℂ)) :
    insert 0 C ≠ ⋃ i, insert 0 (Cι i) := by
  intro h
  have h0 : (0 : Fin (n + 1) → ℂ) ∈ ⋃ i, insert 0 (Cι i) := h ▸ mem_insert 0 C
  obtain ⟨i, _⟩ := mem_iUnion.mp h0
  exact i.elim0

/-- Composition check: the pure cover, the per-piece projection, the amended
vertex extension and the finite union give exactly the conclusion of
`chowEE3_vertex_extension_of_point` from exactly its premises.
Source: Griffiths--Harris, Chapter 1 §3, cone proof of Chow. -/
example (n : ℕ) (A : Set (Fin (n + 1) → ℂ))
    (hzero : (0 : Fin (n + 1) → ℂ) ∉ A) (hne : A.Nonempty)
    (hclosed : IsClosed {z : {z : Fin (n + 1) → ℂ // z ≠ 0} | z.val ∈ A})
    (hscale : ∀ (t : ℂ), t ≠ 0 → ∀ z ∈ A, t • z ∈ A)
    (hloc : ∀ x ∈ A, ∃ U : Set (Fin (n + 1) → ℂ), IsOpen U ∧ x ∈ U ∧
      U ⊆ {z | z ≠ 0} ∧ ∃ (m : ℕ) (f : Fin m → (Fin (n + 1) → ℂ) → ℂ),
        (∀ j, AnalyticOnNhd ℂ (f j) U) ∧
        ∀ z ∈ U, (z ∈ A ↔ ∀ j, f j z = 0)) :
    IsClosedAnalytic (Fin (n + 1) → ℂ) (insert 0 A) := by
  obtain ⟨k, Cι, dι, hcover, hpiece⟩ :=
    adim9_cone_pure_cover n A hzero hne hclosed hscale hloc
  refine adim9_cone_vertex_extension_finite_union n k A Cι hcover (fun i ↦ ?_)
  obtain ⟨_, _, hz, hn, hc, hs, hl, hp⟩ := hpiece i
  obtain ⟨L, hsurj, honto, hproper, hfib, hcentral⟩ :=
    adim9_cone_pure_projection n (Cι i) hz hn hc hs hl (dι i) hp
  exact adim9_cone_vertex_extension n (Cι i) hz hn hc hs hl (dι i) L hp honto
    hsurj hproper hfib hcentral

end HodgeLean.Foundations
