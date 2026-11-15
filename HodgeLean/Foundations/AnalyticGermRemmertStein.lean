import HodgeLean.Foundations.AnalyticGermRemmertSteinProofs

/-! # Continuation toward point extension

Implication from bounded holomorphy off a hypersurface to analytic continuation,
and from dense parameter sets to closure of monic zero loci.
Adapted projection and mixed-relation exactness at the missing point remain deferred.
HC no distance; AV milestone no distance.
-/

noncomputable section
open Set Filter Topology Polynomial
namespace HodgeLean.Foundations

/-- Source: Gunning--Rossi, Analytic Functions of Several Complex Variables, III.C, Riemann extension theorem across an analytic subset; Chirka, Complex Analytic Sets, §4. -/
theorem adim8_hypersurface_extension (d : ℕ) (V : Set (Fin (d + 1) → ℂ))
    (hV : IsOpen V) (δ f : (Fin (d + 1) → ℂ) → ℂ)
    (hδ : AnalyticOnNhd ℂ δ V)
    (hnz : ∀ x ∈ V, ¬ (δ =ᶠ[𝓝 x] fun _ ↦ 0))
    (hf : AnalyticOnNhd ℂ f (V \ {x | δ x = 0}))
    (C : ℝ) (hb : ∀ x ∈ V \ {x | δ x = 0}, ‖f x‖ ≤ C) :
    ∃ F : (Fin (d + 1) → ℂ) → ℂ,
      AnalyticOnNhd ℂ F V ∧ Set.EqOn F f (V \ {x | δ x = 0}) ∧
      (∀ x ∈ V, ‖F x‖ ≤ C) ∧
      ∀ G : (Fin (d + 1) → ℂ) → ℂ,
        ContinuousOn G V → Set.EqOn G f (V \ {x | δ x = 0}) → Set.EqOn G F V :=
  adim8_hypersurface_extension_aux d V hV δ f hδ hnz hf C hb

/-- W1: a coordinate hyperplane in two parameters is a positive-dimensional exceptional locus.
The supplied function has an intentionally different value on that hyperplane.
Source: Gunning--Rossi, III.C, bounded removable singularities. -/
example : ∃ F : (Fin 2 → ℂ) → ℂ,
    AnalyticOnNhd ℂ F (Metric.ball 0 1) ∧
    Set.EqOn F (fun z ↦ if z 0 = 0 then 7 else z 1)
      (Metric.ball 0 1 \ {z | z 0 = 0}) ∧
    (∀ z ∈ Metric.ball 0 1, ‖F z‖ ≤ 1) := by
  have hnz : ∀ x : Fin 2 → ℂ, ¬ ((fun z : Fin 2 → ℂ ↦ z 0) =ᶠ[𝓝 x] fun _ ↦ 0) := by
    intro x he
    have hd := he.fderiv_eq (𝕜 := ℂ)
    have hv := congrArg (fun L : (Fin 2 → ℂ) →L[ℂ] ℂ ↦ L (fun _ ↦ 1)) hd
    rw [fderiv_apply (𝕜 := ℂ) differentiableAt_id, fderiv_fun_id] at hv
    simp at hv
  obtain ⟨F, hF, heq, hb, _⟩ := adim8_hypersurface_extension 1 (Metric.ball 0 1)
    Metric.isOpen_ball (fun z ↦ z 0) (fun z ↦ if z 0 = 0 then 7 else z 1)
    ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 2 ↦ ℂ) 0).analyticOnNhd _)
    (fun x _ ↦ hnz x)
    (by
      apply AnalyticOnNhd.congr
        (Metric.isOpen_ball.sdiff (isClosed_eq (continuous_apply 0) continuous_const))
        ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 2 ↦ ℂ) 1).analyticOnNhd _)
      intro z hz
      have hn : z 0 ≠ 0 := hz.2
      simp [hn])
    1 (by
      intro z hz
      have hn : z 0 ≠ 0 := hz.2
      simp only [ite_eq_right hn]
      have hz' : ‖z‖ < 1 := by simpa using hz.1
      exact (norm_le_pi_norm z 1).trans hz'.le)
  exact ⟨F, hF, heq, hb⟩

/-- Source: Gunning--Rossi, III.C and V, continuation of coefficients; adim6_bounded_point_extension. -/
theorem adim8_coefficient_extension (d k : ℕ) (U : Set (Fin (d + 1) → ℂ))
    (hU : IsOpen U) (hU0 : (0 : Fin (d + 1) → ℂ) ∈ U)
    (δ : (Fin (d + 1) → ℂ) → ℂ)
    (hδ : AnalyticOnNhd ℂ δ (U \ {0}))
    (hnz : ∀ x ∈ U \ {0}, ¬ (δ =ᶠ[𝓝 x] fun _ ↦ 0))
    (a : Fin k → (Fin (d + 1) → ℂ) → ℂ)
    (ha : ∀ i, AnalyticOnNhd ℂ (a i) ((U \ {0}) \ {x | δ x = 0}))
    (C : Fin k → ℝ)
    (hb : ∀ i x, x ∈ (U \ {0}) \ {x | δ x = 0} → ‖a i x‖ ≤ C i) :
    ∃ b : Fin k → (Fin (d + 1) → ℂ) → ℂ,
      (∀ i, AnalyticOnNhd ℂ (b i) U) ∧
      (∀ i, Set.EqOn (b i) (a i) ((U \ {0}) \ {x | δ x = 0})) ∧
      (∀ i x, x ∈ U → ‖b i x‖ ≤ C i) :=
  adim8_coefficient_extension_aux d k U hU hU0 δ hδ hnz a ha C hb

/-- Source: Gunning--Rossi, I.A, argument principle and continuity of roots of monic polynomials; III.C, finite hypersurface projections. -/
theorem adim8_monic_closure (d k : ℕ) (U D : Set (Fin d → ℂ))
    (hU : IsOpen U) (hDU : D ⊆ U) (hdense : U ⊆ closure D)
    (a : Fin k → (Fin d → ℂ) → ℂ) (ha : ∀ i, ContinuousOn (a i) U) :
    ∀ p : (Fin d → ℂ) × ℂ, p.1 ∈ U →
      (p ∈ closure {q : (Fin d → ℂ) × ℂ |
        q.1 ∈ D ∧ q.2 ^ k + ∑ i : Fin k, a i q.1 * q.2 ^ (i : ℕ) = 0} ↔
        p.2 ^ k + ∑ i : Fin k, a i p.1 * p.2 ^ (i : ℕ) = 0) :=
  adim8_monic_closure_aux d k U D hU hDU hdense a ha

/-- W2: a bounded coordinate family across a hyperplane and the origin.
Source: Gunning--Rossi, III.C and V, coefficient continuation. -/
example : ∃ b : Fin 1 → (Fin 2 → ℂ) → ℂ,
    (∀ i, AnalyticOnNhd ℂ (b i) (Metric.ball 0 1)) ∧
    (∀ i, Set.EqOn (b i) (fun z ↦ if z 0 = 0 then 7 else z 1)
      ((Metric.ball 0 1 \ {0}) \ {z | z 0 = 0})) ∧
    (∀ i x, x ∈ Metric.ball 0 1 → ‖b i x‖ ≤ 1) := by
  have hnz : ∀ x : Fin 2 → ℂ, ¬ ((fun z : Fin 2 → ℂ ↦ z 0) =ᶠ[𝓝 x] fun _ ↦ 0) := by
    intro x he
    have hd := he.fderiv_eq (𝕜 := ℂ)
    have hv := congrArg (fun L : (Fin 2 → ℂ) →L[ℂ] ℂ ↦ L (fun _ ↦ 1)) hd
    rw [fderiv_apply (𝕜 := ℂ) differentiableAt_id, fderiv_fun_id] at hv
    simp at hv
  apply adim8_coefficient_extension 1 1 (Metric.ball 0 1) Metric.isOpen_ball
    (Metric.mem_ball_self (by norm_num)) (fun z ↦ z 0)
    ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 2 ↦ ℂ) 0).analyticOnNhd _)
    (fun x _ ↦ hnz x) (fun _ z ↦ if z 0 = 0 then 7 else z 1)
  · intro i
    apply AnalyticOnNhd.congr
      ((Metric.isOpen_ball.sdiff isClosed_singleton).sdiff
        (isClosed_eq (continuous_apply 0) continuous_const))
      ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 2 ↦ ℂ) 1).analyticOnNhd _)
    intro z hz
    have hn : z 0 ≠ 0 := hz.2
    simp [hn]
  · intro i z hz
    have hn : z 0 ≠ 0 := hz.2
    simp only [ite_eq_right hn]
    have hz' : ‖z‖ < 1 := by simpa using hz.1.1
    exact (norm_le_pi_norm z 1).trans hz'.le

/-- W3: the two branches of the node rejoin over the missing parameter.
Source: Chirka, Complex Analytic Sets, §4, elementary curve models. -/
example : ∀ p : (Fin 1 → ℂ) × ℂ,
    (p ∈ closure {q : (Fin 1 → ℂ) × ℂ |
      q.1 ≠ 0 ∧ q.2 ^ 2 - q.1 0 ^ 2 = 0} ↔ p.2 ^ 2 - p.1 0 ^ 2 = 0) := by
  have H := adim8_monic_closure 1 2 univ {0}ᶜ isOpen_univ (subset_univ _)
    (by rw [closure_compl_singleton])
    ![(fun z : Fin 1 → ℂ ↦ -(z 0 ^ 2)), (fun _ ↦ 0)]
    (by intro i; fin_cases i <;> dsimp <;> fun_prop)
  intro p
  simpa [Fin.sum_univ_two, sub_eq_add_neg] using H p (mem_univ _)

/-- W4: the cusp retains its ramification point.
Source: Chirka, Complex Analytic Sets, §4, elementary curve models. -/
example : ∀ p : (Fin 1 → ℂ) × ℂ,
    (p ∈ closure {q : (Fin 1 → ℂ) × ℂ |
      q.1 ≠ 0 ∧ q.2 ^ 2 - q.1 0 ^ 3 = 0} ↔ p.2 ^ 2 - p.1 0 ^ 3 = 0) := by
  have H := adim8_monic_closure 1 2 univ {0}ᶜ isOpen_univ (subset_univ _)
    (by rw [closure_compl_singleton])
    ![(fun z : Fin 1 → ℂ ↦ -(z 0 ^ 3)), (fun _ ↦ 0)]
    (by intro i; fin_cases i <;> dsimp <;> fun_prop)
  intro p
  simpa [Fin.sum_univ_two, sub_eq_add_neg] using H p (mem_univ _)

/-- W5: the quadratic cone over the plane conic t² = xy retains its vertex.
Source: Chirka, Complex Analytic Sets, §4; Griffiths--Harris, Chapter 1 §3. -/
example : ∀ p : (Fin 2 → ℂ) × ℂ,
    (p ∈ closure {q : (Fin 2 → ℂ) × ℂ |
      q.1 ≠ 0 ∧ q.2 ^ 2 - q.1 0 * q.1 1 = 0} ↔
      p.2 ^ 2 - p.1 0 * p.1 1 = 0) := by
  have H := adim8_monic_closure 2 2 univ {0}ᶜ isOpen_univ (subset_univ _)
    (by rw [closure_compl_singleton])
    ![(fun z : Fin 2 → ℂ ↦ -(z 0 * z 1)), (fun _ ↦ 0)]
    (by intro i; fin_cases i <;> dsimp <;> fun_prop)
  intro p
  simpa [Fin.sum_univ_two, sub_eq_add_neg] using H p (mem_univ _)

/-- W6: independent coordinate equations allow incompatible signs.
Source: mixed-root falsification in docs/specs/AnalyticGermExtension.md. -/
example : (1 : ℂ) ^ 2 = 1 ^ 2 ∧ (-1 : ℂ) ^ 2 = 1 ^ 2 ∧ (1 : ℂ) ≠ -1 := by
  norm_num

/-- W7: even coupled equations and monic coordinate relations acquire extra points
on the discriminant. Here Q=t²-y, Δ=xy and R₁=R₂=Δt.
Source: direct substitution into the primitive presentation of Gunning--Rossi, III.C. -/
example : ∀ s : ℂ, s ≠ 0 →
    let x : ℂ := 0
    let y := s ^ 2
    let t := s
    let c₁ := s
    let c₂ := -s
    t ^ 2 - y = 0 ∧
    (x * y) * c₁ = (x * y) * t ∧
    (x * y) * c₂ = (x * y) * t ∧
    c₁ ^ 2 - y = 0 ∧ c₂ ^ 2 - y = 0 ∧ c₁ ≠ c₂ := by
  intro s hs
  dsimp
  refine ⟨by ring, by ring, by ring, by ring, by ring, ?_⟩
  intro he
  apply hs
  linear_combination (1 / 2 : ℂ) * he

/-- W8: the spurious points of W7 are outside the closure of the good mixed locus.
Source: the closed diagonal and cancellation off the discriminant. -/
example : ∀ s : ℂ, s ≠ 0 →
    ![0, s ^ 2, s, s, -s] ∉ closure {q : Fin 5 → ℂ |
      q 0 * q 1 ≠ 0 ∧
      (q 0 * q 1) * q 3 = (q 0 * q 1) * q 2 ∧
      (q 0 * q 1) * q 4 = (q 0 * q 1) * q 2} := by
  intro s hs hp
  have hsub : {q : Fin 5 → ℂ | q 0 * q 1 ≠ 0 ∧
      (q 0 * q 1) * q 3 = (q 0 * q 1) * q 2 ∧
      (q 0 * q 1) * q 4 = (q 0 * q 1) * q 2} ⊆ {q | q 3 = q 4} := by
    intro q hq
    exact (mul_left_cancel₀ hq.1 hq.2.1).trans (mul_left_cancel₀ hq.1 hq.2.2).symm
  have he := closure_minimal hsub
    (isClosed_eq (continuous_apply 3) (continuous_apply 4)) hp
  change s = -s at he
  apply hs
  linear_combination (1 / 2 : ℂ) * he

end HodgeLean.Foundations
