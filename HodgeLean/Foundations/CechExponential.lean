module

public import HodgeLean.Foundations.CechExponentialProofs

/-! # Logarithmic lifting: frozen specification

Route A uses convex logarithms and a degree-two Čech--singular diagram chase over the integers.
The endpoint is an implication from a pointed open cover and a holomorphic multiplicative
cocycle to a refined additive lift. No additive potential or holomorphic trivialization is claimed. HC no distance; AV milestone no distance.
-/

public section
noncomputable section
open Set
open scoped Simplicial BigOperators
namespace HodgeLean.Foundations

/-- Pointed open covers have pointed convex refinements.
Source: metric balls form a basis; Mathlib `Metric.isOpen_iff` and `convex_ball`. -/
theorem cech_convex_refinement (n : ℕ)
    (U : (Fin n → ℂ) → Set (Fin n → ℂ))
    (hU : ∀ p, IsOpen (U p)) (hcover : ∀ p, p ∈ U p) :
    ∃ V : (Fin n → ℂ) → Set (Fin n → ℂ),
      (∀ p, IsOpen (V p)) ∧ (∀ p, p ∈ V p) ∧
      (∀ p, Convex ℝ (V p)) ∧ (∀ p, V p ⊆ U p) :=
  cech_convex_refinement_aux n U hU hcover

/-- A nonvanishing analytic function on a convex open has an analytic logarithm.
Source: Mathlib `Complex.isCoveringMapOn_exp` and
`IsCoveringMapOn.existsUnique_continuousMap_lifts`; local analytic logarithms. -/
theorem cech_convex_log (n : ℕ) (S : Set (Fin n → ℂ))
    (hS : IsOpen S) (hc : Convex ℝ S)
    (f : (Fin n → ℂ) → ℂ) (hf : AnalyticOnNhd ℂ f S)
    (hn : ∀ z ∈ S, f z ≠ 0) :
    ∃ b : (Fin n → ℂ) → ℂ,
      AnalyticOnNhd ℂ b S ∧ ∀ z ∈ S, Complex.exp (b z) = f z :=
  cech_convex_log_aux n S hS hc f hf hn

/-- Overlap logarithms determine a constant integral two-cocycle on a convex cover.
Source: Gunning--Rossi, VIII, exponential sequence; Mathlib `Complex.exp_eq_one_iff`. -/
theorem cech_integer_defect (n : ℕ) (V : (Fin n → ℂ) → Set (Fin n → ℂ))
    (hV : ∀ p, IsOpen (V p)) (hv : ∀ p, Convex ℝ (V p))
    (u b : (Fin n → ℂ) → (Fin n → ℂ) → (Fin n → ℂ) → ℂ)
    (hb : ∀ p q, AnalyticOnNhd ℂ (b p q) (V p ∩ V q))
    (he : ∀ p q z, z ∈ V p ∩ V q → Complex.exp (b p q z) = u p q z)
    (hc : ∀ p q r z, z ∈ V p ∩ V q ∩ V r → u p q z * u q r z = u p r z) :
    ∃ c : (Fin n → ℂ) → (Fin n → ℂ) → (Fin n → ℂ) → ℤ,
      (∀ p q r z, z ∈ V p ∩ V q ∩ V r →
        b q r z - b p r z + b p q z = (2 * Real.pi * Complex.I) * (c p q r : ℂ)) ∧
      (∀ p q r s z, z ∈ V p ∩ V q ∩ V r ∩ V s →
        c q r s - c p r s + c p q s - c p q r = 0) :=
  cech_integer_defect_aux n V hV hv u b hb he hc

/-- Positive Čech degrees of the singular cochain rows are exact on supported simplices.
Source: Bott--Tu, §8, contraction by an index containing the entire simplex. -/
theorem cech_horizontal_exact (n p q : ℕ) (U : (Fin n → ℂ) → Set (Fin n → ℂ))
    (F : (Fin (p + 2) → (Fin n → ℂ)) → cech_simplex n q → ℤ)
    (hF : ∀ t σ, (∀ x i, σ x ∈ U (t i)) → cech_h n (p + 1) F t σ = 0) :
    ∃ G : (Fin (p + 1) → (Fin n → ℂ)) → cech_simplex n q → ℤ,
      ∀ t σ, (∀ x i, σ x ∈ U (t i)) → cech_h n p G t σ = F t σ :=
  cech_horizontal_exact_aux n p q U F hF

/-- Compatible degree-zero rows glue to a cochain on cover-small singular simplices.
Source: Bott--Tu, §8, augmentation of the Čech double complex. -/
theorem cech_horizontal_glue (n q : ℕ) (U : (Fin n → ℂ) → Set (Fin n → ℂ))
    (F : (Fin 1 → (Fin n → ℂ)) → cech_simplex n q → ℤ)
    (hF : ∀ t σ, (∀ x i, σ x ∈ U (t i)) → cech_h n 0 F t σ = 0) :
    ∃ G : cech_simplex n q → ℤ,
      ∀ t σ, (∀ x i, σ x ∈ U (t i)) → G σ = F t σ :=
  cech_horizontal_glue_aux n q U F hF

/-- A closed integral singular one-cochain on a convex subset has a primitive.
Source: Hatcher, Theorem 2.10 and §3.1; upstream
`singularCochainComplex_exactAt_of_contractible` at `2ead713`. -/
theorem cech_vertical_one (n : ℕ) (S : Set (Fin n → ℂ)) (hc : Convex ℝ S)
    (F : cech_simplex n 1 → ℤ)
    (hF : ∀ σ, (∀ x, σ x ∈ S) → cech_d n 1 F σ = 0) :
    ∃ G : cech_simplex n 0 → ℤ,
      ∀ σ, (∀ x, σ x ∈ S) → cech_d n 0 G σ = F σ :=
  cech_vertical_one_aux n S hc F hF

/-- Closed singular zero-cochains on a convex subset are constant.
Source: Hatcher, §3.1, degree-zero cohomology and paths. -/
theorem cech_vertical_zero (n : ℕ) (S : Set (Fin n → ℂ)) (hc : Convex ℝ S)
    (F : cech_simplex n 0 → ℤ)
    (hF : ∀ σ, (∀ x, σ x ∈ S) → cech_d n 0 F σ = 0) :
    ∃ k : ℤ, ∀ σ, (∀ x, σ x ∈ S) → F σ = k :=
  cech_vertical_zero_aux n S hc F hF

/-- A closed integral cover-small two-cochain on affine space has a cover-small primitive.
Source: Hatcher, Proposition 2.21 and Theorem 2.10; upstream
`coverSmallChainApproximation_of_openCover` at `2ead713`. -/
theorem cech_small_two (n : ℕ) (U : (Fin n → ℂ) → Set (Fin n → ℂ))
    (hU : ∀ p, IsOpen (U p)) (hcover : ∀ p, p ∈ U p)
    (F : cech_simplex n 2 → ℤ)
    (hF : ∀ σ, (∃ p, ∀ x, σ x ∈ U p) → cech_d n 2 F σ = 0) :
    ∃ G : cech_simplex n 1 → ℤ,
      ∀ σ, (∃ p, ∀ x, σ x ∈ U p) → cech_d n 1 G σ = F σ :=
  cech_small_two_aux n U hU hcover F hF

/-- Integral two-cocycles on a convex open cover of affine space have integral primitives.
Source: Bott--Tu, §§8--9, the Čech double complex; the degree-two diagram chase
using `cech_horizontal_exact`, `cech_horizontal_glue`, `cech_vertical_one`,
`cech_vertical_zero`, and `cech_small_two`. -/
theorem cech_integral_primitive (n : ℕ) (V : (Fin n → ℂ) → Set (Fin n → ℂ))
    (hV : ∀ p, IsOpen (V p)) (hcover : ∀ p, p ∈ V p)
    (hv : ∀ p, Convex ℝ (V p))
    (c : (Fin n → ℂ) → (Fin n → ℂ) → (Fin n → ℂ) → ℤ)
    (hc : ∀ p q r s z, z ∈ V p ∩ V q ∩ V r ∩ V s →
      c q r s - c p r s + c p q s - c p q r = 0) :
    ∃ k : (Fin n → ℂ) → (Fin n → ℂ) → ℤ,
      ∀ p q r z, z ∈ V p ∩ V q ∩ V r →
        k q r - k p r + k p q = c p q r :=
  cech_integral_primitive_aux n V hV hcover hv c hc

/-- Subtracting the integral primitive makes the logarithms additive without changing exponentials.
Source: Gunning--Rossi, VIII, the exponential sequence; direct cancellation of the defect. -/
theorem cech_correct_logarithms (n : ℕ) (V : (Fin n → ℂ) → Set (Fin n → ℂ))
    (u b : (Fin n → ℂ) → (Fin n → ℂ) → (Fin n → ℂ) → ℂ)
    (k : (Fin n → ℂ) → (Fin n → ℂ) → ℤ)
    (hb : ∀ p q, AnalyticOnNhd ℂ (b p q) (V p ∩ V q))
    (he : ∀ p q z, z ∈ V p ∩ V q → Complex.exp (b p q z) = u p q z)
    (hd : ∀ p q r z, z ∈ V p ∩ V q ∩ V r →
      b q r z - b p r z + b p q z =
        (2 * Real.pi * Complex.I) * ((k q r - k p r + k p q : ℤ) : ℂ)) :
    (∀ p q, AnalyticOnNhd ℂ (cech_correct n b k p q) (V p ∩ V q)) ∧
      (∀ p z, z ∈ V p → cech_correct n b k p p z = 0) ∧
      (∀ p q r z, z ∈ V p ∩ V q ∩ V r →
        cech_correct n b k p q z + cech_correct n b k q r z = cech_correct n b k p r z) ∧
      (∀ p q z, z ∈ V p ∩ V q → Complex.exp (cech_correct n b k p q z) = u p q z) :=
  cech_correct_logarithms_aux n V u b k hb he hd

/-- A multiplicative cocycle has an additive logarithmic lift after refinement.
Source: Gunning--Rossi, VIII, exponential sequence and Cousin II.
This is the exact type of `bh7_exponential_trivialization_aux`. -/
theorem cech_exponential_trivialization (n : ℕ)
    (U : (Fin n → ℂ) → Set (Fin n → ℂ))
    (hU : ∀ p, IsOpen (U p)) (hcover : ∀ p, p ∈ U p)
    (u : (Fin n → ℂ) → (Fin n → ℂ) → (Fin n → ℂ) → ℂ)
    (hu : ∀ p q, AnalyticOnNhd ℂ (u p q) (U p ∩ U q))
    (hun : ∀ p q z, z ∈ U p ∩ U q → u p q z ≠ 0)
    (hdiag : ∀ p z, z ∈ U p → u p p z = 1)
    (hcocycle : ∀ p q r z, z ∈ U p ∩ U q ∩ U r → u p q z * u q r z = u p r z) :
    ∃ (V : (Fin n → ℂ) → Set (Fin n → ℂ)) (r : (Fin n → ℂ) → (Fin n → ℂ))
      (a : (Fin n → ℂ) → (Fin n → ℂ) → (Fin n → ℂ) → ℂ),
      (∀ p, IsOpen (V p)) ∧ (∀ p, p ∈ V p) ∧ (∀ p, V p ⊆ U (r p)) ∧
      (∀ p q, AnalyticOnNhd ℂ (a p q) (V p ∩ V q)) ∧
      (∀ p z, z ∈ V p → a p p z = 0) ∧
      (∀ p q t z, z ∈ V p ∩ V q ∩ V t → a p q z + a q t z = a p t z) ∧
      (∀ p q z, z ∈ V p ∩ V q → Complex.exp (a p q z) = u (r p) (r q) z) :=
  cech_exponential_trivialization_aux n U hU hcover u hu hun hdiag hcocycle


/-! ## Constructed witnesses -/

-- cech_witness_convex_refinement
example :
    ∃ V : (Fin 0 → ℂ) → Set (Fin 0 → ℂ),
      (∀ p, IsOpen (V p)) ∧ (∀ p, p ∈ V p) ∧
      (∀ p, Convex ℝ (V p)) ∧ (∀ p, V p ⊆ (fun _ ↦ Set.univ) p) :=
  cech_convex_refinement 0 (fun _ ↦ Set.univ) (fun _ ↦ isOpen_univ) (fun _ ↦ Set.mem_univ _)

-- cech_witness_convex_log
example :
    ∃ b : (Fin 1 → ℂ) → ℂ,
      AnalyticOnNhd ℂ b (Metric.ball 0 1) ∧ ∀ z ∈ (Metric.ball 0 1), Complex.exp (b z) = (fun _ ↦ 1) z :=
  cech_convex_log 1 (Metric.ball 0 1) Metric.isOpen_ball (convex_ball 0 1) (fun _ ↦ 1) (fun _ _ ↦ analyticAt_const) (by intros; exact one_ne_zero)

-- cech_witness_integer_defect
example :
    ∃ c : (Fin 1 → ℂ) → (Fin 1 → ℂ) → (Fin 1 → ℂ) → ℤ,
      (∀ p q r z, z ∈ (fun p ↦ Metric.ball p 1) p ∩ (fun p ↦ Metric.ball p 1) q ∩ (fun p ↦ Metric.ball p 1) r →
        (fun _ _ _ ↦ 0) q r z - (fun _ _ _ ↦ 0) p r z + (fun _ _ _ ↦ 0) p q z = (2 * Real.pi * Complex.I) * (c p q r : ℂ)) ∧
      (∀ p q r s z, z ∈ (fun p ↦ Metric.ball p 1) p ∩ (fun p ↦ Metric.ball p 1) q ∩ (fun p ↦ Metric.ball p 1) r ∩ (fun p ↦ Metric.ball p 1) s →
        c q r s - c p r s + c p q s - c p q r = 0) :=
  cech_integer_defect 1 (fun p ↦ Metric.ball p 1) (fun _ ↦ Metric.isOpen_ball) (fun p ↦ convex_ball p 1) (fun _ _ _ ↦ 1) (fun _ _ _ ↦ 0) (fun _ _ _ _ ↦ analyticAt_const) (by intros; simp) (by intros; simp)

-- cech_witness_horizontal_exact
example :
    ∃ G : (Fin (0 + 1) → (Fin 0 → ℂ)) → cech_simplex 0 0 → ℤ,
      ∀ t σ, (∀ x i, σ x ∈ (fun _ ↦ Set.univ) (t i)) → cech_h 0 0 G t σ = (fun _ _ ↦ 0) t σ :=
  cech_horizontal_exact 0 0 0 (fun _ ↦ Set.univ) (fun _ _ ↦ 0) (by intros; simp [cech_h])

-- cech_witness_horizontal_glue
example :
    ∃ G : cech_simplex 0 0 → ℤ,
      ∀ (t : Fin 1 → (Fin 0 → ℂ)) (σ : cech_simplex 0 0),
        (∀ x i, σ x ∈ (fun _ ↦ Set.univ) (t i)) → G σ = (fun _ _ ↦ 0) t σ :=
  cech_horizontal_glue 0 0 (fun _ ↦ Set.univ) (fun _ _ ↦ 0) (by intros; simp [cech_h])

-- cech_witness_vertical_one
example :
    ∃ G : cech_simplex 1 0 → ℤ,
      ∀ σ, (∀ x, σ x ∈ (Metric.ball 0 1)) → cech_d 1 0 G σ = (fun _ ↦ 0) σ :=
  cech_vertical_one 1 (Metric.ball 0 1) (convex_ball 0 1) (fun _ ↦ 0) (by intros; simp [cech_d])

-- cech_witness_vertical_zero
example :
    ∃ k : ℤ, ∀ (σ : cech_simplex 1 0), (∀ x, σ x ∈ (Metric.ball 0 1)) → (fun _ ↦ 7) σ = k :=
  cech_vertical_zero 1 (Metric.ball 0 1) (convex_ball 0 1) (fun _ ↦ 7) (by intros; simp [cech_d, Fin.sum_univ_two])

-- cech_witness_small_two
example :
    ∃ G : cech_simplex 1 1 → ℤ,
      ∀ σ, (∃ p, ∀ x, σ x ∈ (fun p ↦ Metric.ball p 1) p) → cech_d 1 1 G σ = (fun _ ↦ 0) σ :=
  cech_small_two 1 (fun p ↦ Metric.ball p 1) (fun _ ↦ Metric.isOpen_ball) (by intro p; simp) (fun _ ↦ 0) (by intros; simp [cech_d])

-- cech_witness_integral_primitive
example :
    ∃ k : (Fin 1 → ℂ) → (Fin 1 → ℂ) → ℤ,
      ∀ p q r z, z ∈ (fun p ↦ Metric.ball p 1) p ∩ (fun p ↦ Metric.ball p 1) q ∩ (fun p ↦ Metric.ball p 1) r →
        k q r - k p r + k p q = (fun _ _ _ ↦ 1) p q r :=
  cech_integral_primitive 1 (fun p ↦ Metric.ball p 1) (fun _ ↦ Metric.isOpen_ball) (by intro p; simp) (fun p ↦ convex_ball p 1) (fun _ _ _ ↦ 1) (by intros; norm_num)

-- cech_witness_correct_logarithms
example :
    (∀ p q, AnalyticOnNhd ℂ (cech_correct 1 (fun _ _ _ ↦ 0) (fun _ _ ↦ 0) p q) ((fun p ↦ Metric.ball p 1) p ∩ (fun p ↦ Metric.ball p 1) q)) ∧
      (∀ p z, z ∈ (fun p ↦ Metric.ball p 1) p → cech_correct 1 (fun _ _ _ ↦ 0) (fun _ _ ↦ 0) p p z = 0) ∧
      (∀ p q r z, z ∈ (fun p ↦ Metric.ball p 1) p ∩ (fun p ↦ Metric.ball p 1) q ∩ (fun p ↦ Metric.ball p 1) r →
        cech_correct 1 (fun _ _ _ ↦ 0) (fun _ _ ↦ 0) p q z + cech_correct 1 (fun _ _ _ ↦ 0) (fun _ _ ↦ 0) q r z = cech_correct 1 (fun _ _ _ ↦ 0) (fun _ _ ↦ 0) p r z) ∧
      (∀ p q z, z ∈ (fun p ↦ Metric.ball p 1) p ∩ (fun p ↦ Metric.ball p 1) q → Complex.exp (cech_correct 1 (fun _ _ _ ↦ 0) (fun _ _ ↦ 0) p q z) = (fun _ _ _ ↦ 1) p q z) :=
  cech_correct_logarithms 1 (fun p ↦ Metric.ball p 1) (fun _ _ _ ↦ 1) (fun _ _ _ ↦ 0) (fun _ _ ↦ 0) (fun _ _ _ _ ↦ analyticAt_const) (by intros; simp) (by intros; simp)

-- cech_witness_exponential_trivialization
example :
    ∃ (V : (Fin 0 → ℂ) → Set (Fin 0 → ℂ)) (r : (Fin 0 → ℂ) → (Fin 0 → ℂ))
      (a : (Fin 0 → ℂ) → (Fin 0 → ℂ) → (Fin 0 → ℂ) → ℂ),
      (∀ p, IsOpen (V p)) ∧ (∀ p, p ∈ V p) ∧ (∀ p, V p ⊆ (fun _ ↦ Set.univ) (r p)) ∧
      (∀ p q, AnalyticOnNhd ℂ (a p q) (V p ∩ V q)) ∧
      (∀ p z, z ∈ V p → a p p z = 0) ∧
      (∀ p q t z, z ∈ V p ∩ V q ∩ V t → a p q z + a q t z = a p t z) ∧
      (∀ p q z, z ∈ V p ∩ V q → Complex.exp (a p q z) = (fun _ _ _ ↦ 1) (r p) (r q) z) :=
  cech_exponential_trivialization 0 (fun _ ↦ Set.univ) (fun _ ↦ isOpen_univ) (fun _ ↦ Set.mem_univ _) (fun _ _ _ ↦ 1) (fun _ _ _ _ ↦ analyticAt_const) (by intros; exact one_ne_zero) (by intros; rfl) (by intros; simp)

end HodgeLean.Foundations
