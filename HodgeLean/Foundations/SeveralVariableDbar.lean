import HodgeLean.Foundations.SeveralVariableDbarProofs

/-! # Several-variable ∂̄ and additive Cousin (frozen specification)

An implication from smooth closed coordinate forms to global primitives, and from analytic
additive cocycles to holomorphic potentials, on every finite-dimensional affine complex space.
The analytic obligations are open in the companion proofs module. No algebraic cycles or
projective comparison are asserted. HC no distance; AV milestone no distance.
-/

noncomputable section
open Set Filter Topology
open scoped ContDiff
namespace HodgeLean.Foundations

/-- Smooth partition of unity splits an analytic additive cocycle.
Source: Gunning--Rossi, Chapter VIII, the partition-of-unity construction of Cousin I. -/
theorem dbar_smooth_split (n : ℕ)
    (U : (Fin n → ℂ) → Set (Fin n → ℂ))
    (hU : ∀ p, IsOpen (U p)) (hcover : ∀ p, p ∈ U p)
    (a : (Fin n → ℂ) → (Fin n → ℂ) → (Fin n → ℂ) → ℂ)
    (ha : ∀ p q, AnalyticOnNhd ℂ (a p q) (U p ∩ U q))
    (hcocycle : ∀ p q r z, z ∈ U p ∩ U q ∩ U r →
      a p q z + a q r z = a p r z) :
    ∃ b : (Fin n → ℂ) → (Fin n → ℂ) → ℂ,
      (∀ p z, z ∈ U p → ContDiffAt ℝ ∞ (b p) z) ∧
      (∀ p q z, z ∈ U p ∩ U q → a p q z = b q z - b p z) :=
  dbar_smooth_split_aux n U hU hcover a ha hcocycle

/-- The anchored coefficients glue smoothly and are closed.
Source: Gunning--Rossi, Chapter VIII, Dolbeault construction; symmetry of second derivatives. -/
theorem dbar_glue (n : ℕ)
    (U : (Fin n → ℂ) → Set (Fin n → ℂ))
    (hU : ∀ p, IsOpen (U p)) (hcover : ∀ p, p ∈ U p)
    (a : (Fin n → ℂ) → (Fin n → ℂ) → (Fin n → ℂ) → ℂ)
    (ha : ∀ p q, AnalyticOnNhd ℂ (a p q) (U p ∩ U q))
    (c : (Fin n → ℂ) → (Fin n → ℂ) → ℂ)
    (hc : ∀ p z, z ∈ U p → ContDiffAt ℝ ∞ (c p) z)
    (he : ∀ p q z, z ∈ U p ∩ U q → a p q z = c q z - c p z) :
    (∀ j, ContDiff ℝ ∞ (dbar_glued n c j)) ∧
      (∀ p j z, z ∈ U p → dbar_glued n c j z = dbar_coord n j (c p) z) ∧
      (∀ j k z, dbar_coord n k (dbar_glued n c j) z =
        dbar_coord n j (dbar_glued n c k) z) :=
  dbar_glue_aux n U hU hcover a ha c hc he

/-- The coordinate Cauchy transform is smooth and commutes with transverse derivatives.
Source: Hörmander, 3rd ed., §2.3, Cauchy transform with parameters;
Mathlib, hasFDerivAt_integral_of_dominated_of_fderiv_le. -/
theorem dbar_transform_calculus (n : ℕ) (j : Fin n)
    (f : (Fin n → ℂ) → ℂ) (hf : ContDiff ℝ ∞ f)
    (R : ℝ) (hR : 0 < R) (hs : ∀ z, R ≤ ‖z j‖ → f z = 0) :
    ContDiff ℝ ∞ (dbar_transform n j f) ∧
      (∀ k, k ≠ j → ∀ z, dbar_coord n k (dbar_transform n j f) z =
        dbar_transform n j (dbar_coord n k f) z) :=
  dbar_transform_calculus_aux n j f hf R hR hs

/-- The coordinate Cauchy transform solves the selected component equation.
Source: Hörmander, 3rd ed., Theorem 1.2.2;
HodgeLean.Foundations.spec_wirtingerDbar_cauchyTransform. -/
theorem dbar_transform_equation (n : ℕ) (j : Fin n)
    (f : (Fin n → ℂ) → ℂ) (hf : ContDiff ℝ ∞ f)
    (R : ℝ) (hR : 0 < R) (hs : ∀ z, R ≤ ‖z j‖ → f z = 0) :
    ∀ z, dbar_coord n j (dbar_transform n j f) z = f z :=
  dbar_transform_equation_aux n j f hf R hR hs

/-- One coordinate correction preserves the previously solved components on a smaller polydisc.
Source: Hörmander, 3rd ed., §2.3, successive Cauchy transforms; Gunning--Rossi, I.D. -/
theorem dbar_eliminate_coordinate (n : ℕ) (k : Fin n)
    (w : Fin n → (Fin n → ℂ) → ℂ) (r R : ℝ) (hr : 0 < r) (hrR : r < R)
    (hw : ∀ j z, z ∈ Metric.ball 0 R → ContDiffAt ℝ ∞ (w j) z)
    (hclosed : ∀ j l z, z ∈ Metric.ball 0 R →
      dbar_coord n l (w j) z = dbar_coord n j (w l) z)
    (u : (Fin n → ℂ) → ℂ) (hu : ContDiff ℝ ∞ u)
    (hprev : ∀ j : Fin n, j.val < k.val → ∀ z, z ∈ Metric.ball 0 R →
      dbar_coord n j u z = w j z) :
    ∃ v : (Fin n → ℂ) → ℂ, ContDiff ℝ ∞ v ∧
      ∀ j : Fin n, j.val ≤ k.val → ∀ z, z ∈ Metric.ball 0 r →
        dbar_coord n j v z = w j z :=
  dbar_eliminate_coordinate_aux n k w r R hr hrR hw hclosed u hu hprev

/-- A closed smooth form has a smooth primitive on a smaller polydisc.
Source: Hörmander, 3rd ed., §2.3, the polydisc ∂̄ lemma; Gunning--Rossi, I.D. -/
theorem dbar_polydisc (n : ℕ) (w : Fin n → (Fin n → ℂ) → ℂ)
    (r R : ℝ) (hr : 0 < r) (hrR : r < R)
    (hw : ∀ j z, z ∈ Metric.ball 0 R → ContDiffAt ℝ ∞ (w j) z)
    (hclosed : ∀ j k z, z ∈ Metric.ball 0 R →
      dbar_coord n k (w j) z = dbar_coord n j (w k) z) :
    ∃ u : (Fin n → ℂ) → ℂ, ContDiff ℝ ∞ u ∧
      ∀ j z, z ∈ Metric.ball 0 r → dbar_coord n j u z = w j z :=
  dbar_polydisc_aux n w r R hr hrR hw hclosed

/-- Taylor polynomials approximate on a strictly smaller closed polydisc.
Source: Gunning--Rossi, I, power series on polydiscs; Hörmander, 3rd ed., §2.2. -/
theorem dbar_polynomial_approximation (n : ℕ) (f : (Fin n → ℂ) → ℂ)
    (r R : ℝ) (hr : 0 < r) (hrR : r < R)
    (hf : AnalyticOnNhd ℂ f (Metric.ball 0 R)) (ε : ℝ) (hε : 0 < ε) :
    ∃ P : MvPolynomial (Fin n) ℂ,
      ∀ z, z ∈ Metric.closedBall 0 r → ‖f z - MvPolynomial.eval z P‖ < ε :=
  dbar_polynomial_approximation_aux n f r R hr hrR hf ε hε

/-- Polynomial corrections produce primitives with summable successive differences.
Source: Hörmander, 3rd ed., §2.3, exhaustion argument;
the one-variable recursion bh7_cousin_step14 at f59a809. -/
theorem dbar_exhaustion (n : ℕ) (w : Fin n → (Fin n → ℂ) → ℂ)
    (hw : ∀ j, ContDiff ℝ ∞ (w j))
    (hclosed : ∀ j k z, dbar_coord n k (w j) z = dbar_coord n j (w k) z) :
    ∃ u : ℕ → (Fin n → ℂ) → ℂ,
      (∀ m, ContDiff ℝ ∞ (u m)) ∧
      (∀ (m : ℕ) j z, z ∈ Metric.ball 0 ((m : ℝ) + 2) →
        dbar_coord n j (u m) z = w j z) ∧
      (∀ (m : ℕ) z, z ∈ Metric.ball 0 ((m : ℝ) + 1) →
        ‖u (m + 1) z - u m z‖ < (1 / 2 : ℝ) ^ m) :=
  dbar_exhaustion_aux n w hw hclosed

/-- Controlled primitives converge locally uniformly to a smooth global primitive.
Source: Hörmander, 3rd ed., §2.3, exhaustion; holomorphic locally uniform limits;
the one-variable telescoping argument bh7_cousin_step15 at f59a809. -/
theorem dbar_exhaustion_limit (n : ℕ) (w : Fin n → (Fin n → ℂ) → ℂ)
    (u : ℕ → (Fin n → ℂ) → ℂ) (hu : ∀ m, ContDiff ℝ ∞ (u m))
    (he : ∀ (m : ℕ) j z, z ∈ Metric.ball 0 ((m : ℝ) + 2) →
      dbar_coord n j (u m) z = w j z)
    (hc : ∀ (m : ℕ) z, z ∈ Metric.ball 0 ((m : ℝ) + 1) →
      ‖u (m + 1) z - u m z‖ < (1 / 2 : ℝ) ^ m) :
    ∃ g : (Fin n → ℂ) → ℂ, ContDiff ℝ ∞ g ∧
      TendstoLocallyUniformly u g atTop ∧
      ∀ j z, dbar_coord n j g z = w j z :=
  dbar_exhaustion_limit_aux n w u hu he hc

/-- Vanishing coordinate conjugate derivatives give holomorphy on an open set.
Source: Hörmander, 3rd ed., §2.2, Cauchy--Riemann equations;
HodgeLean.Foundations.AnalyticDivisorAlgebraic2.spec_analyticOnNhd_of_differentiableOn_fin. -/
theorem dbar_holomorphic (n : ℕ) (V : Set (Fin n → ℂ)) (hV : IsOpen V)
    (f : (Fin n → ℂ) → ℂ) (hf : ∀ z, z ∈ V → DifferentiableAt ℝ f z)
    (hd : ∀ j z, z ∈ V → dbar_coord n j f z = 0) :
    AnalyticOnNhd ℂ f V :=
  dbar_holomorphic_aux n V hV f hf hd

/-- Every smooth closed (0,1)-form on affine complex space has a global smooth primitive.
Source: Hörmander, 3rd ed., §2.3; composition of controlled exhaustion and its limit. -/
theorem dbar_global (n : ℕ) (w : Fin n → (Fin n → ℂ) → ℂ)
    (hw : ∀ j, ContDiff ℝ ∞ (w j))
    (hclosed : ∀ j k z, dbar_coord n k (w j) z = dbar_coord n j (w k) z) :
    ∃ g : (Fin n → ℂ) → ℂ, ContDiff ℝ ∞ g ∧
      ∀ j z, dbar_coord n j g z = w j z :=
  dbar_global_aux n w hw hclosed

/-- Additive holomorphic cocycles on affine complex space are coboundaries.
Source: Gunning--Rossi, Chapter VIII, Cartan theorem B and the first Cousin problem. -/
theorem dbar_cousin_additive (n : ℕ)
    (U : (Fin n → ℂ) → Set (Fin n → ℂ))
    (hU : ∀ p, IsOpen (U p)) (hcover : ∀ p, p ∈ U p)
    (a : (Fin n → ℂ) → (Fin n → ℂ) → (Fin n → ℂ) → ℂ)
    (ha : ∀ p q, AnalyticOnNhd ℂ (a p q) (U p ∩ U q))
    (hdiag : ∀ p z, z ∈ U p → a p p z = 0)
    (hcocycle : ∀ p q r z, z ∈ U p ∩ U q ∩ U r → a p q z + a q r z = a p r z) :
    ∃ b : (Fin n → ℂ) → (Fin n → ℂ) → ℂ,
      (∀ p, AnalyticOnNhd ℂ (b p) (U p)) ∧
      (∀ p q z, z ∈ U p ∩ U q → a p q z = b q z - b p z) :=
  dbar_cousin_additive_aux n U hU hcover a ha hdiag hcocycle

/-! ## Constructed-premise examples -/

/-- Two half spaces selected by the sign of the anchor's first real coordinate.
Source: elementary open-cover example for Cousin I. -/
def dbar_twoCover (p : Fin 2 → ℂ) : Set (Fin 2 → ℂ) :=
  if (p 0).re < 0 then {z | (z 0).re < 1} else {z | -1 < (z 0).re}

example : dbar_twoCover (fun _ ↦ -1) = {z | (z 0).re < 1} := by
  norm_num [dbar_twoCover]

/-- The two-set cover consists of open sets.
Source: continuity of coordinate projections and real part. -/
theorem dbar_twoCover_open (p : Fin 2 → ℂ) : IsOpen (dbar_twoCover p) := by
  unfold dbar_twoCover
  split_ifs
  · exact isOpen_lt (Complex.continuous_re.comp (continuous_apply 0)) continuous_const
  · exact isOpen_lt continuous_const (Complex.continuous_re.comp (continuous_apply 0))

/-- Every anchor belongs to its selected half space.
Source: the inequalities defining the two-set cover. -/
theorem dbar_twoCover_anchor (p : Fin 2 → ℂ) : p ∈ dbar_twoCover p := by
  unfold dbar_twoCover
  split_ifs with h <;> simp only [mem_ofPred_eq] <;> linarith

/-- A spatially varying additive cocycle on the two-set cover.
Source: the coboundary of the explicit functions `p 0 * z 1`. -/
def dbar_twoCocycle (p q z : Fin 2 → ℂ) : ℂ := (q 0 - p 0) * z 1

example : dbar_twoCocycle (fun _ ↦ 0) (fun _ ↦ 1) (fun _ ↦ 1) = 1 := by
  norm_num [dbar_twoCocycle]

/-- The constructed cocycle is analytic on every overlap.
Source: analyticity of continuous complex-linear maps and multiplication. -/
theorem dbar_twoCocycle_analytic (p q : Fin 2 → ℂ) :
    AnalyticOnNhd ℂ (dbar_twoCocycle p q) (dbar_twoCover p ∩ dbar_twoCover q) := by
  intro z _
  exact analyticAt_const.mul ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 2 ↦ ℂ) 1).analyticAt z)

/-- The constructed cocycle satisfies its triple-overlap identity everywhere.
Source: subtraction in the additive group of holomorphic functions. -/
theorem dbar_twoCocycle_identity (p q r z : Fin 2 → ℂ) :
    dbar_twoCocycle p q z + dbar_twoCocycle q r z = dbar_twoCocycle p r z := by
  unfold dbar_twoCocycle
  ring

-- Witness W1: the partition construction, with a nonzero cocycle on two proper opens.
example : ∃ c : (Fin 2 → ℂ) → (Fin 2 → ℂ) → ℂ,
    (∀ p z, z ∈ dbar_twoCover p → ContDiffAt ℝ ∞ (c p) z) ∧
    (∀ p q z, z ∈ dbar_twoCover p ∩ dbar_twoCover q →
      dbar_twoCocycle p q z = c q z - c p z) :=
  dbar_smooth_split 2 dbar_twoCover dbar_twoCover_open dbar_twoCover_anchor
    dbar_twoCocycle dbar_twoCocycle_analytic (fun p q r z _ ↦ dbar_twoCocycle_identity p q r z)

-- Witness W2: gluing constant local potentials, supplying every overlap premise.
example (n : ℕ) :
    (∀ j, ContDiff ℝ ∞ (dbar_glued n (fun _ _ ↦ 0) j)) ∧
    (∀ (_p : Fin n → ℂ) j z, z ∈ (univ : Set (Fin n → ℂ)) →
      dbar_glued n (fun _ _ ↦ 0) j z = dbar_coord n j (fun _ ↦ 0) z) ∧
    (∀ j k z, dbar_coord n k (dbar_glued n (fun _ _ ↦ 0) j) z =
      dbar_coord n j (dbar_glued n (fun _ _ ↦ 0) k) z) :=
  dbar_glue n (fun _ ↦ univ) (fun _ ↦ isOpen_univ) (fun _ ↦ mem_univ _)
    (fun _ _ _ ↦ 0) (fun _ _ _ _ ↦ analyticAt_const) (fun _ _ ↦ 0)
    (fun _ _ _ ↦ contDiffAt_const) (by intros; simp)

-- Witnesses W3 and W4: compactly supported zero input for each transform statement.
example : ContDiff ℝ ∞ (dbar_transform 2 0 (fun _ ↦ 0)) ∧
    (∀ k, k ≠ (0 : Fin 2) → ∀ z,
      dbar_coord 2 k (dbar_transform 2 0 (fun _ ↦ 0)) z =
        dbar_transform 2 0 (dbar_coord 2 k (fun _ ↦ 0)) z) :=
  dbar_transform_calculus 2 0 (fun _ ↦ 0) contDiff_const 1 (by norm_num) (by intros; rfl)

example : ∀ z, dbar_coord 2 0 (dbar_transform 2 0 (fun _ ↦ 0)) z = 0 :=
  dbar_transform_equation 2 0 (fun _ ↦ 0) contDiff_const 1 (by norm_num) (by intros; rfl)

-- Witness W5: the second elimination step has a genuinely inhabited earlier-coordinate set.
example : ∃ v : (Fin 2 → ℂ) → ℂ, ContDiff ℝ ∞ v ∧
    ∀ j : Fin 2, j.val ≤ (1 : Fin 2).val → ∀ z, z ∈ Metric.ball 0 1 →
      dbar_coord 2 j v z = 0 :=
  dbar_eliminate_coordinate 2 1 (fun _ _ ↦ 0) 1 2 (by norm_num) (by norm_num)
    (fun _ _ _ ↦ contDiffAt_const) (by intros; simp [dbar_coord])
    (fun _ ↦ 0) contDiff_const (by intros; simp [dbar_coord])

-- Witness W6: a nonzero closed form on a two-dimensional polydisc.
example : ∃ u : (Fin 2 → ℂ) → ℂ, ContDiff ℝ ∞ u ∧
    ∀ j z, z ∈ Metric.ball 0 1 → dbar_coord 2 j u z = 1 :=
  dbar_polydisc 2 (fun _ _ ↦ 1) 1 2 (by norm_num) (by norm_num)
    (fun _ _ _ ↦ contDiffAt_const) (by intros; simp [dbar_coord])

-- Witness W7: approximation includes nonzero constant holomorphic functions.
example : ∃ P : MvPolynomial (Fin 2) ℂ,
    ∀ z, z ∈ Metric.closedBall 0 1 → ‖(1 : ℂ) - MvPolynomial.eval z P‖ < 1 :=
  dbar_polynomial_approximation 2 (fun _ ↦ 1) 1 2 (by norm_num) (by norm_num)
    (fun _ _ ↦ analyticAt_const) 1 (by norm_num)

-- Witness W8: the exhaustion accepts a nonzero closed form.
example : ∃ u : ℕ → (Fin 2 → ℂ) → ℂ,
    (∀ m, ContDiff ℝ ∞ (u m)) ∧
    (∀ (m : ℕ) j z, z ∈ Metric.ball 0 ((m : ℝ) + 2) → dbar_coord 2 j (u m) z = 1) ∧
    (∀ (m : ℕ) z, z ∈ Metric.ball 0 ((m : ℝ) + 1) →
      ‖u (m + 1) z - u m z‖ < (1 / 2 : ℝ) ^ m) :=
  dbar_exhaustion 2 (fun _ _ ↦ 1) (fun _ ↦ contDiff_const)
    (by intros; simp [dbar_coord])

-- Witness W9: an independently constructed sequence, with all estimates checked.
example : ∃ g : (Fin 2 → ℂ) → ℂ, ContDiff ℝ ∞ g ∧
    TendstoLocallyUniformly (fun (_ : ℕ) (_ : Fin 2 → ℂ) ↦ (0 : ℂ)) g atTop ∧
    ∀ j z, dbar_coord 2 j g z = 0 :=
  dbar_exhaustion_limit 2 (fun _ _ ↦ 0) (fun _ _ ↦ 0) (fun _ ↦ contDiff_const)
    (by intros; simp [dbar_coord]) (by intros; simp only [sub_self, norm_zero]; positivity)

-- Witness W10: holomorphy, with a nonzero smooth function and checked derivatives.
example : AnalyticOnNhd ℂ (fun _ : Fin 2 → ℂ ↦ (1 : ℂ)) univ :=
  dbar_holomorphic 2 univ isOpen_univ (fun _ ↦ 1) (fun _ _ ↦ differentiableAt_const _)
    (by intros; simp [dbar_coord])

-- Witness W11: nonzero closed coefficients and the global solver.
example : (∀ j k z, dbar_coord 2 k (fun _ ↦ (1 : ℂ)) z =
    dbar_coord 2 j (fun _ ↦ (1 : ℂ)) z) ∧
    ∃ g : (Fin 2 → ℂ) → ℂ, ContDiff ℝ ∞ g ∧ ∀ j z, dbar_coord 2 j g z = 1 := by
  have hclosed : ∀ j k z, dbar_coord 2 k (fun _ ↦ (1 : ℂ)) z =
      dbar_coord 2 j (fun _ ↦ (1 : ℂ)) z := by intros; simp [dbar_coord]
  exact ⟨hclosed, dbar_global 2 (fun _ _ ↦ 1) (fun _ ↦ contDiff_const) hclosed⟩

-- Witness W12: the exact consumer with a spatially varying cocycle and two proper opens.
example : ∃ b : (Fin 2 → ℂ) → (Fin 2 → ℂ) → ℂ,
    (∀ p, AnalyticOnNhd ℂ (b p) (dbar_twoCover p)) ∧
    (∀ p q z, z ∈ dbar_twoCover p ∩ dbar_twoCover q →
      dbar_twoCocycle p q z = b q z - b p z) :=
  dbar_cousin_additive 2 dbar_twoCover dbar_twoCover_open dbar_twoCover_anchor
    dbar_twoCocycle dbar_twoCocycle_analytic (by intros; simp [dbar_twoCocycle])
    (fun p q r z _ ↦ dbar_twoCocycle_identity p q r z)

-- Witness W13: dimension zero and the trivial cocycle are allowed inputs.
example : ∃ b : (Fin 0 → ℂ) → (Fin 0 → ℂ) → ℂ,
    (∀ p, AnalyticOnNhd ℂ (b p) univ) ∧ (∀ p q z, (0 : ℂ) = b q z - b p z) := by
  obtain ⟨b, hb, he⟩ := dbar_cousin_additive 0 (fun _ ↦ univ) (fun _ ↦ isOpen_univ)
    (fun _ ↦ mem_univ _) (fun _ _ _ ↦ 0) (fun _ _ _ _ ↦ analyticAt_const)
    (by intros; rfl) (by intros; simp)
  exact ⟨b, hb, fun p q z ↦ he p q z ⟨mem_univ _, mem_univ _⟩⟩

end HodgeLean.Foundations
