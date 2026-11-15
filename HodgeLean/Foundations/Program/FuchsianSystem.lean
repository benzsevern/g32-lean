import HodgeLean.Foundations.Program.FuchsianSystemProofs

/-! # Fuchsian fundamental solutions and monodromy

Implication from a nonresonant residue and a holomorphic regular part to a local
fundamental solution, and from regular holomorphic coefficients to path continuation.
The finite-pole specialization gives a fundamental-group representation.
HC no distance; AV milestone no distance.
-/

noncomputable section
open Set Metric Filter
open scoped Topology
namespace HodgeLean.Foundations.Program

/-- Nonresonant local fundamental solution on the principal slit disc and its positive circular continuation. Mathlib-only.
Source: Ilyashenko–Yakovenko, Lectures on Analytic Differential Equations, §16, nonresonant Fuchsian normalization. -/
theorem b65f_local_normal_form (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E]
    (R : E →L[ℂ] E) (B : ℂ → E →L[ℂ] E) (a : ℂ) (d : ℝ)
    (hd : 0 < d) (hB : AnalyticOnNhd ℂ B (ball a d))
    (hnr : ∀ k : ℕ, 0 < k → Function.Bijective
      (fun T : E →L[ℂ] E ↦ (k : ℂ) • T - (R * T - T * R))) :
    ∃ r : ℝ, 0 < r ∧ r ≤ d ∧ ∃ H : ℂ → E →L[ℂ] E,
      AnalyticOnNhd ℂ H (ball a r) ∧ H a = 1 ∧
      (∀ z ∈ ball a r, IsUnit (H z)) ∧
      (∀ z ∈ ball a r, (z - a) • deriv H z =
        R * H z - H z * R + (z - a) • (B z * H z)) ∧
      (∀ z ∈ ball a r, z - a ∈ Complex.slitPlane →
        HasDerivAt (fun w ↦ H w * NormedSpace.exp (Complex.log (w - a) • R))
          (((z - a)⁻¹ • R + B z) *
            (H z * NormedSpace.exp (Complex.log (z - a) • R))) z) ∧
      ∀ ρ : ℝ, 0 < ρ → ρ < r →
        let Q := fun t : ℝ ↦ H (b65f_circle a ρ t) *
          NormedSpace.exp ((Complex.log (ρ : ℂ) +
            2 * Real.pi * Complex.I * (t : ℂ)) • R)
        (∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt Q
          ((2 * Real.pi * Complex.I * (b65f_circle a ρ t - a)) •
            (((b65f_circle a ρ t - a)⁻¹ • R + B (b65f_circle a ρ t)) * Q t)) t) ∧
        Q 1 = Q 0 * NormedSpace.exp ((2 * Real.pi * Complex.I) • R) ∧
        b65f_transport E (fun z ↦ (z - a)⁻¹ • R + B z) (b65f_circle a ρ) * Q 0 = Q 1 :=
  b65f_local_normal_form_aux E R B a d hd hB hnr

example (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E]
    (R : E →L[ℂ] E) (B : ℂ → E →L[ℂ] E) (a : ℂ) (d : ℝ)
    (hd : 0 < d) (hB : AnalyticOnNhd ℂ B (ball a d))
    (hnr : ∀ k : ℕ, 0 < k → Function.Bijective
      (fun T : E →L[ℂ] E ↦ (k : ℂ) • T - (R * T - T * R))) :
    ∃ r : ℝ, 0 < r ∧ r ≤ d ∧ ∃ H : ℂ → E →L[ℂ] E,
      AnalyticOnNhd ℂ H (ball a r) ∧ H a = 1 ∧
      (∀ z ∈ ball a r, IsUnit (H z)) ∧
      (∀ z ∈ ball a r, (z - a) • deriv H z =
        R * H z - H z * R + (z - a) • (B z * H z)) ∧
      (∀ z ∈ ball a r, z - a ∈ Complex.slitPlane →
        HasDerivAt (fun w ↦ H w * NormedSpace.exp (Complex.log (w - a) • R))
          (((z - a)⁻¹ • R + B z) *
            (H z * NormedSpace.exp (Complex.log (z - a) • R))) z) ∧
      ∀ ρ : ℝ, 0 < ρ → ρ < r →
        let Q := fun t : ℝ ↦ H (b65f_circle a ρ t) *
          NormedSpace.exp ((Complex.log (ρ : ℂ) +
            2 * Real.pi * Complex.I * (t : ℂ)) • R)
        (∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt Q
          ((2 * Real.pi * Complex.I * (b65f_circle a ρ t - a)) •
            (((b65f_circle a ρ t - a)⁻¹ • R + B (b65f_circle a ρ t)) * Q t)) t) ∧
        Q 1 = Q 0 * NormedSpace.exp ((2 * Real.pi * Complex.I) • R) ∧
        b65f_transport E (fun z ↦ (z - a)⁻¹ • R + B z) (b65f_circle a ρ) * Q 0 = Q 1 :=
  b65f_local_normal_form E R B a d hd hB hnr

/-- Dyson series agrees with the normalized regular fundamental solution. Mathlib-only.
Source: Hille, Ordinary Differential Equations in the Complex Domain, §2.3; b65_linear_system. -/
theorem b65f_segment_solution (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E]
    (A : ℂ → E →L[ℂ] E) (a : ℂ) (r : ℝ)
    (hr : 0 < r) (hA : AnalyticOnNhd ℂ A (ball a r)) :
    AnalyticOnNhd ℂ (b65f_segment E A a) (ball a r) ∧
      b65f_segment E A a a = 1 ∧
      (∀ z ∈ ball a r, Summable (fun m ↦ b65f_iterated E A a z m 1)) ∧
      (∀ z ∈ ball a r, HasDerivAt (b65f_segment E A a)
        (A z * b65f_segment E A a z) z) ∧
      ∀ z ∈ ball a r, IsUnit (b65f_segment E A a z) :=
  b65f_segment_solution_aux E A a r hr hA

example (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E]
    (A : ℂ → E →L[ℂ] E) (a : ℂ) (r : ℝ)
    (hr : 0 < r) (hA : AnalyticOnNhd ℂ A (ball a r)) :
    AnalyticOnNhd ℂ (b65f_segment E A a) (ball a r) ∧
      b65f_segment E A a a = 1 ∧
      (∀ z ∈ ball a r, Summable (fun m ↦ b65f_iterated E A a z m 1)) ∧
      (∀ z ∈ ball a r, HasDerivAt (b65f_segment E A a)
        (A z * b65f_segment E A a z) z) ∧
      ∀ z ∈ ball a r, IsUnit (b65f_segment E A a z) :=
  b65f_segment_solution E A a r hr hA

/-- Continuation along every continuous path in a regular domain. Mathlib-only.
Source: Ilyashenko–Yakovenko, Lectures on Analytic Differential Equations, §15, continuation along paths. -/
theorem b65f_path_convergence (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E]
    (U : Set ℂ) (hU : IsOpen U) (A : ℂ → E →L[ℂ] E)
    (hA : AnalyticOnNhd ℂ A U) (x y : U) (γ : Path x y) :
    Tendsto (b65f_polygon E A (fun t ↦ (γ.extend t).val)) atTop
      (𝓝 (b65f_transport E A (fun t ↦ (γ.extend t).val))) ∧
      IsUnit (b65f_transport E A (fun t ↦ (γ.extend t).val)) :=
  b65f_path_convergence_aux E U hU A hA x y γ

example (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E]
    (U : Set ℂ) (hU : IsOpen U) (A : ℂ → E →L[ℂ] E)
    (hA : AnalyticOnNhd ℂ A U) (x y : U) (γ : Path x y) :
    Tendsto (b65f_polygon E A (fun t ↦ (γ.extend t).val)) atTop
      (𝓝 (b65f_transport E A (fun t ↦ (γ.extend t).val))) ∧
      IsUnit (b65f_transport E A (fun t ↦ (γ.extend t).val)) :=
  b65f_path_convergence E U hU A hA x y γ

/-- Compatibility of path continuation with the regular disc solution. Mathlib-only.
Source: Hille, Ordinary Differential Equations in the Complex Domain, §2.3; uniqueness in b65_linear_system. -/
theorem b65f_disc_transport (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E]
    (A : ℂ → E →L[ℂ] E) (a : ℂ) (r : ℝ)
    (hr : 0 < r) (hA : AnalyticOnNhd ℂ A (ball a r))
    (y : ball a r) (γ : Path (⟨a, mem_ball_self hr⟩ : ball a r) y) :
    b65f_transport E A (fun t ↦ (γ.extend t).val) = b65f_segment E A a y.val :=
  b65f_disc_transport_aux E A a r hr hA y γ

example (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E]
    (A : ℂ → E →L[ℂ] E) (a : ℂ) (r : ℝ)
    (hr : 0 < r) (hA : AnalyticOnNhd ℂ A (ball a r))
    (y : ball a r) (γ : Path (⟨a, mem_ball_self hr⟩ : ball a r) y) :
    b65f_transport E A (fun t ↦ (γ.extend t).val) = b65f_segment E A a y.val :=
  b65f_disc_transport E A a r hr hA y γ

/-- Transport for successive paths, with column-vector convention. Mathlib-only.
Source: Ilyashenko–Yakovenko, Lectures on Analytic Differential Equations, §15, continuation along paths. -/
theorem b65f_path_composition (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E]
    (U : Set ℂ) (hU : IsOpen U) (A : ℂ → E →L[ℂ] E)
    (hA : AnalyticOnNhd ℂ A U) (x y z : U) (γ : Path x y) (δ : Path y z) :
    b65f_transport E A (fun t ↦ ((γ.trans δ).extend t).val) =
      b65f_transport E A (fun t ↦ (δ.extend t).val) *
        b65f_transport E A (fun t ↦ (γ.extend t).val) :=
  b65f_path_composition_aux E U hU A hA x y z γ δ

example (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E]
    (U : Set ℂ) (hU : IsOpen U) (A : ℂ → E →L[ℂ] E)
    (hA : AnalyticOnNhd ℂ A U) (x y z : U) (γ : Path x y) (δ : Path y z) :
    b65f_transport E A (fun t ↦ ((γ.trans δ).extend t).val) =
      b65f_transport E A (fun t ↦ (δ.extend t).val) *
        b65f_transport E A (fun t ↦ (γ.extend t).val) :=
  b65f_path_composition E U hU A hA x y z γ δ

/-- Homotopies fix both endpoints and stay in the regular domain. Mathlib-only.
Source: Ilyashenko–Yakovenko, Lectures on Analytic Differential Equations, §15, monodromy theorem. -/
theorem b65f_homotopy_invariance (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E]
    (U : Set ℂ) (hU : IsOpen U) (A : ℂ → E →L[ℂ] E)
    (hA : AnalyticOnNhd ℂ A U) (x y : U) (γ δ : Path x y)
    (h : γ.Homotopic δ) :
    b65f_transport E A (fun t ↦ (γ.extend t).val) =
      b65f_transport E A (fun t ↦ (δ.extend t).val) :=
  b65f_homotopy_invariance_aux E U hU A hA x y γ δ h

example (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E]
    (U : Set ℂ) (hU : IsOpen U) (A : ℂ → E →L[ℂ] E)
    (hA : AnalyticOnNhd ℂ A U) (x y : U) (γ δ : Path x y)
    (h : γ.Homotopic δ) :
    b65f_transport E A (fun t ↦ (γ.extend t).val) =
      b65f_transport E A (fun t ↦ (δ.extend t).val) :=
  b65f_homotopy_invariance E U hU A hA x y γ δ h

/-- Monodromy representation of the punctured plane into the general linear group of continuous endomorphisms. Mathlib-only.
Source: Ilyashenko–Yakovenko, Lectures on Analytic Differential Equations, §15; Mathlib FundamentalGroup.mul_def. -/
theorem b65f_monodromy_representation (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E]
    (s : Finset ℂ) (R : ℂ → E →L[ℂ] E) (x : {z : ℂ // z ∉ s}) :
    ∃ M : FundamentalGroup {z : ℂ // z ∉ s} x →* (E →L[ℂ] E)ˣ,
      ∀ γ : Path x x,
        (M (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk γ)) : E →L[ℂ] E) =
          b65f_transport E (b65f_coefficient E s R) (fun t ↦ (γ.extend t).val) :=
  b65f_monodromy_representation_aux E s R x

example (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E]
    (s : Finset ℂ) (R : ℂ → E →L[ℂ] E) (x : {z : ℂ // z ∉ s}) :
    ∃ M : FundamentalGroup {z : ℂ // z ∉ s} x →* (E →L[ℂ] E)ˣ,
      ∀ γ : Path x x,
        (M (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk γ)) : E →L[ℂ] E) =
          b65f_transport E (b65f_coefficient E s R) (fun t ↦ (γ.extend t).val) :=
  b65f_monodromy_representation E s R x

/-- Input test for the continuity and base membership fields of `g32r_PeriodMap`.
The shifted scalar Fuchsian coefficient gives ten illustrative coordinates.
Source: HodgeLean/Papers/G32DominanceDefs.lean, fields curve_cont and curve_zero. -/
example (V : Set (Fin 10 → ℂ)) (hV : (fun _ ↦ (1 : ℂ)) ∈ V) :
    ∃ curve : ℂ → Fin 10 → ℂ,
      (∀ θ i, curve θ i = (b65f_coefficient ℂ {0} (fun _ ↦ 1) (1 + θ)) 1) ∧
      ContinuousAt curve 0 ∧ curve 0 ∈ V ∧ curve 1 ≠ curve 0 := by
  refine ⟨fun θ _ ↦ (1 + θ)⁻¹, ?_, ?_, ?_, ?_⟩
  · intro θ i
    simp [b65f_coefficient]
  · fun_prop (disch := norm_num)
  · simpa using hV
  · intro h
    have h' := congrFun h (0 : Fin 10)
    norm_num at h'

end HodgeLean.Foundations.Program
