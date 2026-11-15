import HodgeLean.Foundations.Program.CoverAnalyticTwoProofs

/-! # Complex-analytic foundations for the cover dictionary, stage 2 (FROZEN SPEC)

Eight statements, prefix `caf_`, on the route selected by the amendment of
`docs/specs/CoverAnalytic.md` (the hybrid at moving poles and at `s = ∞`), toward bodies for
`b65g_dictionary_aux` and `b65g_cover_solutions_aux`. Specification: `docs/specs/CoverAnalyticTwo.md`.

Claimed:
1. two solutions of `Y' = A Y` on a connected open set, the second invertible, differ by a
   constant right factor;
2. two holomorphic `1`-forms on a Riemann surface that agree over the complement of a finite set
   are equal;
3. a function on the tangent bundle that is a holomorphic `1`-form over the complement of a
   finite set `F`, with bounded chart coefficient near each point of `F`, agrees there with a
   holomorphic `1`-form;
4. a connected surface charted on `ℂ` minus a finite set is path-connected;
5. (bridge (a)) the moving residues of a 5c record have trace `1/3` or `2/3` along the whole
   parameter disc, are diagonalizable with eigenvalues `0, 0, 0, λ`, and satisfy the
   non-resonance premise of `b65f_local_normal_form`;
6. (determinant equation) for an invertible meromorphic solution of
   `(z − z₀) Y' = (A₀ + (z − z₀) G) Y`, the order of `det Y` at `z₀` is an integer equal to
   `trace A₀`;
7. (character and order) a meromorphic germ of finite order `m` with `v(ζ y) = α v(y)` has
   `α = ζ^m`;
8. (determinant unit, bridge (b)) if `Y = H D` on a punctured neighbourhood, `H` analytic at
   `z₀`, `det D = (z − z₀)ⁿ`, and `det Y` has order `n`, then `H z₀` is invertible.

Statements 6–8 constrain functions only on punctured neighbourhoods (`𝓝[≠] z₀`), and
statements 2–3 only off the finite set: the value assigned at an excluded point (by the record
`b65g_Solutions`, whose fields `unit`, `ode`, `equivariant` hold only on the regular locus) is
never a premise, and every conclusion at an excluded point concerns a newly constructed
extension (`H` in statement 8, `θ'` in statement 3).

Not claimed: any statement about the cover family, the record `b65g_Solutions` or the dictionary
(later stages, planned in the specification); the transfer of `hT` to all-loop monodromy at
nearby parameters (bridge (c), planned); existence of solutions and the non-resonant normal form
(not restated: `b65f_segment_solution`, `b65f_local_normal_form`).
HC no distance; AV milestone no distance.
-/

noncomputable section
open Set Metric Filter Matrix Manifold
open scoped Topology ContDiff
namespace HodgeLean.Foundations.Program

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- **Fundamental solutions differ by a constant.** If `Y' = A Y` and `Z' = A Z` on a
preconnected open set `U`, with `Z` invertible on `U`, then `Y = Z K` on `U` for a constant `K`:
`(Z⁻¹ Y)' = −Z⁻¹ A Y + Z⁻¹ A Y = 0`.
Source: Coddington–Levinson, *Theory of Ordinary Differential Equations*, ch. 1, §2
(fundamental matrices of a linear system); Mathlib `IsOpen.is_const_of_deriv_eq_zero`. -/
theorem caf_eq_mul_const_of_ode [FiniteDimensional ℂ E] (U : Set ℂ) (hU : IsOpen U)
    (hc : IsPreconnected U) (A Y Z : ℂ → E →L[ℂ] E)
    (hY : ∀ z ∈ U, HasDerivAt Y (A z * Y z) z) (hZ : ∀ z ∈ U, HasDerivAt Z (A z * Z z) z)
    (hZu : ∀ z ∈ U, IsUnit (Z z)) :
    ∃ K : E →L[ℂ] E, ∀ z ∈ U, Y z = Z z * K :=
  caf_eq_mul_const_of_ode_aux U hU hc A Y Z hY hZ hZu

/-- **Holomorphic forms are determined off a finite set.** Two holomorphic `1`-forms on a
Riemann surface that agree at every tangent vector over the complement of a finite set are equal:
both are continuous on the tangent bundle, and tangent vectors over the complement are dense
(a surface charted on `ℂ` has no isolated points).
Source: Forster, *Lectures on Riemann Surfaces*, GTM 81, §9 (holomorphic `1`-forms, local
expression `f dz`); identity of continuous functions on a dense set. -/
theorem caf_holForm_ext (C : Type) [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] [T2Space C] (θ θ' : TangentBundle 𝓘(ℂ, ℂ) C → ℂ)
    (hθ : θ ∈ b3_HolForm ℂ C) (hθ' : θ' ∈ b3_HolForm ℂ C) (F : Set C) (hF : F.Finite)
    (h : ∀ u : TangentBundle 𝓘(ℂ, ℂ) C, u.1 ∉ F → θ u = θ' u) : θ = θ' :=
  caf_holForm_ext_aux C θ θ' hθ hθ' F hF h

/-- **Removable singularities for `1`-forms.** A function on the tangent bundle that is
holomorphic and fibrewise linear over the complement of a finite set `F`, and whose coefficient
`θ(∂/∂z)` in the chart at each point of `F` is bounded on a punctured neighbourhood, agrees over
the complement of `F` with a holomorphic `1`-form. Its values over `F` are not used.
Source: Forster, §9 (local expression of a `1`-form); Ahlfors, *Complex Analysis*, 3rd ed.,
ch. 4, §3.1 (Riemann's removable singularity theorem); Mathlib
`Complex.differentiableOn_update_limUnder_of_bddAbove`. -/
theorem caf_holForm_extend (C : Type) [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] [T2Space C] (θ : TangentBundle 𝓘(ℂ, ℂ) C → ℂ)
    (F : Set C) (hF : F.Finite)
    (hhol : ∀ u : TangentBundle 𝓘(ℂ, ℂ) C, u.1 ∉ F →
      ContMDiffAt 𝓘(ℂ, ℂ).tangent 𝓘(ℂ, ℂ) ω θ u)
    (hlin : ∀ x ∉ F, ∀ (a : ℂ) (v w : TangentSpace 𝓘(ℂ, ℂ) x),
      θ ⟨x, a • v + w⟩ = a * θ ⟨x, v⟩ + θ ⟨x, w⟩)
    (hbdd : ∀ x ∈ F, ∃ B : ℝ, ∀ᶠ z in 𝓝[≠] (extChartAt 𝓘(ℂ, ℂ) x x),
      ‖θ ⟨(extChartAt 𝓘(ℂ, ℂ) x).symm z,
        mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (extChartAt 𝓘(ℂ, ℂ) x).symm z (1 : ℂ)⟩‖ ≤ B) :
    ∃ θ' ∈ b3_HolForm ℂ C, ∀ u : TangentBundle 𝓘(ℂ, ℂ) C, u.1 ∉ F → θ' u = θ u :=
  caf_holForm_extend_aux C θ F hF hhol hlin hbdd

/-- **A punctured surface is path-connected.** A connected space charted on `ℂ`, minus a finite
set, is path-connected: it is locally path-connected, and removing finitely many points from a
connected surface leaves it connected (each point has a disc neighbourhood whose punctured disc
is connected).
Source: Forster, §1 (Riemann surfaces are path-connected); Mathlib
`isPathConnected_compl_singleton_of_one_lt_rank` (the planar case). -/
theorem caf_isPathConnected_compl_finite (M : Type) [TopologicalSpace M] [ChartedSpace ℂ M]
    [T2Space M] [ConnectedSpace M] (S : Set M) (hS : S.Finite) : IsPathConnected Sᶜ :=
  caf_isPathConnected_compl_finite_aux M S hS

/-- **Spectral data of the moving residues (bridge (a)).** For a 5c record `O` and a moving
pole `x`, there is `λ ∈ {1/3, 2/3}` such that at every parameter of the record's disc the residue
`A = b65q_res O.residue θ (Sum.inr x)` has trace `λ`, is conjugate to `diag(0, 0, 0, λ)`, and
`k − ad A` is bijective for every positive integer `k` (the premise `hnr` of
`b65f_local_normal_form` for `R = O.residue θ (Sum.inr x)`).
Source: `b65q_trace_zero_inr`, `b65q_trace_flow` (`λ = trace b65q_BQ (b65q_fibreIndex x)`) and
`b65q_rank_one_flow` (`A² = λ A`: `A/λ` is an idempotent of trace one); G32 v0.16, §5.3
(exponents `0, 0, 0, λ` at the moving poles); the eigenvalues of `ad A` are `0, ±λ`. -/
theorem caf_moving_spectrum {p : Fin 12 → ℂ} (O : b65p_Outputs p) (x : Fin 12) :
    ∃ q : ℚ, (q = 1 / 3 ∨ q = 2 / 3) ∧ ∀ θ ∈ ball (0 : ℂ) O.radius,
      Matrix.trace (b65q_res O.residue θ (Sum.inr x)) = (q : ℂ) ∧
      (∃ P : Matrix (Fin 4) (Fin 4) ℂ, IsUnit P ∧
        b65q_res O.residue θ (Sum.inr x) * P = P * diagonal ![0, 0, 0, (q : ℂ)]) ∧
      ∀ k : ℕ, 0 < k → Function.Bijective
        (fun T : (Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ) ↦
          (k : ℂ) • T - (O.residue θ (Sum.inr x) * T - T * O.residue θ (Sum.inr x))) :=
  caf_moving_spectrum_aux O x

/-- **The determinant equation.** If `Y` is meromorphic at `z₀`, invertible on a punctured
neighbourhood and solves `Y' = (z − z₀)⁻¹ (A₀ + (z − z₀) G) Y` there, with `G` continuous at
`z₀`, then `det Y` has integer order `n` at `z₀` and `n = trace A₀`: by Liouville's formula
`(z − z₀)(det Y)' = (trace A₀ + (z − z₀) trace G) det Y`, and the scalar indicial equation
(`caf_order_eigenvalue`).
Source: Coddington–Levinson, ch. 1, §2 (Liouville's formula `(det Y)' = trace A · det Y`) and
ch. 4 (indicial equation); `caf_order_eigenvalue`. -/
theorem caf_det_order [FiniteDimensional ℂ E] (Y : ℂ → E →L[ℂ] E) (z₀ : ℂ)
    (A₀ : E →L[ℂ] E) (G : ℂ → E →L[ℂ] E) (hY : MeromorphicAt Y z₀) (hG : ContinuousAt G z₀)
    (hunit : ∀ᶠ z in 𝓝[≠] z₀, IsUnit (Y z))
    (hode : ∀ᶠ z in 𝓝[≠] z₀,
      HasDerivAt Y (((z - z₀)⁻¹ • (A₀ + (z - z₀) • G z)) * Y z) z) :
    ∃ n : ℤ, meromorphicOrderAt (fun z ↦ (Y z).det) z₀ = (n : WithTop ℤ) ∧
      (n : ℂ) = LinearMap.trace ℂ E (A₀ : E →ₗ[ℂ] E) :=
  caf_det_order_aux Y z₀ A₀ G hY hG hunit hode

/-- **Character and order.** A meromorphic germ `v` at `0` of finite order `m` with
`v(ζ y) = α v(y)` on a punctured neighbourhood (`ζ ≠ 0`) has `α = ζ^m`: writing
`v = y^m g` with `g(0) ≠ 0`, the leading coefficients give `ζ^m g(0) = α g(0)`.
Source: Forster, §2, Theorem 2.1 (local form under the rotation `y ↦ ζ y`); Mathlib
`meromorphicOrderAt_eq_int_iff`. -/
theorem caf_rotation_order (v : ℂ → E) (m : ℤ) (ζ α : ℂ) (hζ : ζ ≠ 0)
    (hv : MeromorphicAt v 0) (hm : meromorphicOrderAt v 0 = (m : WithTop ℤ))
    (hrot : ∀ᶠ y in 𝓝[≠] (0 : ℂ), v (ζ * y) = α • v y) :
    α = ζ ^ m :=
  caf_rotation_order_aux v m ζ α hζ hv hm hrot

/-- **The determinant unit (bridge (b)).** If `Y = H D` on a punctured neighbourhood of `z₀`,
with `H` analytic at `z₀` and `det D = (z − z₀)ⁿ`, and `det Y` has order exactly `n` at `z₀`,
then `H z₀` is invertible: the order of `det H` at `z₀` is `0`. The value `Y z₀` is not a premise;
the conclusion concerns the extension `H`.
Source: Ahlfors, ch. 4, §3.2 (orders of zeros and poles are additive); amendment of
`docs/specs/CoverAnalytic.md` (moving poles, item 3). -/
theorem caf_isUnit_extension [FiniteDimensional ℂ E] (Y H D : ℂ → E →L[ℂ] E) (z₀ : ℂ)
    (n : ℤ) (hH : AnalyticAt ℂ H z₀)
    (hYHD : ∀ᶠ z in 𝓝[≠] z₀, Y z = H z * D z)
    (hD : ∀ᶠ z in 𝓝[≠] z₀, (D z).det = (z - z₀) ^ n)
    (hdet : meromorphicOrderAt (fun z ↦ (Y z).det) z₀ = (n : WithTop ℤ)) :
    IsUnit (H z₀) :=
  caf_isUnit_extension_aux Y H D z₀ n hH hYHD hD hdet

/-! ## Independent premise checks

Examples for statements 1–4 and 6–8 check their premises together on concrete instances.
Statement 5 has an initial-matrix calculation only; full record satisfiability is not checked.
No example uses a statement of this file or its auxiliary. -/

/-- Statement 1: `Z = eᶻ`, `Y = 2eᶻ` solve `Y' = Y` on `ℂ`, and `Z` is invertible. -/
example : IsOpen (univ : Set ℂ) ∧ IsPreconnected (univ : Set ℂ) ∧
    (∀ z ∈ (univ : Set ℂ), HasDerivAt (fun z : ℂ ↦ (2 * Complex.exp z) • (1 : ℂ →L[ℂ] ℂ))
      ((1 : ℂ →L[ℂ] ℂ) * ((2 * Complex.exp z) • (1 : ℂ →L[ℂ] ℂ))) z) ∧
    (∀ z ∈ (univ : Set ℂ), HasDerivAt (fun z : ℂ ↦ Complex.exp z • (1 : ℂ →L[ℂ] ℂ))
      ((1 : ℂ →L[ℂ] ℂ) * (Complex.exp z • (1 : ℂ →L[ℂ] ℂ))) z) ∧
    (∀ z ∈ (univ : Set ℂ), IsUnit (Complex.exp z • (1 : ℂ →L[ℂ] ℂ))) := by
  refine ⟨isOpen_univ, isPreconnected_univ, fun z _ ↦ ?_, fun z _ ↦ ?_, fun z _ ↦ ?_⟩
  · rw [one_mul]
    exact ((Complex.hasDerivAt_exp z).const_mul (2 : ℂ)).smul_const (1 : ℂ →L[ℂ] ℂ)
  · rw [one_mul]; exact (Complex.hasDerivAt_exp z).smul_const (1 : ℂ →L[ℂ] ℂ)
  · rw [← Algebra.algebraMap_eq_smul_one]
    exact (Complex.exp_ne_zero z).isUnit.map _

/-- Statement 2: the zero form on `ℂ` with the finite set `{0}`. -/
example : (0 : TangentBundle 𝓘(ℂ, ℂ) ℂ → ℂ) ∈ b3_HolForm ℂ ℂ ∧
    (0 : TangentBundle 𝓘(ℂ, ℂ) ℂ → ℂ) ∈ b3_HolForm ℂ ℂ ∧ ({0} : Set ℂ).Finite ∧
    (∀ u : TangentBundle 𝓘(ℂ, ℂ) ℂ, u.1 ∉ ({0} : Set ℂ) →
      (0 : TangentBundle 𝓘(ℂ, ℂ) ℂ → ℂ) u = 0) :=
  ⟨(b3_HolForm ℂ ℂ).zero_mem, (b3_HolForm ℂ ℂ).zero_mem,
    finite_singleton 0, fun _ _ ↦ rfl⟩

/-- Statement 3: the zero function on the tangent bundle of `ℂ` with `F = {0}`. -/
example : ({0} : Set ℂ).Finite ∧
    (∀ u : TangentBundle 𝓘(ℂ, ℂ) ℂ, u.1 ∉ ({0} : Set ℂ) →
      ContMDiffAt 𝓘(ℂ, ℂ).tangent 𝓘(ℂ, ℂ) ω (0 : TangentBundle 𝓘(ℂ, ℂ) ℂ → ℂ) u) ∧
    (∀ x ∉ ({0} : Set ℂ), ∀ (a : ℂ) (v w : TangentSpace 𝓘(ℂ, ℂ) x),
      (0 : TangentBundle 𝓘(ℂ, ℂ) ℂ → ℂ) ⟨x, a • v + w⟩ =
        a * (0 : TangentBundle 𝓘(ℂ, ℂ) ℂ → ℂ) ⟨x, v⟩ +
          (0 : TangentBundle 𝓘(ℂ, ℂ) ℂ → ℂ) ⟨x, w⟩) ∧
    (∀ x ∈ ({0} : Set ℂ), ∃ B : ℝ, ∀ᶠ z in 𝓝[≠] (extChartAt 𝓘(ℂ, ℂ) x x),
      ‖(0 : TangentBundle 𝓘(ℂ, ℂ) ℂ → ℂ) ⟨(extChartAt 𝓘(ℂ, ℂ) x).symm z,
        mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (extChartAt 𝓘(ℂ, ℂ) x).symm z (1 : ℂ)⟩‖ ≤ B) :=
  ⟨finite_singleton 0, fun _ _ ↦ contMDiffAt_const, fun _ _ _ _ _ ↦ by simp,
    fun _ _ ↦ ⟨0, Eventually.of_forall fun _ ↦ by simp⟩⟩

/-- Statement 4: the planar case `ℂ \ {0}`, premise and conclusion, from Mathlib. -/
example : ({0} : Set ℂ).Finite ∧ IsPathConnected ({0} : Set ℂ)ᶜ :=
  ⟨finite_singleton 0, isPathConnected_compl_singleton_of_one_lt_rank (by simp) 0⟩

/-- Statement 5: initial-matrix calculation of the two rational traces only.
Full record satisfiability is not checked. -/
example : Matrix.trace (b65q_BQ 0) = 1 / 3 ∧ Matrix.trace (b65q_BQ 1) = 2 / 3 := by
  constructor <;> decide +kernel

/-- Statement 6: `Y = z` on `ℂ` solves `z Y' = A₀ Y` with `A₀ = 1`, `G = 0`; it is meromorphic
and invertible off `0`. Its determinant has order `1 = trace A₀`. -/
example : MeromorphicAt (fun z : ℂ ↦ z • (1 : ℂ →L[ℂ] ℂ)) 0 ∧
    ContinuousAt (fun _ : ℂ ↦ (0 : ℂ →L[ℂ] ℂ)) 0 ∧
    (∀ᶠ z in 𝓝[≠] (0 : ℂ), IsUnit (z • (1 : ℂ →L[ℂ] ℂ))) ∧
    (∀ᶠ z in 𝓝[≠] (0 : ℂ), HasDerivAt (fun z : ℂ ↦ z • (1 : ℂ →L[ℂ] ℂ))
      (((z - 0)⁻¹ • ((1 : ℂ →L[ℂ] ℂ) + (z - 0) • (0 : ℂ →L[ℂ] ℂ))) *
        (z • (1 : ℂ →L[ℂ] ℂ))) z) := by
  refine ⟨(analyticAt_id.smul analyticAt_const).meromorphicAt, continuousAt_const, ?_, ?_⟩
  · filter_upwards [self_mem_nhdsWithin] with z hz
    rw [← Algebra.algebraMap_eq_smul_one]
    exact (show z ≠ 0 from hz).isUnit.map _
  · filter_upwards [self_mem_nhdsWithin] with z hz
    have hz' : z ≠ 0 := hz
    have h : ((z - 0)⁻¹ • ((1 : ℂ →L[ℂ] ℂ) + (z - 0) • (0 : ℂ →L[ℂ] ℂ))) *
        (z • (1 : ℂ →L[ℂ] ℂ)) = (1 : ℂ) • (1 : ℂ →L[ℂ] ℂ) := by
      simp [hz']
    rw [h]
    exact (hasDerivAt_id' z).smul_const (1 : ℂ →L[ℂ] ℂ)

/-- Statement 7: `v = y³` of order `3`, `ζ = α = −1`; and `−1 = (−1)³`. -/
example : MeromorphicAt (fun y : ℂ ↦ y ^ 3) 0 ∧
    meromorphicOrderAt (fun y : ℂ ↦ y ^ 3) 0 = ((3 : ℤ) : WithTop ℤ) ∧ (-1 : ℂ) ≠ 0 ∧
    (∀ᶠ y in 𝓝[≠] (0 : ℂ), (-1 * y) ^ 3 = (-1 : ℂ) • y ^ 3) ∧
    (-1 : ℂ) = (-1) ^ (3 : ℤ) := by
  refine ⟨(analyticAt_id.pow 3).meromorphicAt, ?_, by norm_num,
    Eventually.of_forall fun y ↦ by simp only [smul_eq_mul]; ring, by norm_num⟩
  simpa using! (meromorphicOrderAt_pow_id_sub_const (𝕜 := ℂ) (n := 3) (x := 0))

/-- Statement 8: `Y = D = z`, `H = 1`, `n = 1` at `z₀ = 0`. -/
example : AnalyticAt ℂ (fun _ : ℂ ↦ (1 : ℂ →L[ℂ] ℂ)) 0 ∧
    (∀ᶠ z in 𝓝[≠] (0 : ℂ), z • (1 : ℂ →L[ℂ] ℂ) = (1 : ℂ →L[ℂ] ℂ) * (z • (1 : ℂ →L[ℂ] ℂ))) ∧
    (∀ᶠ z in 𝓝[≠] (0 : ℂ), (z • (1 : ℂ →L[ℂ] ℂ)).det = (z - 0) ^ (1 : ℤ)) ∧
    meromorphicOrderAt (fun z : ℂ ↦ (z • (1 : ℂ →L[ℂ] ℂ)).det) 0 = ((1 : ℤ) : WithTop ℤ) := by
  have hd : ∀ z : ℂ, (z • (1 : ℂ →L[ℂ] ℂ)).det = z := fun z ↦ by
    simp [ContinuousLinearMap.det]
  refine ⟨analyticAt_const, Eventually.of_forall fun z ↦ by rw [one_mul],
    Eventually.of_forall fun z ↦ by rw [hd, sub_zero, zpow_one], ?_⟩
  simp only [hd]
  simpa using! (meromorphicOrderAt_pow_id_sub_const (𝕜 := ℂ) (n := 1) (x := 0))

/-- Statement 8 does not extend to the assigned value: `Y` equal to `1` except `Y 0 = 0`
satisfies the premises with `H = D = 1` and `n = 0`, while `Y 0` is not invertible. -/
example : AnalyticAt ℂ (fun _ : ℂ ↦ (1 : ℂ →L[ℂ] ℂ)) 0 ∧
    (∀ᶠ z in 𝓝[≠] (0 : ℂ), Function.update (fun _ : ℂ ↦ (1 : ℂ →L[ℂ] ℂ)) 0 0 z =
      (1 : ℂ →L[ℂ] ℂ) * (1 : ℂ →L[ℂ] ℂ)) ∧
    (∀ᶠ z in 𝓝[≠] (0 : ℂ), (1 : ℂ →L[ℂ] ℂ).det = (z - 0) ^ (0 : ℤ)) ∧
    meromorphicOrderAt (fun z ↦ (Function.update (fun _ : ℂ ↦ (1 : ℂ →L[ℂ] ℂ)) 0 0 z).det) 0 =
      ((0 : ℤ) : WithTop ℤ) ∧
    ¬ IsUnit (Function.update (fun _ : ℂ ↦ (1 : ℂ →L[ℂ] ℂ)) 0 0 0) := by
  have hev : ∀ᶠ z in 𝓝[≠] (0 : ℂ),
      Function.update (fun _ : ℂ ↦ (1 : ℂ →L[ℂ] ℂ)) 0 0 z = 1 := by
    filter_upwards [self_mem_nhdsWithin] with z hz
    exact Function.update_of_ne hz _ _
  refine ⟨analyticAt_const, hev.mono fun z hz ↦ by rw [hz, one_mul], Eventually.of_forall fun z ↦ by simp, ?_,
    by simp⟩
  rw [meromorphicOrderAt_congr (hev.mono fun z hz ↦ by rw [hz])]
  have h := meromorphicOrderAt_pow_id_sub_const (𝕜 := ℂ) (n := 0) (x := 0)
  simp only [pow_zero] at h
  simp only [ContinuousLinearMap.det, ContinuousLinearMap.toLinearMap_one, map_one]
  exact h

end HodgeLean.Foundations.Program
