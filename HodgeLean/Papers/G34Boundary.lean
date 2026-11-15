import HodgeLean.Papers.G34BoundaryProofs

/-! # G34 Theorem A, the boundary certificate: dominance and split discriminant (FROZEN SPEC)

G34 v1.5, Section 8 and Appendix A, show that the Hurwitz component of the tuple of twenty
reflections of `G₃₄` is dominant onto `M(4, ℚ(√-3), [1])` and that its discriminant is split.
Through the generic Weil transfer (`spec/wtr`, the instance `(n, δ) = (4, [1])`), these are the
fields `dominant` and `fiber_disc` of `WeilTransferDatum 4 1`. This spec separates the finite
matrix certificate, the Lean steps of the boundary argument, and the geometric premises.

Claimed, about the printed matrices of Appendix A (`g34b_S`, `g34b_X`, `g34b_N`):
* `S` is skew-Hermitian with `det S = 81`; the logarithms `N_j` satisfy (H1)–(H4) with `n = 4`:
  `N_j N_k = 0`; `I = Σ_j im N_j` is the span of `b₁, …, b₄`, of dimension `4`, totally isotropic
  and killed by every `N_j`; the forms `β_j` are Hermitian, negative semidefinite, with negative
  definite sum on `V_par / I`; the `N_j` span a `ℚ`-space of dimension `16`.

Claimed, as Lean steps from (H1)–(H4), for any family of matrices:
* (H2) gives (H1); (H2) and (H3) give `ker M = im M = I` for every positive combination `M` of
  the `N_j` (Lemma 8.3, the linear algebra); complexification along `ι : K → ℂ` commutes with
  ranges and keeps dimensions; (H2)–(H4) with a nondegenerate skew-Hermitian `S` give
  `span_ℂ {N_j} = Hom(V_ℂ / I_ℂ, I_ℂ)`; with `F₀ ∩ I_ℂ = 0` and `dim F₀ = n` the tangent map
  `v ↦ Σ_j v_j M_j · F₀` is onto (Lemma 8.4);
* rank is lower semicontinuous; an analytic map whose derivative has full rank `d` at a point of
  an open set has image containing a neighbourhood of the value (inverse function theorem);
* a Hermitian matrix with vanishing upper-left `n × n` block (a totally isotropic `n`-space) has
  determinant `(-1)ⁿ |det A|²`; for `n = 4` and a nonzero rational scale the class is `[1]`.

Claimed, as implications from the named premises `g34b_ParabolicPolarization` (Proposition 7.1)
and `g34b_BoundaryPeriodMap` (Lemmas 8.1, 8.2, the nilpotent orbit theorem, Cattani–Kaplan–Schmid
(4.5)): every fibre has discriminant `[1]` (`g34b_fiber_disc`); the period map has rank `16` at
some point (`g34b_period_rank`); the field `dominant` (`g34b_dominant`); and, with the remaining
stage fields of the generic transfer, `G34TheoremAStatement A` (`g34b_theoremA_of_boundary`).

Not claimed: any premise. The identification of the geometric monodromy logarithms with the
printed `N_j` (Gauss–Manin, Lemma 8.1), the admissible-cover local monodromy after base change
(Lemma 8.2), the nilpotent orbit normal form and its differentiation, and the Hodge–Tate input
`F¹₀ ∩ W₀ = 0` are premises that Lean does not check. That the printed matrices are the output of
the cocycle computation (the derivation level of Appendix A) is not checked either. No family,
period map or Theorem A is asserted.

HC no distance; AV milestone no distance.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace Set Filter
open Matrix
open scoped Topology Matrix
open HodgeLean.RealDefs HodgeLean.Foundations HodgeLean.Foundations.WeilPower
open HodgeLean.Foundations.Symplectic HodgeLean.Foundations.HermitianForm HodgeLean.Adapters

namespace HodgeLean.Papers

local notation "𝕂" => QuadraticAlgebra ℚ (-3) 0

section Certificate

/-- **`S` is skew-Hermitian**: `Sᴴ = -S`, so `𝒮` is skew-Hermitian and `h = ϑ𝒮` Hermitian.
Source: G34 v1.5, Lemma 7.2 (`𝒮` is skew-Hermitian) and Appendix A (the matrix `S`). -/
theorem g34b_S_skew : g34b_Sᴴ = -g34b_S :=
  g34b_S_skew_aux

example (i j : Fin 4 ⊕ Fin 4) : star (g34b_S i j) = -g34b_S j i := by
  simpa using congrFun (congrFun g34b_S_skew j) i

/-- **`det S = 81`**: the cup product is nondegenerate.
Source: G34 v1.5, Appendix A (the matrix `S`, with off-diagonal blocks `diag(3, 1, 1, 3)` and
`D = diag(-3, -1, -1, -3)`). -/
theorem g34b_S_det : g34b_S.det = 81 :=
  g34b_S_det_aux

example : g34b_S.det ≠ 0 := by
  rw [g34b_S_det]; norm_num

/-- **(H1) for the printed logarithms**: `N_j N_k = 0`, from the block form `(0 X_j; 0 0)`.
Source: G34 v1.5, Appendix A ("(H1) is the block form itself"). -/
theorem g34b_h1 : g34b_H1 g34b_N :=
  g34b_h1_aux

example : g34b_N 0 * g34b_N 16 = 0 := g34b_h1 0 16

/-- **`I = ⟨b₁, …, b₄⟩`**: the images of the printed `N_j` span exactly the first four
coordinates (already `X₁` is invertible).
Source: G34 v1.5, Appendix A ("Then `I = ⟨b₁, …, b₄⟩`"). -/
theorem g34b_I_eq :
    g34b_I g34b_N = Submodule.span 𝕂
      (Set.range fun i : Fin 4 => (Pi.single (Sum.inl i) 1 : Fin 4 ⊕ Fin 4 → 𝕂)) :=
  g34b_I_eq_aux

example : (Pi.single (Sum.inl 0) 1 : Fin 4 ⊕ Fin 4 → 𝕂) ∈ g34b_I g34b_N := by
  rw [g34b_I_eq]
  exact Submodule.subset_span ⟨0, rfl⟩

/-- **(H2) for the printed data**: `I` has dimension `4`, is totally isotropic for `𝒮` (the
upper-left block of `S` vanishes) and is killed by every `N_j`.
Source: G34 v1.5, Proof of Theorem A in Section 9 and Appendix A ("(H2) holds because the upper
left `4 × 4` block of `S` vanishes"). -/
theorem g34b_h2 : g34b_H2 g34b_S g34b_N 4 :=
  g34b_h2_aux

example : Module.finrank 𝕂 (g34b_I g34b_N) = 4 := g34b_h2.finrank_eq

/-- **(H3) for the printed data**: every `β_j` is Hermitian and negative semidefinite (matrix
`D X_j` on `V_par / I`), and `Σ_j β_j` is negative definite on `V_par / I`; the common sign is
`σ = -1`.
Source: G34 v1.5, Proof of Theorem A in Section 9 ("every `β_j` is negative semidefinite and
`Σ_j β_j` is negative definite"); Appendix A (the table of signatures, and "On `V_par / I` the
form `β_j` has matrix `D X_j`"). -/
theorem g34b_h3 : g34b_H3 g34b_S g34b_N :=
  g34b_h3_aux

example (x : Fin 4 ⊕ Fin 4 → 𝕂) :
    g34b_beta g34b_S (g34b_N 0) x x = star (g34b_beta g34b_S (g34b_N 0) x x) :=
  g34b_h3.herm 0 x x

/-- **(H4) for the printed data, the rank-16 span**: the seventeen `N_j` span a `ℚ`-space of
dimension `16 = 4²` (in the `32`-dimensional `ℚ`-space of `4 × 4` blocks over `K`).
Source: G34 v1.5, Proof of Theorem A in Section 9 ("the `N_j` span a `ℚ`-space of dimension
`16 = n²`") and Appendix A. -/
theorem g34b_h4 : g34b_H4 g34b_N 4 :=
  g34b_h4_aux

example : Module.finrank ℚ (Submodule.span ℚ (Set.range g34b_N)) = 16 := g34b_h4

end Certificate

section Generic

variable {m : Type*} [Fintype m] [DecidableEq m] {r n : ℕ}

/-- **(H2) implies (H1).** Each image `im N_k` lies in `I`, which every `N_j` kills. So (H1) is
not an independent condition once (H2) is stated with `I = Σ_j im N_j`.
Source: G34 v1.5, Section 8, conditions (H1) and (H2). -/
theorem g34b_h1_of_h2 (S : Matrix m m 𝕂) (N : Fin r → Matrix m m 𝕂)
    (h2 : g34b_H2 S N n) : g34b_H1 N :=
  g34b_h1_of_h2_aux S N h2

example : g34b_H1 g34b_N := g34b_h1_of_h2 g34b_S g34b_N g34b_h2

/-- **The kernel of a cone element is `I`.** For positive rationals `a_j`, the kernel of
`M = Σ_j a_j N_j` is `I`: `M` kills `I` by (H2), and for `x ∉ I`, `σ 𝒮(x, M x) =
Σ_j a_j σ β_j(x, x) > 0` by (H3).
Source: G34 v1.5, proof of Lemma 8.3 ("by (H3), for `x ∉ I` we have `𝒮(x, εMx) ≠ 0`"). -/
theorem g34b_cone_ker (S : Matrix m m 𝕂) (N : Fin r → Matrix m m 𝕂)
    (h2 : g34b_H2 S N n) (h3 : g34b_H3 S N) (a : Fin r → ℚ) (ha : ∀ j, 0 < a j) :
    LinearMap.ker (Matrix.toLin' (∑ j, (a j : 𝕂) • N j)) = g34b_I N :=
  g34b_cone_ker_aux S N h2 h3 a ha

example : LinearMap.ker (Matrix.toLin' (∑ j, ((1 : ℚ) : 𝕂) • g34b_N j)) = g34b_I g34b_N :=
  g34b_cone_ker g34b_S g34b_N g34b_h2 g34b_h3 (fun _ => 1) fun _ => one_pos

/-- **The image of a cone element is `I`.** With `dim V = 2n`, `M` induces an injection
`V / I → I` between spaces of dimension `n`, so `im M = I`; with `g34b_cone_ker`, `im M = ker M =
I`, the weight filtration `W₀ = W₁ = I ⊂ W₂ = V` of Lemma 8.3.
Source: G34 v1.5, Lemma 8.3 and its proof ("`M : V_par / I → I` is injective, hence bijective").
-/
theorem g34b_cone_range (S : Matrix m m 𝕂) (N : Fin r → Matrix m m 𝕂)
    (h2 : g34b_H2 S N n) (h3 : g34b_H3 S N) (hm : Fintype.card m = 2 * n)
    (a : Fin r → ℚ) (ha : ∀ j, 0 < a j) :
    LinearMap.range (Matrix.toLin' (∑ j, (a j : 𝕂) • N j)) = g34b_I N :=
  g34b_cone_range_aux S N h2 h3 hm a ha

example (a : Fin 17 → ℚ) (ha : ∀ j, 0 < a j) :
    LinearMap.range (Matrix.toLin' (∑ j, (a j : 𝕂) • g34b_N j)) = g34b_I g34b_N :=
  g34b_cone_range g34b_S g34b_N g34b_h2 g34b_h3 (by simp) a ha

/-- **Ranges commute with complexification**: the range of `A` mapped along `ι` is the
complexification of the range of `A`.
Source: scalar extension of linear maps along `K ⊂ ℂ`, as in G34 v1.5, Section 8 ("write
`V_{par,ℂ}`, `I_ℂ` for the scalar extensions"). -/
theorem g34b_range_map (ι : 𝕂 →+* ℂ) (A : Matrix m m 𝕂) :
    LinearMap.range (Matrix.toLin' (A.map ι)) =
      g34b_complexify ι (LinearMap.range (Matrix.toLin' A)) :=
  g34b_range_map_aux ι A

example (ι : 𝕂 →+* ℂ) :
    LinearMap.range (Matrix.toLin' ((0 : Matrix m m 𝕂).map ι)) =
      g34b_complexify ι (LinearMap.range (Matrix.toLin' (0 : Matrix m m 𝕂))) :=
  g34b_range_map ι 0

/-- **Complexification keeps dimension**: `dim_ℂ U_ℂ = dim_K U`.
Source: scalar extension along a field embedding; Bourbaki, *Algebra*, Ch. II, §5 (base change of
vector spaces). -/
theorem g34b_finrank_complexify (ι : 𝕂 →+* ℂ) (U : Submodule 𝕂 (m → 𝕂)) :
    Module.finrank ℂ (g34b_complexify ι U) = Module.finrank 𝕂 U :=
  g34b_finrank_complexify_aux ι U

example (ι : 𝕂 →+* ℂ) : Module.finrank ℂ (g34b_complexify ι (g34b_I g34b_N)) = 4 := by
  rw [g34b_finrank_complexify, g34b_h2.finrank_eq]

/-- **The logarithms span `Hom(V_ℂ / I_ℂ, I_ℂ)`.** For a nondegenerate skew-Hermitian `S` on
`K^{2n}` and logarithms with (H2)–(H4), the `ℂ`-span of the `N_j` (mapped along `ι`) is the space
of `X` with `X(ℂ^{2n}) ⊆ I_ℂ` and `X(I_ℂ) = 0`. The rational Lie algebra `𝔫_I` (`X(V) ⊆ I`,
`X(I) = 0`, `S X` Hermitian) is the `ℚ`-space of Hermitian forms on `V / I`, of dimension `n²`;
(H3) puts each `N_j` in it and (H4) makes them span it; its complexification is
`Hom(V_ℂ / I_ℂ, I_ℂ)`.
Source: G34 v1.5, proof of Lemma 8.4 (first four sentences). -/
theorem g34b_span_eq_boundaryAlg (ι : 𝕂 →+* ℂ) (S : Matrix m m 𝕂)
    (N : Fin r → Matrix m m 𝕂) (hS : Sᴴ = -S) (hdet : S.det ≠ 0) (h2 : g34b_H2 S N n)
    (h3 : g34b_H3 S N) (h4 : g34b_H4 N n) (hm : Fintype.card m = 2 * n) :
    Submodule.span ℂ (Set.range fun j => (N j).map ι) =
      g34b_boundaryAlg (g34b_complexify ι (g34b_I N)) :=
  g34b_span_eq_boundaryAlg_aux ι S N hS hdet h2 h3 h4 hm

example (ι : 𝕂 →+* ℂ) (j : Fin 17) :
    (g34b_N j).map ι ∈ g34b_boundaryAlg (g34b_complexify ι (g34b_I g34b_N)) := by
  rw [← g34b_span_eq_boundaryAlg ι g34b_S g34b_N g34b_S_skew (by rw [g34b_S_det]; norm_num)
    g34b_h2 g34b_h3 g34b_h4 (by simp)]
  exact Submodule.subset_span ⟨j, rfl⟩

/-- **Every tangent vector at `F₀` comes from the boundary algebra.** If `F₀` and `J` are
`n`-dimensional subspaces of `ℂ^{2n}` meeting trivially, every `φ ∈ Hom(F₀, ℂ^{2n} / F₀)` is the
class `[X |_{F₀}]` of some `X` with `X(ℂ^{2n}) ⊆ J` and `X(J) = 0`: `ℂ^{2n} = J ⊕ F₀`, and
`J → ℂ^{2n} / F₀` is an isomorphism.
Source: G34 v1.5, proof of Lemma 8.4 (last three sentences, with `J = I_ℂ`). -/
theorem g34b_boundaryAlg_surj (J F₀ : Submodule ℂ (m → ℂ))
    (hJ : Module.finrank ℂ J = n) (hF : Module.finrank ℂ F₀ = n)
    (hm : Fintype.card m = 2 * n) (hJF : F₀ ⊓ J = ⊥)
    (φ : F₀ →ₗ[ℂ] (m → ℂ) ⧸ F₀) :
    ∃ X ∈ g34b_boundaryAlg J, F₀.mkQ ∘ₗ Matrix.toLin' X ∘ₗ F₀.subtype = φ :=
  g34b_boundaryAlg_surj_aux J F₀ hJ hF hm hJF φ

example (J F₀ : Submodule ℂ (m → ℂ)) (hJ : Module.finrank ℂ J = n)
    (hF : Module.finrank ℂ F₀ = n) (hm : Fintype.card m = 2 * n) (hJF : F₀ ⊓ J = ⊥) :
    ∃ X ∈ g34b_boundaryAlg J, F₀.mkQ ∘ₗ Matrix.toLin' X ∘ₗ F₀.subtype = 0 :=
  g34b_boundaryAlg_surj J F₀ hJ hF hm hJF 0

/-- **The logarithms span the tangent space (Lemma 8.4).** Under (H2)–(H4) for a nondegenerate
skew-Hermitian `S` on `K^{2n}`, for nonzero scalars `c_j` and an `n`-dimensional `F₀ ⊆ ℂ^{2n}`
meeting `I_ℂ` trivially, the tangent map `v ↦ [Σ_j v_j c_j N_j |_{F₀}]` onto `Hom(F₀, ℂ^{2n} / F₀)`
is surjective, so its image has dimension `n²`.
Source: G34 v1.5, Lemma 8.4. -/
theorem g34b_tangent_surjective (ι : 𝕂 →+* ℂ) (S : Matrix m m 𝕂)
    (N : Fin r → Matrix m m 𝕂) (hS : Sᴴ = -S) (hdet : S.det ≠ 0) (h2 : g34b_H2 S N n)
    (h3 : g34b_H3 S N) (h4 : g34b_H4 N n) (hm : Fintype.card m = 2 * n)
    (c : Fin r → ℂ) (hc : ∀ j, c j ≠ 0) (F₀ : Submodule ℂ (m → ℂ))
    (hF : Module.finrank ℂ F₀ = n) (hHT : F₀ ⊓ g34b_complexify ι (g34b_I N) = ⊥) :
    Function.Surjective (g34b_tangentMap (fun j => c j • (N j).map ι) F₀) :=
  g34b_tangent_surjective_aux ι S N hS hdet h2 h3 h4 hm c hc F₀ hF hHT

example (ι : 𝕂 →+* ℂ) (F₀ : Submodule ℂ (Fin 4 ⊕ Fin 4 → ℂ)) (hF : Module.finrank ℂ F₀ = 4)
    (hHT : F₀ ⊓ g34b_complexify ι (g34b_I g34b_N) = ⊥) :
    Function.Surjective (g34b_tangentMap (fun j => (1 : ℂ) • (g34b_N j).map ι) F₀) :=
  g34b_tangent_surjective ι g34b_S g34b_N g34b_S_skew (by rw [g34b_S_det]; norm_num) g34b_h2
    g34b_h3 g34b_h4 (by simp) (fun _ => 1) (fun _ => one_ne_zero) F₀ hF hHT

/-- **Rank is lower semicontinuous**: if `A_k → A₀`, then eventually `rk A_k ≥ rk A₀` (a nonzero
minor of `A₀` stays nonzero nearby).
Source: G34 v1.5, proof of Proposition 8.5 ("the corresponding `n² × n²` minor of the limit is
nonzero and stays nonzero for small `u`"). -/
theorem g34b_rank_eventually {p q : ℕ} (A : ℕ → Matrix (Fin p) (Fin q) ℂ)
    (A₀ : Matrix (Fin p) (Fin q) ℂ) (h : Tendsto A atTop (𝓝 A₀)) :
    ∀ᶠ k in atTop, A₀.rank ≤ (A k).rank :=
  g34b_rank_eventually_aux A A₀ h

example (A₀ : Matrix (Fin 2) (Fin 3) ℂ) : ∀ᶠ _k in (atTop : Filter ℕ), A₀.rank ≤ A₀.rank :=
  g34b_rank_eventually (fun _ => A₀) A₀ tendsto_const_nhds

/-- **The open-image step**: an analytic map `f` on an open `V` with values in `ℂᵈ`, whose
derivative at `x ∈ V` has rank `d`, has image `f '' V` containing an open neighbourhood of `f x`.
The generalization of `g32r_open_image_analytic` from `ℂ⁹` to `ℂᵈ`.
Source: G34 v1.5, Theorem 6.2 (proof: "a submersion at `C₁`; shrinking `D`, `Φ(D)` contains a
ball"); Mathlib's `AnalyticAt.hasStrictFDerivAt` and `HasStrictFDerivAt.map_nhds_eq_of_surj`. -/
theorem g34b_open_image {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E] {d : ℕ} (f : E → Fin d → ℂ) (V : Set E) (hV : IsOpen V)
    (hf : AnalyticOnNhd ℂ f V) (x : E) (hx : x ∈ V)
    (hrank : Module.finrank ℂ (LinearMap.range (fderiv ℂ f x : E →ₗ[ℂ] Fin d → ℂ)) = d) :
    ∃ U : Set (Fin d → ℂ), IsOpen U ∧ f x ∈ U ∧ U ⊆ f '' V :=
  g34b_open_image_aux f V hV hf x hx hrank

example {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    (f : E → Fin (4 ^ 2) → ℂ) (V : Set E) (hV : IsOpen V) (hf : AnalyticOnNhd ℂ f V) (x : E)
    (hx : x ∈ V) (hrank : Module.finrank ℂ
      (LinearMap.range (fderiv ℂ f x : E →ₗ[ℂ] Fin (4 ^ 2) → ℂ)) = 4 ^ 2) :
    f '' V ∈ 𝓝 (f x) :=
  let ⟨_, hU, hxU, hUV⟩ := g34b_open_image f V hV hf x hx hrank
  Filter.mem_of_superset (hU.mem_nhds hxU) hUV

/-- **A totally isotropic coordinate subspace is a zero block**: if the span of the first `n`
coordinate vectors is totally isotropic for `G`, the upper-left block of `G` vanishes.
Source: G34 v1.5, Appendix A ("(H2) holds because the upper left `4 × 4` block of `S`
vanishes"), read in the other direction. -/
theorem g34b_toBlocks₁₁_eq_zero {n : ℕ} (G : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) 𝕂)
    (hiso : ∀ x ∈ Submodule.span 𝕂
        (Set.range fun i : Fin n => (Pi.single (Sum.inl i) 1 : Fin n ⊕ Fin n → 𝕂)),
      ∀ y ∈ Submodule.span 𝕂
        (Set.range fun i : Fin n => (Pi.single (Sum.inl i) 1 : Fin n ⊕ Fin n → 𝕂)),
      star x ⬝ᵥ (G *ᵥ y) = 0) :
    G.toBlocks₁₁ = 0 :=
  g34b_toBlocks₁₁_eq_zero_aux G hiso

example : g34b_S.toBlocks₁₁ = 0 :=
  g34b_toBlocks₁₁_eq_zero g34b_S fun x hx y hy =>
    g34b_h2.isotropic x (g34b_I_eq ▸ hx) y (g34b_I_eq ▸ hy)

/-- **Split determinant**: a Hermitian matrix `(0 A; Aᴴ B)` with `n × n` blocks has determinant
`(-1)ⁿ det A · conj(det A)`, so its class is `[(-1)ⁿ]` modulo norms.
Source: G34 v1.5, Section 2 ("the Hermitian spaces of signature `(n, n)` with a totally isotropic
subspace of dimension `n` are exactly those of discriminant `(-1)ⁿ`") and the proof of
Proposition 8.5 ("By (H2), `(V_par, h)` has a totally isotropic subspace of dimension `n`, so `h`
is split"). -/
theorem g34b_det_isotropic {n : ℕ} (G : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) 𝕂)
    (hG : G.IsHermitian) (h₀ : G.toBlocks₁₁ = 0) :
    G.det = (-1) ^ n * (G.toBlocks₁₂.det * star G.toBlocks₁₂.det) :=
  g34b_det_isotropic_aux G hG h₀

example (G : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) 𝕂) (hG : G.IsHermitian)
    (h₀ : G.toBlocks₁₁ = 0) : G.det = G.toBlocks₁₂.det * star G.toBlocks₁₂.det := by
  rw [g34b_det_isotropic G hG h₀]; norm_num

end Generic

section Deposited

/-- **`h = ϑ𝒮` is Hermitian**: `(ϑ S)ᴴ = ϑ̄ Sᴴ = (-ϑ)(-S)`.
Source: G34 v1.5, Section 7 (`h = ϑ𝒮`, Hermitian since `𝒮` is skew-Hermitian). -/
theorem g34b_hGram_isHermitian : g34b_hGram.IsHermitian :=
  g34b_hGram_isHermitian_aux

example : g34b_hGramᴴ = g34b_hGram := g34b_hGram_isHermitian

/-- **The determinant of `h` is a nonzero norm**: `det (ϑ S) = x x̄` for some `x ≠ 0`, by
`g34b_det_isotropic` with the zero block of (H2).
Source: G34 v1.5, proof of Proposition 8.5 ("`h` is split") and Appendix A. -/
theorem g34b_hGram_det_norm : ∃ x : 𝕂, x ≠ 0 ∧ g34b_hGram.det = x * star x :=
  g34b_hGram_det_norm_aux

example : g34b_hGram.det ≠ 0 := by
  obtain ⟨x, hx, h⟩ := g34b_hGram_det_norm
  rw [h]
  exact mul_ne_zero hx (star_ne_zero.2 hx)

/-- **The complex weight-zero space of the printed cone element is `I_ℂ`**: for a sign `ε` and
positive `c_j`, the range of `Σ_j M_j = ε Σ_j c_j N_j` (mapped along `ι`) is the complexification
of `I`; from `g34b_cone_range` and `g34b_range_map`.
Source: G34 v1.5, Lemma 8.3 (`im M = I`, `W₀ = I`). -/
theorem g34b_cone_range_deposited (ι : 𝕂 →+* ℂ) (ε : ℤ) (hε : ε = 1 ∨ ε = -1)
    (c : Fin 17 → ℕ) (hc : ∀ j, 0 < c j) :
    LinearMap.range (Matrix.toLin' (∑ j, g34b_Mlog ι ε c j)) =
      g34b_complexify ι (g34b_I g34b_N) :=
  g34b_cone_range_deposited_aux ι ε hε c hc

example (ι : 𝕂 →+* ℂ) :
    LinearMap.range (Matrix.toLin' (∑ j, g34b_Mlog ι 1 (fun _ => 1) j)) =
      g34b_complexify ι (g34b_I g34b_N) :=
  g34b_cone_range_deposited ι 1 (Or.inl rfl) (fun _ => 1) fun _ => one_pos

/-- **The tangent map of the printed logarithms is onto**: for a sign `ε`, positive `c_j` and a
`4`-dimensional `F₀` meeting the weight-zero space `im Σ_j M_j` trivially, the tangent map of
`M_j = ε c_j N_j` is surjective onto `Hom(F₀, ℂ⁸ / F₀)`, of dimension `16`. From (H2)–(H4) for the
printed data and Lemmas 8.3 and 8.4 in their Lean form.
Source: G34 v1.5, Lemmas 8.3 and 8.4, the proof of Theorem A in Section 9, and Appendix A. -/
theorem g34b_tangent_surjective_deposited (ι : 𝕂 →+* ℂ) (ε : ℤ) (hε : ε = 1 ∨ ε = -1)
    (c : Fin 17 → ℕ) (hc : ∀ j, 0 < c j) (F₀ : Submodule ℂ (Fin 4 ⊕ Fin 4 → ℂ))
    (hF : Module.finrank ℂ F₀ = 4)
    (hHT : F₀ ⊓ LinearMap.range (Matrix.toLin' (∑ j, g34b_Mlog ι ε c j)) = ⊥) :
    Function.Surjective (g34b_tangentMap (g34b_Mlog ι ε c) F₀) :=
  g34b_tangent_surjective_deposited_aux ι ε hε c hc F₀ hF hHT

example (F : wtr_UniversalFamily 4 1) {S : Type} (fiber : S → wtr_Variety 4)
    (Φ : g34b_BoundaryPeriodMap F fiber) :
    Function.Surjective (g34b_tangentMap (g34b_Mlog Φ.ι Φ.ε Φ.c) Φ.F₀) :=
  g34b_tangent_surjective_deposited Φ.ι Φ.ε Φ.ε_sign Φ.c Φ.c_pos Φ.F₀ Φ.F₀_finrank Φ.hodgeTate

end Deposited

section Discriminant

/-- **A scaled norm has class `[1]`**: if `q ∈ ℚˣ` equals `c⁸ · x x̄` with `c ∈ ℚˣ`, then
`[q] = 1` in `ℚˣ ⧸ Nm(Kˣ)` (`c⁸ = Nm(c⁴)` and `x x̄ = Nm(x)`).
Source: G34 v1.5, Section 2 ("such a change multiplies `det H` by a `2n`-th power of a rational
number, which is a norm") and the proof of Proposition 7.1. -/
theorem g34b_norm_class (q c : ℚ) (hq : q ≠ 0) (hc : c ≠ 0) (x : 𝕂)
    (h : algebraMap ℚ 𝕂 q = (c : 𝕂) ^ 8 * (x * star x)) :
    ((Units.mk0 q hq : ℚˣ) : ℚˣ ⧸ normSubgroup 𝕂) = 1 :=
  g34b_norm_class_aux q c hq hc x h

example : ((Units.mk0 (6561 : ℚ) (by norm_num) : ℚˣ) : ℚˣ ⧸ normSubgroup 𝕂) = 1 :=
  g34b_norm_class 6561 1 (by norm_num) one_ne_zero 81 (by norm_num [map_ofNat, star_ofNat])

/-- **Stage bridge: split discriminant.** If every fibre carries the parabolic-polarization
comparison, every fibre has discriminant `[1]`: the exact type of `WeilTransferDatum.fiber_disc`
and `wtr_StageFields.fiber_disc` at `(4, [1])`. The Gram determinant is `c⁸ det h` (or its
conjugate), and `det h` is a norm by (H2) (`g34b_hGram_det_norm`).
Source: G34 v1.5, Proposition 7.1 and the proof of Proposition 8.5 (the discriminant). -/
theorem g34b_fiber_disc {S : Type} (fiber : S → wtr_Variety 4)
    (fiber_polarized : ∀ s, wtr_PolarizedWeil 4 (fiber s))
    (hpar : ∀ s, g34b_ParabolicPolarization (fiber_polarized s)) :
    ∀ s, wtr_disc (fiber_polarized s) = 1 :=
  g34b_fiber_disc_aux fiber fiber_polarized hpar

example {S : Type} (fiber : S → wtr_Variety 4)
    (fiber_polarized : ∀ s, wtr_PolarizedWeil 4 (fiber s))
    (hpar : ∀ s, g34b_ParabolicPolarization (fiber_polarized s)) (s : S) :
    wtr_IsMember 4 1 (fiber s) :=
  ⟨fiber_polarized s, g34b_fiber_disc fiber fiber_polarized hpar s⟩

end Discriminant

section Bridge

/-- **The period map has rank `16` at some point.** The derivative matrices along `pt k`, after
invertible changes of coordinates, converge to the matrix of the tangent map in a chart; the
tangent map is onto (`g34b_tangent_surjective_deposited`), so the limit has rank `16`; by
`g34b_rank_eventually` some `pt k` has derivative of rank `16`.
Source: G34 v1.5, proof of Proposition 8.5 ("the period map has rank `n²` at interior points near
the boundary"). -/
theorem g34b_period_rank (F : wtr_UniversalFamily 4 1) {S : Type}
    (fiber : S → wtr_Variety 4) (Φ : g34b_BoundaryPeriodMap F fiber) :
    ∃ t ∈ Φ.V, Module.finrank ℂ
      (LinearMap.range (fderiv ℂ Φ.period t : (Fin 17 → ℂ) →ₗ[ℂ] Fin (4 ^ 2) → ℂ)) = 4 ^ 2 :=
  g34b_period_rank_aux F fiber Φ

example (F : wtr_UniversalFamily 4 1) {S : Type} (fiber : S → wtr_Variety 4)
    (Φ : g34b_BoundaryPeriodMap F fiber) :
    ∃ t ∈ Φ.V, Φ.period t ∈ (wtr_Domain 4 : Set (Fin (4 ^ 2) → ℂ)) :=
  let ⟨t, ht, _⟩ := g34b_period_rank F fiber Φ
  ⟨t, ht, Φ.mapsTo ht⟩

/-- **Dominance, the bridge to the stage field.** From a boundary period map, a nonempty open
`U ⊆ 𝓗₄` each of whose points is the target of a `K`-linear polarized isogeny from some fibre:
the exact type of `wtr_StageFields.dominant` over `F` (and of `WeilTransferDatum.dominant` with
`M = wtr_Domain 4`). The open set is the preimage in `𝓗₄` of the open set of `g34b_open_image` at
the point of `g34b_period_rank`.
Source: G34 v1.5, Proposition 8.5 ("`S` is dominant") and the proof of Theorem 6.2 ("`Φ(D)`
contains a ball `𝓑`" and the isogeny `N μ : A_σ(C) → A_z`). -/
theorem g34b_dominant (F : wtr_UniversalFamily 4 1) {S : Type}
    (fiber : S → wtr_Variety 4) (Φ : g34b_BoundaryPeriodMap F fiber) :
    ∃ U : Set (wtr_Domain 4), IsOpen U ∧ U.Nonempty ∧
      ∀ m ∈ U, ∃ s, wtr_KIsog (fiber s) (F.univ m) :=
  g34b_dominant_aux F fiber Φ

/-- Both fields of this stage fill a `wtr_StageFields F`, with the other stages' fields. -/
example (F : wtr_UniversalFamily 4 1) {S : Type} (fiber : S → wtr_Variety 4)
    (fiber_polarized : ∀ s, wtr_PolarizedWeil 4 (fiber s))
    (hpar : ∀ s, g34b_ParabolicPolarization (fiber_polarized s))
    (Φ : g34b_BoundaryPeriodMap F fiber) (fiber_alg : ∀ s, wtr_WeilAlg (fiber s))
    (spread : ∃ C : Set (Set (wtr_Domain 4)), C.Countable ∧
      (∀ Z ∈ C, IsClosedAnalytic (Fin (4 ^ 2) → ℂ) Z) ∧ {m | wtr_WeilAlg (F.univ m)} = ⋃₀ C)
    (transport : ∀ P Q : wtr_Variety 4, wtr_KIsog P Q → (wtr_WeilAlg P ↔ wtr_WeilAlg Q)) :
    wtr_StageFields F :=
  ⟨S, fiber, fiber_polarized, g34b_fiber_disc fiber fiber_polarized hpar, fiber_alg,
    g34b_dominant F fiber Φ, spread, transport⟩

/-- **G34 Theorem A from the boundary stage and the other stage fields.** With a universal family
over `𝓗₄` for discriminant `[1]`, a family of fibres with the parabolic-polarization comparison
and a boundary period map, and the fields `fiber_alg`, `spread` and `transport` of the other
stages, `G34TheoremAStatement A` holds for every `A`: this stage supplies `fiber_disc`
(`g34b_fiber_disc`) and `dominant` (`g34b_dominant`), and `wtr_g34A_of_transfer` applies to
`wtr_transferFields`.

This is the implication from the premises and the other stage fields; none of them is asserted.
Source: G34 v1.5, proof of Theorem A in Section 9 (Proposition 8.5 and Theorem 6.2);
`wtr_g34A_of_transfer`. -/
theorem g34b_theoremA_of_boundary (F : wtr_UniversalFamily 4 1) {S : Type}
    (fiber : S → wtr_Variety 4) (fiber_polarized : ∀ s, wtr_PolarizedWeil 4 (fiber s))
    (hpar : ∀ s, g34b_ParabolicPolarization (fiber_polarized s))
    (Φ : g34b_BoundaryPeriodMap F fiber) (fiber_alg : ∀ s, wtr_WeilAlg (fiber s))
    (spread : ∃ C : Set (Set (wtr_Domain 4)), C.Countable ∧
      (∀ Z ∈ C, IsClosedAnalytic (Fin (4 ^ 2) → ℂ) Z) ∧ {m | wtr_WeilAlg (F.univ m)} = ⋃₀ C)
    (transport : ∀ P Q : wtr_Variety 4, wtr_KIsog P Q → (wtr_WeilAlg P ↔ wtr_WeilAlg Q))
    (A : Over (Spec ↧ℂ))
    [GrpObj A] [IsCommMonObj A] [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom] :
    G34TheoremAStatement A :=
  g34b_theoremA_of_boundary_aux F fiber fiber_polarized hpar Φ fiber_alg spread transport A

end Bridge

end HodgeLean.Papers
