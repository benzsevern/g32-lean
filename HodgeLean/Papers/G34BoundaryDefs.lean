import HodgeLean.Papers.WeilTransferDefs
import HodgeLean.Foundations.WeilHermitian

/-! # G34 Theorem A, the boundary certificate: definitions

G34 v1.5, Section 8, proves that the Hurwitz component `S` of the tuple of Appendix A is dominant
and that its discriminant is split, from the logarithms `N_j` of the local monodromies at a
maximal degeneration and four conditions (H1)–(H4) on them. This file records:

* the printed finite data of Appendix A over `K = ℚ(√-3)`: the Gram matrix `g34b_S` of the
  skew-Hermitian cup product `𝒮` in the basis `b₁, …, b₈` of `V_par`, the seventeen blocks
  `g34b_X j`, the logarithms `g34b_N j = (0 X_j; 0 0)`, and the Gram matrix `g34b_hGram` of
  `h = ϑ𝒮`;
* the conditions (H1)–(H4) as predicates on a family of matrices (`g34b_H1`, `g34b_H2`,
  `g34b_H3`, `g34b_H4`), with `I = Σ_j im N_j` (`g34b_I`) and the forms
  `β_j(x, y) = 𝒮(x, N_j y)` (`g34b_beta`);
* the complexification of a `K`-subspace along an embedding `K → ℂ` (`g34b_complexify`), the
  space `{X | X(V) ⊆ I, X(I) = 0}` (`g34b_boundaryAlg`), the tangent map
  `v ↦ [Σ_j v_j M_j |_{F₀}] ∈ Hom(F₀, V/F₀)` of Lemma 8.4 (`g34b_tangentMap`), and the
  logarithms `M_j = ε c_j N_j` of Lemma 8.2 (`g34b_Mlog`);
* two named premises: the parabolic-polarization comparison of Proposition 7.1
  (`g34b_ParabolicPolarization`) and the boundary period map of Section 8
  (`g34b_BoundaryPeriodMap`), which carries the Gauss–Manin and local-monodromy identification,
  the Hodge–Tate input of Cattani–Kaplan–Schmid, and the derivative limit of the nilpotent orbit
  normal form.

Nothing here asserts (H1)–(H4), a rank, an open image, dominance, a discriminant or algebraicity.
HC no distance; AV milestone no distance.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace Set Filter
open Matrix
open scoped Topology Matrix
open HodgeLean.RealDefs HodgeLean.Foundations HodgeLean.Foundations.WeilPower
open HodgeLean.Foundations.Symplectic HodgeLean.Foundations.HermitianForm HodgeLean.Adapters
open HodgeLean.Foundations.WeilHermitian

namespace HodgeLean.Papers

local notation "𝕂" => QuadraticAlgebra ℚ (-3) 0

section Data

/-- **The primitive cube root of unity** `ω = (-1 + √-3) / 2` of the printed matrices; in
`QuadraticAlgebra ℚ (-3) 0` the generator `QuadraticAlgebra.omega` is `√-3`.
Source: G34 v1.5, Appendix A ("Write elements of `K = ℚ(ω)` as `a + bω`"). -/
def g34b_ω : 𝕂 := (-1 + QuadraticAlgebra.omega) / 2

example : g34b_ω = (-1 + QuadraticAlgebra.omega) / 2 := rfl

/-- **The seventeen printed blocks** `X₁, …, X₁₇` (index `j` here is `X_{j+1}` there), the
upper-right `4 × 4` blocks of the logarithms `N_j` in the basis `b₁, …, b₈`.
Source: G34 v1.5, Appendix A, paragraph "The matrices". -/
def g34b_X : Fin 17 → Matrix (Fin 4) (Fin 4) 𝕂 :=
  let w := g34b_ω
  ![!![2, 1/3 - 1/3*w, 1/3 + 2/3*w, -w; 2 + w, 2, 0, 2 + w; -1 - 2*w, 0, 2, -1 + w;
      1 + w, 1/3 - 1/3*w, -2/3 - 1/3*w, 2],
    !![2, -2*w, -2/3 + 2/3*w, 2 - 2*w; 6 + 6*w, 6, -4 - 2*w, 12 + 6*w;
      -4 - 2*w, -2 + 2*w, 2, -6; 4 + 2*w, 2 - 2*w, -2, 6],
    !![0, 0, 0, 0; 0, 3, -w, 3 + 3*w; 0, 1 + w, 3, 3*w; 0, -w, -1 - w, 3],
    !![0, 0, 0, 0; 0, 2, 0, 2 + w; 0, 0, 2, -1 + w; 0, 1/3 - 1/3*w, -2/3 - 1/3*w, 2],
    !![0, 0, 0, 0; 0, 0, 0, 0; 0, 0, 4, -2 + 2*w; 0, 0, -4/3 - 2/3*w, 3],
    !![0, 0, 0, 0; 0, 0, 0, 0; 0, 0, 2, 0; 0, 0, 0, 0],
    !![0, 0, 0, 0; 0, 0, 0, 0; 0, 0, 2, -1 + w; 0, 0, -2/3 - 1/3*w, 2],
    !![0, 0, 0, 0; 0, 0, 0, 0; 0, 0, 0, 0; 0, 0, 0, 2],
    !![2, 2, -4/3 - 2/3*w, 2; 6, 6, -4 - 2*w, 6; -2 + 2*w, -2 + 2*w, 2, -2 + 2*w;
      2, 2, -4/3 - 2/3*w, 2],
    !![3, 2 - w, -2 - w, 3; 9 + 3*w, 8, -5 - 4*w, 9 + 3*w; -3 + 3*w, -1 + 4*w, 3, -3 + 3*w;
      3, 2 - w, -2 - w, 3],
    !![5, 4/3 - 7/3*w, -4/3 + 1/3*w, 3 - 2*w; 11 + 7*w, 8, -5 - 3*w, 11 + 4*w;
      -5 - w, -2 + 3*w, 4, -5 + 2*w; 5 + 2*w, 7/3 - 4/3*w, -7/3 - 2/3*w, 5],
    !![7, 2/3 - 11/3*w, -2/3 + 5/3*w, 3 - 4*w; 13 + 11*w, 9, -5 - 2*w, 13 + 5*w;
      -7 - 5*w, -3 + 2*w, 5, -7 + w; 7 + 4*w, 8/3 - 5/3*w, -8/3 - 1/3*w, 7],
    !![5, 4/3 - 7/3*w, -1/3 + 4/3*w, 3 - 2*w; 11 + 7*w, 8, -3, 11 + 4*w;
      -5 - 4*w, -3, 3, -5 - w; 5 + 2*w, 7/3 - 4/3*w, -4/3 + 1/3*w, 5],
    !![2, 4/3 - 4/3*w, -4/3 - 2/3*w, 2; 8 + 4*w, 8, -4 - 4*w, 8 + 4*w;
      -2 + 2*w, 4*w, 2, -2 + 2*w; 2, 4/3 - 4/3*w, -4/3 - 2/3*w, 2],
    !![0, 0, 0, 0; 0, 2, -2 - 2*w, 4 + 2*w; 0, 2*w, 2, -2 + 2*w;
      0, 2/3 - 2/3*w, -4/3 - 2/3*w, 2],
    !![2, -w, 1/3 + 2/3*w, 1 - w; 3 + 3*w, 3, -2 - w, 6 + 3*w; -1 - 2*w, -1 + w, 2, -3;
      2 + w, 1 - w, -1, 3],
    !![2, 2/3 - 2/3*w, 0, 2; 4 + 2*w, 2, 0, 4 + 2*w; 0, 0, 0, 0;
      2, 2/3 - 2/3*w, 0, 2]]

/-- The sixth block `X₆` has the single entry `2` at position `(3, 3)`. -/
example : g34b_X 5 = !![0, 0, 0, 0; 0, 0, 0, 0; 0, 0, 2, 0; 0, 0, 0, 0] := rfl

/-- **The logarithms** `N_j = (0 X_j; 0 0)` in the basis `b₁, …, b₈` of `V_par`, the first four
coordinates (`Sum.inl`) being `b₁, …, b₄`.
Source: G34 v1.5, Appendix A ("In this basis every `N_j` has the block form"). -/
def g34b_N (j : Fin 17) : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) 𝕂 :=
  Matrix.fromBlocks 0 (g34b_X j) 0 0

example (j : Fin 17) : (g34b_N j).toBlocks₁₂ = g34b_X j := by
  simp [g34b_N]

/-- **The lower-left block** `D = diag(-3, -1, -1, -3)` of `S`; on `V_par / I` the form `β_j` has
matrix `D X_j`.
Source: G34 v1.5, Appendix A ("`D = diag(-3,-1,-1,-3)` is the lower left block of `S`"). -/
def g34b_D : Matrix (Fin 4) (Fin 4) 𝕂 := Matrix.diagonal ![-3, -1, -1, -3]

example : g34b_D 0 0 = -3 := rfl

/-- **The Gram matrix of the skew-Hermitian cup product** `𝒮(x, y) = x̄ᵀ S y` in the basis
`b₁, …, b₈`, as printed: upper-left block `0`, upper-right `diag(3, 1, 1, 3)`, lower-left `D`.
Source: G34 v1.5, Appendix A ("the Gram matrix of the skew-Hermitian form is"); Lemma 7.2. -/
def g34b_S : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) 𝕂 :=
  let w := g34b_ω
  Matrix.fromBlocks 0 (Matrix.diagonal ![3, 1, 1, 3]) g34b_D
    !![-3 - 6*w, -3 - 3*w, 4 + 5*w, -6 - 6*w; -3*w, -1 - 2*w, 1 + 4*w, -2 - 4*w;
      1 + 5*w, 3 + 4*w, -2 - 4*w, 3 + 6*w; -6*w, -2 - 4*w, 3 + 6*w, -3 - 6*w]

example : g34b_S.toBlocks₂₁ = g34b_D := by
  simp [g34b_S]

/-- **The Gram matrix of the Hermitian form** `h = ϑ𝒮`, with `ϑ = √-3` (`ϑ̄ = -ϑ`).
Source: G34 v1.5, Section 7 (`h = ϑ𝒮`) and Appendix A. -/
def g34b_hGram : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) 𝕂 :=
  (QuadraticAlgebra.omega : 𝕂) • g34b_S

example : g34b_hGram = (QuadraticAlgebra.omega : 𝕂) • g34b_S := rfl

end Data

section Conditions

variable {m : Type*} [Fintype m] [DecidableEq m] {r : ℕ}

/-- **The subspace** `I = Σ_j im N_j` of `K^m`.
Source: G34 v1.5, Section 8, condition (H2). -/
def g34b_I (N : Fin r → Matrix m m 𝕂) : Submodule 𝕂 (m → 𝕂) :=
  ⨆ j, LinearMap.range (Matrix.toLin' (N j))

example (N : Fin r → Matrix m m 𝕂) (j : Fin r) (x : m → 𝕂) : N j *ᵥ x ∈ g34b_I N :=
  Submodule.mem_iSup_of_mem j ⟨x, rfl⟩

/-- **The form** `β(x, y) = 𝒮(x, N y) = x̄ᵀ S N y` attached to a logarithm `N`.
Source: G34 v1.5, Section 8, condition (H3). -/
def g34b_beta (S N : Matrix m m 𝕂) (x y : m → 𝕂) : 𝕂 :=
  star x ⬝ᵥ ((S * N) *ᵥ y)

example (S N : Matrix m m 𝕂) (y : m → 𝕂) : g34b_beta S N 0 y = 0 := by
  simp [g34b_beta]

/-- **(H1)**: `N_j N_k = 0` for all `j, k`.
Source: G34 v1.5, Section 8, condition (H1). -/
def g34b_H1 (N : Fin r → Matrix m m 𝕂) : Prop :=
  ∀ j k, N j * N k = 0

example : g34b_H1 (fun _ : Fin 3 => (0 : Matrix (Fin 2) (Fin 2) 𝕂)) := fun _ _ => by simp

/-- **(H2)**: `I = Σ_j im N_j` has `K`-dimension `n`, is totally isotropic for `𝒮` (hence for
`h = ϑ𝒮`), and is killed by every `N_j`.
Source: G34 v1.5, Section 8, condition (H2). -/
structure g34b_H2 (S : Matrix m m 𝕂) (N : Fin r → Matrix m m 𝕂) (n : ℕ) : Prop where
  /-- `dim_K I = n`. -/
  finrank_eq : Module.finrank 𝕂 (g34b_I N) = n
  /-- `I` is totally isotropic. -/
  isotropic : ∀ x ∈ g34b_I N, ∀ y ∈ g34b_I N, star x ⬝ᵥ (S *ᵥ y) = 0
  /-- Every `N_j` kills `I`. -/
  kill : ∀ j, ∀ x ∈ g34b_I N, N j *ᵥ x = 0

/-- **(H3)**: the forms `β_j` are Hermitian, semidefinite of one common sign `σ ∈ {1, -1}`, and
`Σ_j β_j` is definite on `V / I` (strictly signed off `I`). For a Hermitian form `β(x, x)` is
rational, so its sign is read on the rational coordinate `re`.
Source: G34 v1.5, Section 8, condition (H3). -/
structure g34b_H3 (S : Matrix m m 𝕂) (N : Fin r → Matrix m m 𝕂) : Prop where
  /-- Each `β_j` is Hermitian. -/
  herm : ∀ j x y, g34b_beta S (N j) y x = star (g34b_beta S (N j) x y)
  /-- The common sign. -/
  sign : ∃ σ : ℚ, (σ = 1 ∨ σ = -1) ∧ (∀ j x, 0 ≤ σ * (g34b_beta S (N j) x x).re) ∧
    ∀ x ∉ g34b_I N, 0 < σ * (∑ j, g34b_beta S (N j) x x).re

/-- **(H4)**: the `N_j` span a `ℚ`-vector space of dimension `n²`.
Source: G34 v1.5, Section 8, condition (H4). -/
def g34b_H4 (N : Fin r → Matrix m m 𝕂) (n : ℕ) : Prop :=
  Module.finrank ℚ (Submodule.span ℚ (Set.range N)) = n ^ 2

example (N : Fin r → Matrix m m 𝕂) (n : ℕ) :
    g34b_H4 N n ↔ Module.finrank ℚ (Submodule.span ℚ (Set.range N)) = n ^ 2 := Iff.rfl

end Conditions

section Complex

variable {m : Type*} [Fintype m] [DecidableEq m] {r : ℕ}

/-- **The complexification** `U_ℂ ⊆ ℂ^m` of a `K`-subspace `U ⊆ K^m` along an embedding
`ι : K → ℂ`: the `ℂ`-span of the images of its vectors.
Source: G34 v1.5, Section 8 ("Fix an embedding `K ⊂ ℂ` and write `V_{par,ℂ}`, `I_ℂ` for the
scalar extensions along it"). -/
def g34b_complexify (ι : 𝕂 →+* ℂ) (U : Submodule 𝕂 (m → 𝕂)) : Submodule ℂ (m → ℂ) :=
  Submodule.span ℂ ((fun x : m → 𝕂 => fun i => ι (x i)) '' U)

example (ι : 𝕂 →+* ℂ) (U : Submodule 𝕂 (m → 𝕂)) (x : m → 𝕂) (hx : x ∈ U) :
    (fun i => ι (x i)) ∈ g34b_complexify ι U :=
  Submodule.subset_span ⟨x, hx, rfl⟩

/-- **The boundary algebra** `{X ∈ M_m(ℂ) | X(ℂ^m) ⊆ J, X(J) = 0}` of a subspace `J`; for
`J = I_ℂ` it is `Hom(V_ℂ / I_ℂ, I_ℂ)`, the complexification of `𝔫_I` in Lemma 8.4.
Source: G34 v1.5, proof of Lemma 8.4 (`𝔫_I = {X ∈ 𝔲(h) : X(V_par) ⊆ I, X(I) = 0}` and its
complexification `Hom(V_ℂ / I_ℂ, I_ℂ)`). -/
def g34b_boundaryAlg (J : Submodule ℂ (m → ℂ)) : Submodule ℂ (Matrix m m ℂ) where
  carrier := {X | (∀ v, X *ᵥ v ∈ J) ∧ ∀ v ∈ J, X *ᵥ v = 0}
  zero_mem' := ⟨fun v => by simp, fun v _ => by simp⟩
  add_mem' := fun {X Y} hX hY =>
    ⟨fun v => by rw [Matrix.add_mulVec]; exact J.add_mem (hX.1 v) (hY.1 v),
      fun v hv => by rw [Matrix.add_mulVec, hX.2 v hv, hY.2 v hv, add_zero]⟩
  smul_mem' := fun c X hX =>
    ⟨fun v => by rw [Matrix.smul_mulVec]; exact J.smul_mem c (hX.1 v),
      fun v hv => by rw [Matrix.smul_mulVec, hX.2 v hv, smul_zero]⟩

example (J : Submodule ℂ (m → ℂ)) : (0 : Matrix m m ℂ) ∈ g34b_boundaryAlg J :=
  Submodule.zero_mem _

/-- **The tangent map of Lemma 8.4** at a filtration `F₀`: `v ↦ [Σ_j v_j M_j |_{F₀}]`, the class
of the restriction to `F₀` in `Hom(F₀, ℂ^m / F₀)`, the tangent space of the compact dual at `F₀`
(here `F₀` stands for `F¹₀`). The `j`-th column is `M_j · F₀`.
Source: G34 v1.5, Lemma 8.4 (`v ↦ Σ_j v_j M_j · F₀` into `Hom(F¹₀, V_ℂ / F¹₀)`). -/
def g34b_tangentMap (M : Fin r → Matrix m m ℂ) (F₀ : Submodule ℂ (m → ℂ)) :
    (Fin r → ℂ) →ₗ[ℂ] (F₀ →ₗ[ℂ] (m → ℂ) ⧸ F₀) :=
  ∑ j, (LinearMap.proj j : (Fin r → ℂ) →ₗ[ℂ] ℂ).smulRight
    (F₀.mkQ ∘ₗ Matrix.toLin' (M j) ∘ₗ F₀.subtype)

example (M : Fin r → Matrix m m ℂ) (F₀ : Submodule ℂ (m → ℂ)) :
    g34b_tangentMap M F₀ 0 = 0 :=
  map_zero _

/-- **The monodromy logarithms of Lemma 8.2** `M_j = ε c_j N_j`, mapped to `ℂ` along `ι`, for a
sign `ε` and multiplicities `c_j`.
Source: G34 v1.5, Lemma 8.2 (logarithm `ε c_j N_j` after the base change
`w_j^{|Z(G)| k_j m_j} = q_j`) and Section 8 (`M_j = ε c_j N_j`). -/
def g34b_Mlog (ι : 𝕂 →+* ℂ) (ε : ℤ) (c : Fin 17 → ℕ) (j : Fin 17) :
    Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) ℂ :=
  ((ε * c j : ℤ) : ℂ) • (g34b_N j).map ι

example (ι : 𝕂 →+* ℂ) (j : Fin 17) : g34b_Mlog ι 1 (fun _ => 1) j = (g34b_N j).map ι := by
  simp [g34b_Mlog]

end Complex

section Premises

/-- **The parabolic-polarization comparison (premise).** In a `K`-basis of the fibre's Weil
Hermitian space, indexed like `b₁, …, b₈`, the geometric Hermitian Gram matrix is a nonzero
rational multiple of `g34b_hGram` (the form `h = ϑ𝒮`), or of its conjugate (Proposition 7.1
allows a `K`-antilinear identification, which conjugates the Gram matrix).
Source: G34 v1.5, Proposition 7.1 (`H₁(A_σ(C), ℚ) ≅ V_par`, `H` a nonzero rational multiple of
`h` or of `h̄`) and Lemma 7.2 (the cocycle formula for `𝒮`); Appendix A (the matrix `S`). -/
def g34b_ParabolicPolarization {P : wtr_Variety 4} (h : wtr_PolarizedWeil 4 P) : Prop :=
  let hT := torusCohomology_cupProductOf P.X
  letI := hT.finite
  let E := polarizationForm hT h.nondegenerate
  let J := ⟨P.W.J, P.W.J_sq⟩
  let H := weilHermitian E J
    (by simpa [E, polarizationForm] using
      (isRosatiSkew_iff_dualForm h.nondegenerate P.W.J).1 h.rosati)
  ∃ c : ℚ, c ≠ 0 ∧
    ∃ e : Module.Basis (Fin 4 ⊕ Fin 4) 𝕂 (WithJ (HQ P.X 1) J),
      LinearMap.toMatrix₂ e e H = (c : 𝕂) • g34b_hGram ∨
        LinearMap.toMatrix₂ e e H = (c : 𝕂) • g34b_hGram.map star

/-- The comparison premise supplies a scale and a basis. -/
example {P : wtr_Variety 4} (h : wtr_PolarizedWeil 4 P) (H : g34b_ParabolicPolarization h) :
    ∃ c : ℚ, c ≠ 0 :=
  let ⟨c, hc, _⟩ := H
  ⟨c, hc⟩

/-- **The boundary period map (premise).** Over a universal family `F` for `M(4, ℚ(√-3), [1])`
and a family of carriers `fiber : S → wtr_Variety 4` (the factors `A_σ(C)` of the G34 covers):

* `V`, `period`, `analytic`, `mapsTo`, `isog`: an open set `V ⊆ ℂ¹⁷` of base-changed smoothing
  parameters `w` near the maximal degeneration (interior points, all `w_j ≠ 0`), and the period
  map `w ↦` complex structure of `H₁(A_σ(C_w), ℝ)` transported by a Landherr marking, in the
  bounded coordinates of `wtr_Domain 4`, analytic, with each parameter value a fibre `K`-isogenous
  to the universal fibre at its period;
* `ι`, `ε`, `c`: the embedding `K ⊂ ℂ`, the sign `ε` and the positive multiplicities `c_j` of
  Lemma 8.2. The Gauss–Manin identification (Lemma 8.1: the monodromy of the full twist on
  `V_par` is the pullback of parabolic cocycles, whose logarithm in the basis `b₁, …, b₈` is the
  printed `N_j`) and the admissible-cover local monodromy after finite base change (Lemma 8.2:
  the logarithm around `w_j = 0` is `ε c_j N_j`) enter as the use of `g34b_Mlog ι ε c`, built
  from the deposited `g34b_N`, in the two fields below;
* `F₀`, `F₀_finrank`, `hodgeTate`: the limit Hodge filtration `F¹₀ = ψ(0)` of dimension `4`, and
  the Cattani–Kaplan–Schmid input that `F¹₀` meets the weight-zero space `W₀ = im M` of the cone
  element `M = Σ_j M_j` trivially (`Gr^W_0` is of type `(0, 0)`);
* `pt`, `chart`, `L`, `R`, `limit`: the nilpotent orbit normal form, differentiated: along
  points `pt k ∈ V` approaching the boundary, the derivative matrix of `period`, after invertible
  changes of coordinates (the translation by `exp(-Σ z_j M_j)`, `∂/∂z_j = 2πi w_j ∂/∂w_j`, and the
  identification of the tangent spaces of `𝓗₄` and of the compact dual), converges to the matrix
  of the tangent map `v ↦ Σ_j v_j M_j · F₀` in a fixed chart of `Hom(F¹₀, V_ℂ / F¹₀)`.

No field states an open set of `𝓗₄`, a rank, dominance, (H1)–(H4), a discriminant, algebraicity,
spreading or transport. The rank of the limit is the frozen `g34b_tangent_surjective_deposited`
(from (H1)–(H4) and `hodgeTate`), and the open image is the frozen `g34b_open_image` (the
inverse function theorem). The repository has no variations of Hodge structure, local systems,
parabolic cohomology, Hurwitz spaces, admissible covers or compact duals of period domains, so
their outputs are recorded here as fields. This structure is a premise; nothing derives it.
Source: G34 v1.5, Section 8: Lemma 8.1 (Dettweiler–Wewers, *Variation of local systems and
parabolic cohomology*, Israel J. Math. 156 (2006), Lemma 2.2 and Theorem 2.5), Lemma 8.2
(Knudsen, Math. Scand. 52 (1983), Theorem 2.7; Harris–Mumford, Invent. Math. 67 (1982), §4;
Fried–Völklein, Math. Ann. 290 (1991), §1.2), the several-variable nilpotent orbit theorem
(Schmid, Invent. Math. 22 (1973), (4.12); Cattani–Kaplan–Schmid, Ann. of Math. 123 (1986),
(1.15)), Lemma 8.3 (Cattani–Kaplan–Schmid, (4.5)), the first paragraph of the proof of
Proposition 8.5; Theorem 6.2 (the period map `Φ` and the isogeny `N μ`) and Lemma 2.2. -/
structure g34b_BoundaryPeriodMap (F : wtr_UniversalFamily 4 1) {S : Type}
    (fiber : S → wtr_Variety 4) where
  /-- The parameter set near the boundary point. -/
  V : Set (Fin 17 → ℂ)
  /-- It is open. -/
  isOpen_V : IsOpen V
  /-- The period map in bounded coordinates. -/
  period : (Fin 17 → ℂ) → Fin (4 ^ 2) → ℂ
  /-- The period map is analytic on `V`. -/
  analytic : AnalyticOnNhd ℂ period V
  /-- It lands in `𝓗₄`. -/
  mapsTo : MapsTo period V (wtr_Domain 4 : Set (Fin (4 ^ 2) → ℂ))
  /-- Each parameter value is a fibre isogenous to the universal fibre at its period. -/
  isog : ∀ t (ht : t ∈ V), ∃ s, wtr_KIsog (fiber s) (F.univ ⟨period t, mapsTo ht⟩)
  /-- The embedding `K ⊂ ℂ`. -/
  ι : 𝕂 →+* ℂ
  /-- The sign `ε` of Lemma 8.2. -/
  ε : ℤ
  /-- It is a sign. -/
  ε_sign : ε = 1 ∨ ε = -1
  /-- The multiplicities `c_j` of Lemma 8.2. -/
  c : Fin 17 → ℕ
  /-- They are positive. -/
  c_pos : ∀ j, 0 < c j
  /-- The limit Hodge filtration `F¹₀`. -/
  F₀ : Submodule ℂ (Fin 4 ⊕ Fin 4 → ℂ)
  /-- It has dimension `4`. -/
  F₀_finrank : Module.finrank ℂ F₀ = 4
  /-- Cattani–Kaplan–Schmid: `F¹₀ ∩ W₀ = 0` for `W₀ = im (Σ_j M_j)`. -/
  hodgeTate : F₀ ⊓ LinearMap.range (Matrix.toLin' (∑ j, g34b_Mlog ι ε c j)) = ⊥
  /-- Points of `V` approaching the boundary. -/
  pt : ℕ → Fin 17 → ℂ
  /-- They lie in `V`. -/
  pt_mem : ∀ k, pt k ∈ V
  /-- A chart of the tangent space `Hom(F¹₀, V_ℂ / F¹₀)`. -/
  chart : (F₀ →ₗ[ℂ] (Fin 4 ⊕ Fin 4 → ℂ) ⧸ F₀) ≃ₗ[ℂ] (Fin (4 ^ 2) → ℂ)
  /-- The change of coordinates on the target. -/
  L : ℕ → Matrix (Fin (4 ^ 2)) (Fin (4 ^ 2)) ℂ
  /-- The change of coordinates on the source. -/
  R : ℕ → Matrix (Fin 17) (Fin 17) ℂ
  /-- `L k` is invertible. -/
  L_unit : ∀ k, IsUnit (L k)
  /-- `R k` is invertible. -/
  R_unit : ∀ k, IsUnit (R k)
  /-- The nilpotent orbit normal form, differentiated: the derivative converges to the tangent
  map. -/
  limit : Tendsto (fun k => L k * LinearMap.toMatrix'
      (fderiv ℂ period (pt k) : (Fin 17 → ℂ) →ₗ[ℂ] Fin (4 ^ 2) → ℂ) * R k) atTop
    (𝓝 (LinearMap.toMatrix' (chart.toLinearMap ∘ₗ g34b_tangentMap (g34b_Mlog ι ε c) F₀)))

/-- A boundary period map has a nonempty parameter set. -/
example (F : wtr_UniversalFamily 4 1) {S : Type} (fiber : S → wtr_Variety 4)
    (Φ : g34b_BoundaryPeriodMap F fiber) : Φ.V.Nonempty :=
  ⟨Φ.pt 0, Φ.pt_mem 0⟩

end Premises

end HodgeLean.Papers
