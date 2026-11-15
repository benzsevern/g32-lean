import HodgeLean.Foundations.Program.KernelFramesFamily
import HodgeLean.Foundations.Program.PathCoverFamily
import HodgeLean.Foundations.Program.PeriodBasisAlignment

/-! # B6-5 stage 5d, geometric part: the cover dictionary at the G32 centre (definitions)

The `s`-coordinate of the G32 path on the fibres of a `b65z_SharedFamily` at the centre
`b65z_centre p` (the inverse of the Möbius normalization of `b65p_mobius`), its differential `ds`,
the regular locus of a fibre over the path, the natural representation and its complex conjugate
on column vectors, the spaces `Hom_G(σ, H⁰(K_C))` of the fibres, the vectors of meromorphic forms
`Y⁻¹ r ds` and `Yᵀ q ds` attached to a fundamental solution `Y`, the contraction of two vectors
of forms, the quadratic differential `N(s) ds² / D_θ(s)` of a numerator, the record of pulled-back
fundamental solutions along the path, and the branch-point coordinate matrix of numerators.
No statement is asserted here. HC no distance; AV milestone no distance.
-/

noncomputable section
open Set Metric Matrix Filter Polynomial Manifold
open scoped Topology ContDiff
open HodgeLean.Papers
namespace HodgeLean.Foundations.Program
attribute [local instance] b4cov_sphChartedSpace b4cov_sph_isManifold
attribute [local instance] b65z_SharedFamily.topC b65z_SharedFamily.chartC
  b65z_SharedFamily.manC b65z_SharedFamily.t2C b65z_SharedFamily.compactC
  b65z_SharedFamily.connectedC b65z_SharedFamily.actionC b65z_SharedFamily.totalChart
  b65z_SharedFamily.totalMan b65z_SharedFamily.fibreChart b65z_SharedFamily.fibreMan
  b65z_SharedFamily.fibreT2 b65z_SharedFamily.fibreCompact b65z_SharedFamily.fibreConnected
  b65z_SharedFamily.fibreFaithful

/-- **The `s`-coordinate** of a point of the normalized sphere: the inverse of `b65p_mobius a b`,
`z ↦ ab/(b − z(b − a))`, with `∞ ↦ 0`. (The point `b/(b − a)`, the image of `s = ∞`, is sent
to the junk value `0` of the division; it is excluded from the regular locus below.)
Source: G32 v0.16, §3.1 (normalization modulo PGL₂) and §5.5 (the covers `C_θ` over the
`s`-line); `b65p_mobius`, `b65s_normalize`. -/
def b65g_sCoord (a b : ℂ) (w : OnePoint ℂ) : ℂ :=
  w.elim 0 (fun z ↦ a * b / (b - z * (b - a)))

/-- The `s`-coordinate inverts the normalization at every finite nonzero `s`. -/
example (a b s : ℂ) (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b) (hs : s ≠ 0) :
    b65g_sCoord a b (b65p_mobius a b (s : OnePoint ℂ)) = s := by
  have hba : b - a ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
  have hm : b65p_mobius a b (s : OnePoint ℂ) = ((b65s_normalize a b s : ℂ) : OnePoint ℂ) := by
    simp [b65p_mobius, hs]
  rw [hm]
  change a * b / (b - (s - a) * b / (s * (b - a)) * (b - a)) = s
  have h : b - (s - a) * b / (s * (b - a)) * (b - a) = a * b / s := by
    field_simp
    ring
  rw [h]
  field_simp

example (a b : ℂ) : b65g_sCoord a b OnePoint.infty = 0 := rfl

/-- **The `s`-function on a fibre**: the `s`-coordinate of the image of a point of the fibre over
`t` under the cover projection, for the normalization `b65p_mobius a b`.
Source: G32 v0.16, §5.5 (the covers `C_θ` over `ℙ¹_s`); `b63d_projection`. -/
def b65g_sFun {c : Fin 10 → ℂ} {g : Fin 13 → b4b_Group} (D : b65z_SharedFamily c g)
    (t : b6t_polydisc c) (a b : ℂ) : b65z_fibre c D.C t → ℂ :=
  fun x ↦ b65g_sCoord a b
    (b63d_projection c D.C D.atlas.f (b6t_polydisc c) (Subset.refl _) t x)

example {c : Fin 10 → ℂ} {g : Fin 13 → b4b_Group} (D : b65z_SharedFamily c g)
    (t : b6t_polydisc c) (a b : ℂ) (x : b65z_fibre c D.C t) :
    b65g_sFun D t a b x = b65g_sCoord a b
      (b63d_projection c D.C D.atlas.f (b6t_polydisc c) (Subset.refl _) t x) := rfl

/-- **The differential `ds`** on a fibre: the manifold derivative of the `s`-function.
Source: Forster, *Lectures on Riemann Surfaces*, §9 (the differential of a function); Mathlib
`mfderiv`. -/
def b65g_ds {c : Fin 10 → ℂ} {g : Fin 13 → b4b_Group} (D : b65z_SharedFamily c g)
    (t : b6t_polydisc c) (a b : ℂ) (u : TangentBundle 𝓘(ℂ, ℂ) (b65z_fibre c D.C t)) : ℂ :=
  mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (b65g_sFun D t a b) u.1 u.2

example {c : Fin 10 → ℂ} {g : Fin 13 → b4b_Group} (D : b65z_SharedFamily c g)
    (t : b6t_polydisc c) (a b : ℂ) (u : TangentBundle 𝓘(ℂ, ℂ) (b65z_fibre c D.C t)) :
    b65g_ds D t a b u = mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (b65g_sFun D t a b) u.1 u.2 := rfl

/-- **The regular locus** of a fibre for a pole configuration: points over a finite point `z`
of the sphere with `b − z(b − a) ≠ 0` (finite `s`) whose `s`-coordinate is none of the poles.
It omits the finitely many points over the branch points, the apparent poles and `s = ∞`.
Source: G32 v0.16, §5.3 (the complement of the poles `P`); `b65s_regular`. -/
def b65g_good {c : Fin 10 → ℂ} {g : Fin 13 → b4b_Group} (D : b65z_SharedFamily c g)
    (t : b6t_polydisc c) (a b : ℂ) (poles : Fin 4 ⊕ Fin 12 → ℂ) :
    Set (b65z_fibre c D.C t) :=
  {x | ∃ z : ℂ,
    b63d_projection c D.C D.atlas.f (b6t_polydisc c) (Subset.refl _) t x = (z : OnePoint ℂ) ∧
      b - z * (b - a) ≠ 0 ∧ b65g_sCoord a b (z : OnePoint ℂ) ∉ Set.range poles}

/-- Points over `∞` (the image of `s = 0`, a pole) are never regular. -/
example {c : Fin 10 → ℂ} {g : Fin 13 → b4b_Group} (D : b65z_SharedFamily c g)
    (t : b6t_polydisc c) (a b : ℂ) (poles : Fin 4 ⊕ Fin 12 → ℂ) (x : b65z_fibre c D.C t)
    (hx : b63d_projection c D.C D.atlas.f (b6t_polydisc c) (Subset.refl _) t x =
      OnePoint.infty) :
    x ∉ b65g_good D t a b poles := by
  rintro ⟨z, hz, -⟩
  rw [hx] at hz
  exact OnePoint.infty_ne_coe z hz

/-- **The natural matrices and their complex conjugates**: `b4b_toMatrix h`, or its entrywise
complex conjugate when `conj` is `true`.
Source: G32 v0.16, §3.3 and Appendix A (the matrices of `ρ`; `ρ̄` is the complex conjugate). -/
def b65g_mat (conj : Bool) (h : b4b_Group) : Matrix (Fin 4) (Fin 4) ℂ :=
  if conj then (b4b_toMatrix h).map (starRingEnd ℂ) else b4b_toMatrix h

example (h : b4b_Group) : b65g_mat false h = b4b_toMatrix h := rfl

/-- **`ρ` and `ρ̄` on column vectors**: `h ↦ b65g_mat conj h` acting on `Fin 4 → ℂ`. For
`conj = false` this is `b63d_naturalRep`.
Source: G32 v0.16, §3.3 (the natural representation `ρ` and its conjugate `ρ̄`); Serre, *Linear
Representations of Finite Groups*, §1.1. -/
def b65g_rep (conj : Bool) : Representation ℂ b4b_Group (Fin 4 → ℂ) where
  toFun h := Matrix.toLin' (b65g_mat conj h)
  map_one' := by
    cases conj <;> simp [b65g_mat, Matrix.toLin'_one] <;> rfl
  map_mul' g h := by
    cases conj
    · simp only [b65g_mat, map_mul, Matrix.toLin'_mul, Bool.false_eq_true, ite_false]; rfl
    · simp only [b65g_mat, ite_true, map_mul, Matrix.map_mul, Matrix.toLin'_mul]; rfl

example (h : b4b_Group) : b65g_rep false h = b63d_naturalRep h := rfl

/-- **The space `Hom_G(σ, H⁰(K_C))`** of the fibre over `t`, for `σ = b65g_rep conj`: the
`G`-maps from column vectors to holomorphic `1`-forms.
Source: G32 v0.16, §3.1 (`M_τ`, `Hom_G(τ, H⁰(C, K_C))`) and §5.1 (`𝒟_ρ(C)`, `𝒟_ρ̄(C)`);
`b4_HomG`, `b3_HolForm`, `b4_formAct`. -/
def b65g_homG {c : Fin 10 → ℂ} {g : Fin 13 → b4b_Group} (D : b65z_SharedFamily c g)
    (t : b6t_polydisc c) (conj : Bool) :
    Submodule ℂ ((Fin 4 → ℂ) →ₗ[ℂ] (TangentBundle 𝓘(ℂ, ℂ) (b65z_fibre c D.C t) → ℂ)) :=
  b4_HomG (b65g_rep conj) (fun h ↦ b4_formAct ℂ (C := b65z_fibre c D.C t) h)
    (b3_HolForm ℂ (b65z_fibre c D.C t))

example {c : Fin 10 → ℂ} {g : Fin 13 → b4b_Group} (D : b65z_SharedFamily c g)
    (t : b6t_polydisc c) (conj : Bool) : (0 : (Fin 4 → ℂ) →ₗ[ℂ]
      (TangentBundle 𝓘(ℂ, ℂ) (b65z_fibre c D.C t) → ℂ)) ∈ b65g_homG D t conj :=
  Submodule.zero_mem _

/-- **The r-forms** `v ⬝ (Y⁻¹ r ds)`: for a matrix function `Y` on the fibre and a rational vector
`r`, the function on the tangent bundle `(x, w) ↦ (v ⬝ Y(x)⁻¹ r(s(x))) · ds_x(w)`. It is
the formula of the dictionary; at the finitely many points off the regular locus its values
are not used.
Source: G32 v0.16, Lemma 5.3 (dictionary): `r ↦ Y⁻¹ r ds`. -/
def b65g_rForm {c : Fin 10 → ℂ} {g : Fin 13 → b4b_Group} (D : b65z_SharedFamily c g)
    (t : b6t_polydisc c) (a b : ℂ) (Y : b65z_fibre c D.C t → Matrix (Fin 4) (Fin 4) ℂ)
    (r : Fin 4 → RatFunc ℂ) (v : Fin 4 → ℂ) :
    TangentBundle 𝓘(ℂ, ℂ) (b65z_fibre c D.C t) → ℂ :=
  fun u ↦ (v ⬝ᵥ ((Y u.1)⁻¹ *ᵥ fun j ↦ b65q_eval (r j) (b65g_sFun D t a b u.1))) *
    b65g_ds D t a b u

/-- **The q-forms** `v ⬝ (Yᵀ q ds)`.
Source: G32 v0.16, Lemma 5.3 (dictionary): `q ↦ Yᵀ q ds`. -/
def b65g_qForm {c : Fin 10 → ℂ} {g : Fin 13 → b4b_Group} (D : b65z_SharedFamily c g)
    (t : b6t_polydisc c) (a b : ℂ) (Y : b65z_fibre c D.C t → Matrix (Fin 4) (Fin 4) ℂ)
    (q : Fin 4 → RatFunc ℂ) (v : Fin 4 → ℂ) :
    TangentBundle 𝓘(ℂ, ℂ) (b65z_fibre c D.C t) → ℂ :=
  fun u ↦ (v ⬝ᵥ ((Y u.1)ᵀ *ᵥ fun j ↦ b65q_eval (q j) (b65g_sFun D t a b u.1))) *
    b65g_ds D t a b u

example {c : Fin 10 → ℂ} {g : Fin 13 → b4b_Group} (D : b65z_SharedFamily c g)
    (t : b6t_polydisc c) (a b : ℂ) (Y : b65z_fibre c D.C t → Matrix (Fin 4) (Fin 4) ℂ)
    (v : Fin 4 → ℂ) : b65g_rForm D t a b Y 0 v = 0 ∧ b65g_qForm D t a b Y 0 v = 0 := by
  constructor <;> funext u <;>
    simp [b65g_rForm, b65g_qForm, b65q_eval, ← Pi.zero_def]

/-- **`φ` is represented by `r` on the regular locus**: `φ v` agrees with the r-form of `r`
at every tangent vector over a regular point.
Source: G32 v0.16, Lemma 5.3 (dictionary). -/
def b65g_rRepresents {c : Fin 10 → ℂ} {g : Fin 13 → b4b_Group} (D : b65z_SharedFamily c g)
    (t : b6t_polydisc c) (a b : ℂ) (poles : Fin 4 ⊕ Fin 12 → ℂ)
    (Y : b65z_fibre c D.C t → Matrix (Fin 4) (Fin 4) ℂ) (r : Fin 4 → RatFunc ℂ)
    (φ : (Fin 4 → ℂ) →ₗ[ℂ] (TangentBundle 𝓘(ℂ, ℂ) (b65z_fibre c D.C t) → ℂ)) : Prop :=
  ∀ v (u : TangentBundle 𝓘(ℂ, ℂ) (b65z_fibre c D.C t)), u.1 ∈ b65g_good D t a b poles →
    φ v u = b65g_rForm D t a b Y r v u

/-- **`ψ` is represented by `q` on the regular locus.**
Source: G32 v0.16, Lemma 5.3 (dictionary). -/
def b65g_qRepresents {c : Fin 10 → ℂ} {g : Fin 13 → b4b_Group} (D : b65z_SharedFamily c g)
    (t : b6t_polydisc c) (a b : ℂ) (poles : Fin 4 ⊕ Fin 12 → ℂ)
    (Y : b65z_fibre c D.C t → Matrix (Fin 4) (Fin 4) ℂ) (q : Fin 4 → RatFunc ℂ)
    (ψ : (Fin 4 → ℂ) →ₗ[ℂ] (TangentBundle 𝓘(ℂ, ℂ) (b65z_fibre c D.C t) → ℂ)) : Prop :=
  ∀ v (u : TangentBundle 𝓘(ℂ, ℂ) (b65z_fibre c D.C t)), u.1 ∈ b65g_good D t a b poles →
    ψ v u = b65g_qForm D t a b Y q v u

/-- The zero map is represented by the zero vector, for r and for q. -/
example {c : Fin 10 → ℂ} {g : Fin 13 → b4b_Group} (D : b65z_SharedFamily c g)
    (t : b6t_polydisc c) (a b : ℂ) (poles : Fin 4 ⊕ Fin 12 → ℂ)
    (Y : b65z_fibre c D.C t → Matrix (Fin 4) (Fin 4) ℂ) :
    b65g_rRepresents D t a b poles Y 0 0 ∧ b65g_qRepresents D t a b poles Y 0 0 := by
  constructor <;> intro v u _ <;>
    simp [b65g_rForm, b65g_qForm, b65q_eval, ← Pi.zero_def]

/-- **The contraction** of two vectors of forms against the invariant line of `ρ ⊗ ρ̄`:
`Σ_i φ(e_i) ψ(e_i)`, a function on the tangent bundle, quadratic on each tangent line.
Source: G32 v0.16, §5.1 (`μ_C`: multiplication of differentials followed by contraction of
`ρ ⊗ ρ̄` against its invariant line). -/
def b65g_contract {X : Type*} (φ ψ : (Fin 4 → ℂ) →ₗ[ℂ] (X → ℂ)) : X → ℂ :=
  fun u ↦ ∑ i : Fin 4, φ (Pi.single i 1) u * ψ (Pi.single i 1) u

example {X : Type*} (ψ : (Fin 4 → ℂ) →ₗ[ℂ] (X → ℂ)) : b65g_contract 0 ψ = 0 := by
  funext u; simp [b65g_contract]

/-- **The quadratic differential of a numerator**: `N(s) ds² / D_θ(s)` on the fibre, for the
coefficients `N 0, …, N 9` of `s⁰ … s⁹` and the branch polynomial `b65q_denominator poles`.
Source: G32 v0.16, Lemma 5.5 (numerators) and §5.5(7) (numerator coordinates). -/
def b65g_quadratic {c : Fin 10 → ℂ} {g : Fin 13 → b4b_Group} (D : b65z_SharedFamily c g)
    (t : b6t_polydisc c) (a b : ℂ) (poles : Fin 4 ⊕ Fin 12 → ℂ) (N : Fin 10 → ℂ) :
    TangentBundle 𝓘(ℂ, ℂ) (b65z_fibre c D.C t) → ℂ :=
  fun u ↦ b65q_eval ((∑ j : Fin 10, RatFunc.C (N j) * RatFunc.X ^ j.val) /
      algebraMap ℂ[X] (RatFunc ℂ) (b65q_denominator poles)) (b65g_sFun D t a b u.1) *
    b65g_ds D t a b u ^ 2

example {c : Fin 10 → ℂ} {g : Fin 13 → b4b_Group} (D : b65z_SharedFamily c g)
    (t : b6t_polydisc c) (a b : ℂ) (poles : Fin 4 ⊕ Fin 12 → ℂ) :
    b65g_quadratic D t a b poles 0 = 0 := by
  funext u; simp [b65g_quadratic, b65q_eval]

/-- **Pulled-back fundamental solutions along the path.** For a 5c record `O` and a family `D`
at the G32 centre: a radius, a choice `conj` of `ρ` or `ρ̄`, and for each parameter `θ` a
function `Y θ` on the total space, such that on the fibre over `b65p_curve p θ`, at every
regular point, `Y θ` is invertible, solves the Fuchsian system of `O` at `θ` in the
`s`-coordinate (`dY = A_θ(s) Y ds`, `A_θ = b65p_coefficient` along `b65p_poles p θ` with the
residues `O.residue θ`), and transforms under the deck group by `Y(h x) = Y(x) σ(h)ᵀ`,
`σ = b65g_rep conj`.
This is a record of outputs, not a premise: `b65g_cover_solutions` asserts that it is
inhabited for the identified family.
Source: G32 v0.16, proof of Lemma 5.3 ("pulled back to the complement of the ramification
points, `Y` is single-valued … `g*Y = Y ρ'(g)`"), §5.5 (The direction: for small `θ` the system
at `θ` is the `ρ`-local system of `C_θ`) and Lemma 5.6(2). -/
structure b65g_Solutions (p : Fin 12 → ℂ) (O : b65p_Outputs p) {g : Fin 13 → b4b_Group}
    (D : b65z_SharedFamily (b65z_centre p) g) where
  /-- The parameter radius. -/
  radius : ℝ
  /-- The radius is positive. -/
  radius_pos : 0 < radius
  /-- Inside the radius of the record. -/
  radius_le : radius ≤ O.radius
  /-- Whether the deck group acts through `ρ̄` rather than `ρ`. -/
  conj : Bool
  /-- The pulled-back fundamental solutions. -/
  Y : ℂ → b6t_polydisc (b65z_centre p) × D.C → (Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ)
  /-- Invertible at regular points. -/
  unit : ∀ θ ∈ ball (0 : ℂ) radius, ∀ t : b6t_polydisc (b65z_centre p),
    t.val = b65p_curve p θ → ∀ x ∈ b65g_good D t (b65p_moving p θ 10) (b65p_moving p θ 11)
      (b65p_poles p θ), IsUnit (Y θ x.val)
  /-- The Fuchsian system at `θ` in the `s`-coordinate. -/
  ode : ∀ θ ∈ ball (0 : ℂ) radius, ∀ t : b6t_polydisc (b65z_centre p),
    t.val = b65p_curve p θ → ∀ x ∈ b65g_good D t (b65p_moving p θ 10) (b65p_moving p θ 11)
      (b65p_poles p θ),
    MDifferentiableAt 𝓘(ℂ, ℂ) 𝓘(ℂ, (Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ))
      (fun y : b65z_fibre (b65z_centre p) D.C t ↦ Y θ y.val) x ∧
    ∀ w : TangentSpace 𝓘(ℂ, ℂ) x,
      (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, (Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ))
        (fun y : b65z_fibre (b65z_centre p) D.C t ↦ Y θ y.val) x w :
          (Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ)) =
        b65g_ds D t (b65p_moving p θ 10) (b65p_moving p θ 11) ⟨x, w⟩ •
          (b65p_coefficient (Fin 4 → ℂ) (b65p_poles p θ) (O.residue θ)
            (b65g_sFun D t (b65p_moving p θ 10) (b65p_moving p θ 11) x) * Y θ x.val)
  /-- The deck transformation law. -/
  equivariant : ∀ θ ∈ ball (0 : ℂ) radius, ∀ t : b6t_polydisc (b65z_centre p),
    t.val = b65p_curve p θ → ∀ x ∈ b65g_good D t (b65p_moving p θ 10) (b65p_moving p θ 11)
      (b65p_poles p θ), ∀ h : b4b_Group,
    Y θ (h • x).val = Y θ x.val * LinearMap.toContinuousLinearMap
      (Matrix.toLin' (b65g_mat conj h)ᵀ)

/-- The matrix function of a solution on the fibre over `t`.
Source: G32 v0.16, proof of Lemma 5.3; `b65g_Solutions.Y`, `b65q_mat`. -/
abbrev b65g_Y {p : Fin 12 → ℂ} {O : b65p_Outputs p} {g : Fin 13 → b4b_Group}
    {D : b65z_SharedFamily (b65z_centre p) g} (S : b65g_Solutions p O D) (θ : ℂ)
    (t : b6t_polydisc (b65z_centre p)) :
    b65z_fibre (b65z_centre p) D.C t → Matrix (Fin 4) (Fin 4) ℂ :=
  fun x ↦ b65q_mat (S.Y θ x.val)

example {p : Fin 12 → ℂ} {O : b65p_Outputs p} {g : Fin 13 → b4b_Group}
    {D : b65z_SharedFamily (b65z_centre p) g} (S : b65g_Solutions p O D) (θ : ℂ)
    (t : b6t_polydisc (b65z_centre p)) (x : b65z_fibre (b65z_centre p) D.C t) :
    b65g_Y S θ t x = b65q_mat (S.Y θ x.val) := rfl

/-- **The branch-point coordinate matrix** at `θ`: entry `(j, k)` is
`s_k^j / (D_θ'(s_k) · m_θ'(s_k))`, where `s_k = b65p_moving p θ k` (`k < 10`) are the branch
points carried by the ten chart coordinates and `m_θ = b65s_normalize a b` is the normalization
to the `z`-line. A numerator row `N` has branch-point coordinates `N ᵥ* V`: the residue at `s_k`
of `N(s) / (D_θ(s) m_θ'(s))`, i.e. the pairing of `N ds²/D_θ` with `∂/∂z_k`.
Source: G32 v0.16, §5.1 (the tangent space modulo `PGL₂` is Serre dual to
`H⁰(ℙ¹, K² (B_C))`) and Lemma 5.5; `docs/specs/NumeratorJet.md`, amendment (the right factor
`B θ` maps branch-point row coordinates to monomial coordinates). -/
def b65g_branchMatrix (p : Fin 12 → ℂ) (θ : ℂ) : Matrix (Fin 10) (Fin 10) ℂ := fun j k ↦
  b65p_moving p θ (Fin.castLE (by norm_num) k) ^ j.val /
    ((derivative (b65q_denominator (b65p_poles p θ))).eval
        (b65p_moving p θ (Fin.castLE (by norm_num) k)) *
      deriv (b65s_normalize (b65p_moving p θ 10) (b65p_moving p θ 11))
        (b65p_moving p θ (Fin.castLE (by norm_num) k)))

example (p : Fin 12 → ℂ) (θ : ℂ) (j k : Fin 10) :
    b65g_branchMatrix p θ j k =
      b65p_moving p θ (Fin.castLE (by norm_num) k) ^ j.val /
        ((derivative (b65q_denominator (b65p_poles p θ))).eval
          (b65p_moving p θ (Fin.castLE (by norm_num) k)) *
        deriv (b65s_normalize (b65p_moving p θ 10) (b65p_moving p θ 11))
          (b65p_moving p θ (Fin.castLE (by norm_num) k))) := rfl

/-- **The right factor `B θ`**: the inverse of the branch-point coordinate matrix, mapping
branch-point row coordinates to the coefficients of `s⁰ … s⁹`.
Source: `docs/specs/NumeratorJet.md`, amendment (`S_i(θ) j = Σ_k C_i(θ) k · B(θ) k j`). -/
def b65g_B (p : Fin 12 → ℂ) (θ : ℂ) : Matrix (Fin 10) (Fin 10) ℂ := (b65g_branchMatrix p θ)⁻¹

example (p : Fin 12 → ℂ) (θ : ℂ) : b65g_B p θ = (b65g_branchMatrix p θ)⁻¹ := rfl

/-- **The left factor `A θ`**: the ordered product change `K(c_F⁻¹, d_F⁻¹)` of the inverse
free-coordinate blocks of two coefficient triples.
Source: `docs/specs/NumeratorJet.md`, amendment (`A θ = K(c_F⁻¹, d_F⁻¹)`); `b66e_productChange`;
`b65k_rFree`, `b65k_qFree`. -/
def b65g_A (c : Matrix (Fin 36) (Fin 3) ℂ) (d : Matrix (Fin 48) (Fin 3) ℂ) :
    Matrix (Fin 9) (Fin 9) ℂ :=
  b66e_productChange (c.submatrix b65k_rFree id)⁻¹ (d.submatrix b65k_qFree id)⁻¹

example (c : Matrix (Fin 36) (Fin 3) ℂ) (d : Matrix (Fin 48) (Fin 3) ℂ) :
    b65g_A c d = b66e_productChange (c.submatrix b65k_rFree id)⁻¹
      (d.submatrix b65k_qFree id)⁻¹ := rfl

/-- Evaluation at the first coordinate gives a nonzero contraction. -/
example : b65g_contract
    ((LinearMap.pi fun _ : Unit ↦ LinearMap.proj (0 : Fin 4)))
    ((LinearMap.pi fun _ : Unit ↦ LinearMap.proj (0 : Fin 4))) () = 1 := by
  norm_num [b65g_contract, Fin.sum_univ_succ, Pi.single_apply]

/-- Constant numerator one at `s = 1`, `ds = 1`, with all poles zero. -/
example {c : Fin 10 → ℂ} {g : Fin 13 → b4b_Group} (D : b65z_SharedFamily c g)
    (t : b6t_polydisc c) (a b : ℂ)
    (u : TangentBundle 𝓘(ℂ, ℂ) (b65z_fibre c D.C t))
    (hs : b65g_sFun D t a b u.1 = 1) (hd : b65g_ds D t a b u = 1) :
    b65g_quadratic D t a b (fun _ ↦ 0) (Pi.single 0 1) u = 1 := by
  simp only [b65g_quadratic, hs, hd, one_pow, mul_one]
  have hn : (∑ j : Fin 10, RatFunc.C ((Pi.single 0 1 : Fin 10 → ℂ) j) *
      RatFunc.X ^ j.val) = (1 : RatFunc ℂ) := by simp [Pi.single_apply]
  rw [hn]
  rw [← map_one (algebraMap ℂ[X] (RatFunc ℂ))]
  change RatFunc.eval (RingHom.id ℂ) 1
    (algebraMap ℂ[X] (RatFunc ℂ) 1 /
      algebraMap ℂ[X] (RatFunc ℂ) (b65q_denominator (fun _ ↦ 0))) = 1
  have hp : b65q_denominator (fun _ ↦ (0 : ℂ)) = (X : ℂ[X]) ^ 13 := by
    simp [b65q_denominator, pow_succ, mul_comm]
  rw [hp, RatFunc.eval, RatFunc.num_div, RatFunc.denom_div 1 (pow_ne_zero 13 X_ne_zero)]
  norm_num

end HodgeLean.Foundations.Program
