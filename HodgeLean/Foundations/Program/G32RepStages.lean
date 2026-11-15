import HodgeLean.Foundations.Program.G32RepStagesProofs

/-!
# The first G32 representation stages (FROZEN SPEC)

Stages A–D of `docs/specs/RepFoundations.md`, eight statements about a realized cover
`X : g32p_Cover A` of a G32 sixfold, with `G₃₂` acting on `ℂ ⊗ H¹(J; ℚ)` by `g32rep_rep X`:

* stage A: the multiplicity spaces `g32c_mult` and characters `g32c_char` of the contraction
  are the general ones, `rfd_mult` and `rfd_det`, of this representation;
* stage B: the complexified polarization form `g32rep_form X` is nondegenerate, alternating,
  `G₃₂`-invariant and preserved by every element of `g32c_U X`;
* stage C: Chevalley–Weil vanishing, `M_σ = 0` for a nontrivial simple `σ` with `m_σ ≤ 0`;
* stage D: the form types, `ν(θ) = -1` and `e_θ² = 1` for quaternionic `θ`, `e_τ̄ · e_τ = 1` for
  the pairs of an enumeration, and `e_σ = 1` for self-dual non-quaternionic `σ`.

These are implications from the fields of `g32p_Cover` (`X.aut_mul`, `X.mult`, `X.pol_nondeg`,
`X.pol_inv`) and the general foundations `rfd_mult_eq_bot`, `rfd_det_mul_dual`,
`rfd_det_orthogonal`, `rfd_indicator_trichotomy`. Nothing here asserts that a `g32p_Cover` exists,
an algebraicity, a character comparison, or any of the three set-aside contraction statements;
stages E–H and their restoration are listed in `docs/specs/G32RepStages.md`.
HC no distance; AV milestone no distance.
-/

noncomputable section
set_option maxHeartbeats 400000

open scoped TensorProduct CategoryTheory.MonObj
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Papers HodgeLean.Foundations

namespace HodgeLean.Foundations.Program

variable {A : g32t_Sixfold}

/-! ## Stage A: the action as a representation -/

/-- **The contraction's multiplicity spaces are the general ones.** `g32c_mult X τ` is
`rfd_mult τ (g32rep_rep X)`, `Hom_G(τ, ℂ ⊗ H¹(J))` for the representation `g ↦ (aut g)^*`.
Source: G32 v0.16, Subsection 4.2 (`H¹(C, ℂ) = ⊕_τ τ ⊗ M_τ`); `g32c_mult`, `rfd_mult`,
`g32rep_rep`. -/
theorem g32rep_mult_eq (X : g32p_Cover A) (τ : FDRep ℂ g32p_G) :
    g32c_mult X τ = rfd_mult τ (g32rep_rep X) :=
  g32rep_mult_eq_aux X τ

/-- The two multiplicity spaces vanish together. -/
example (X : g32p_Cover A) (τ : FDRep ℂ g32p_G) :
    g32c_mult X τ = ⊥ ↔ rfd_mult τ (g32rep_rep X) = ⊥ := by
  rw [g32rep_mult_eq X τ]

/-- **The contraction's characters are the general ones.** For `u ∈ U`,
`e_τ(u) = det(u | M_τ)` computed in `g32c_char` equals `rfd_det τ (g32rep_rep X) u`.
Source: G32 v0.16, Subsection 4.2 (the characters `e_τ` of `U`); `g32c_char`, `rfd_det`,
`g32rep_U_le`. -/
theorem g32rep_char_eq (X : g32p_Cover A) (τ : FDRep ℂ g32p_G)
    (u : Module.End ℂ (ℂ ⊗[ℚ] HQ X.J 1)) (hu : u ∈ g32c_U X) :
    g32c_char X τ u hu = rfd_det τ (g32rep_rep X) u (g32rep_U_le X hu) :=
  g32rep_char_eq_aux X τ u hu

/-- A general value of `rfd_det` transfers to `g32c_char`. -/
example (X : g32p_Cover A) (τ : FDRep ℂ g32p_G)
    (u : Module.End ℂ (ℂ ⊗[ℚ] HQ X.J 1)) (hu : u ∈ g32c_U X)
    (h : rfd_det τ (g32rep_rep X) u (g32rep_U_le X hu) = 1) :
    g32c_char X τ u hu = 1 := by
  rw [g32rep_char_eq X τ u hu, h]

/-! ## Stage B: the polarization form -/

/-- **The polarization form.** `g32rep_form X` is nondegenerate (from `X.pol_nondeg`), alternating,
invariant under `g32rep_rep X` (from `X.pol_inv`) and preserved by every `u ∈ U` (which fixes the
polarization 2-vector and is invertible).
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., Ch. 4 (the Riemann form of an
invariant polarization); G32 v0.16, Subsection 4.2 (`U` in the symplectic group of
`(H¹(C, ℚ), E)`); `polarizationForm`, `nondegenerate_polarizationForm`,
`isAlt_polarizationForm`, `spec_homPullback_cupWedgeMap`. -/
theorem g32rep_form_spec (X : g32p_Cover A) :
    (g32rep_form X).Nondegenerate ∧ (g32rep_form X).IsAlt ∧
      (∀ g x y, g32rep_form X (g32rep_rep X g x) (g32rep_rep X g y) = g32rep_form X x y) ∧
      ∀ u ∈ g32c_U X, ∀ x y, g32rep_form X (u x) (u y) = g32rep_form X x y :=
  g32rep_form_spec_aux X

/-- The form vanishes on the diagonal. -/
example (X : g32p_Cover A) (x : ℂ ⊗[ℚ] HQ X.J 1) : g32rep_form X x x = 0 :=
  (g32rep_form_spec X).2.1 x

/-! ## Stage C: Chevalley–Weil vanishing -/

/-- **Vanishing multiplicities.** For a nontrivial simple `σ` with Chevalley–Weil multiplicity
`m_σ ≤ 0`, the multiplicity space `M_σ` is zero: `X.mult` gives `g32p_multiplicity = m_σ`, the
rational trace of `(aut g)^*` is the complex trace of its base change, and `rfd_mult_eq_bot`
applies.
Source: G32 v0.16, Proposition 3.1; Serre, *Linear representations of finite groups*, §2.3,
Theorem 3; `X.mult`, `rfd_mult_eq_bot`, Mathlib `LinearMap.trace_baseChange`. -/
theorem g32rep_mult_eq_bot (X : g32p_Cover A) (σ : FDRep ℂ g32p_G) (hσ : Simple σ)
    (hnt : ∃ g, σ.ρ g ≠ 1) (hcw : g32p_cwMult σ ≤ 0) :
    g32c_mult X σ = ⊥ :=
  g32rep_mult_eq_bot_aux X σ hσ hnt hcw

/-- With a vanishing multiplicity space, `e_σ = 1`. -/
example (X : g32p_Cover A) (σ : FDRep ℂ g32p_G) (hσ : Simple σ)
    (hnt : ∃ g, σ.ρ g ≠ 1) (hcw : g32p_cwMult σ ≤ 0)
    (u : Module.End ℂ (ℂ ⊗[ℚ] HQ X.J 1)) (hu : u ∈ g32c_U X) :
    g32c_char X σ u hu = 1 := by
  have h := g32rep_mult_eq_bot X σ hσ hnt hcw
  have : Subsingleton (g32c_mult X σ) := by
    rw [h]
    infer_instance
  exact LinearMap.det_eq_one_of_subsingleton _

/-! ## Stage D: form types for the enumeration -/

/-- **Quaternionic representations have indicator `-1`.** `g32p_Quaternionic θ` records
`Σ_g χ_θ(g²) = -|G|`; dividing by `|G|` gives `rfd_indicator θ = -1`.
Source: Serre, *Linear representations of finite groups*, §13.2, Proposition 39;
`g32p_Quaternionic`, `rfd_indicator`. -/
theorem g32rep_quaternionic_indicator (θ : FDRep ℂ g32p_G) (h : g32p_Quaternionic θ) :
    rfd_indicator θ = -1 :=
  g32rep_quaternionic_indicator_aux θ h

/-- A quaternionic representation is not of orthogonal type. -/
example (θ : FDRep ℂ g32p_G) (h : g32p_Quaternionic θ) : rfd_indicator θ ≠ 1 := by
  rw [g32rep_quaternionic_indicator θ h]
  norm_num

/-- **Quaternionic parity.** For a quaternionic simple `θ` and `u ∈ U`, `e_θ(u)² = 1`: the
instance `σ̄ = σ = θ` of `rfd_det_mul_dual` for the form of stage B, through stage A.
Source: G32 v0.16, Subsection 4.2 (factors `O(M_θ)` of `U`); `rfd_det_mul_dual`,
`g32rep_form_spec`, `g32rep_char_eq`. -/
theorem g32rep_parity (X : g32p_Cover A) (θ : FDRep ℂ g32p_G) (hθ : Simple θ)
    (h : g32p_Quaternionic θ) (u : Module.End ℂ (ℂ ⊗[ℚ] HQ X.J 1)) (hu : u ∈ g32c_U X) :
    g32c_char X θ u hu ^ 2 = 1 :=
  g32rep_parity_aux X θ hθ h u hu

/-- `e_θ(u)` is a sign. -/
example (X : g32p_Cover A) (θ : FDRep ℂ g32p_G) (hθ : Simple θ)
    (h : g32p_Quaternionic θ) (u : Module.End ℂ (ℂ ⊗[ℚ] HQ X.J 1)) (hu : u ∈ g32c_U X) :
    g32c_char X θ u hu = 1 ∨ g32c_char X θ u hu = -1 :=
  sq_eq_one_iff.mp (g32rep_parity X θ hθ h u hu)

/-- **Dual pairs.** For an enumeration `(τ, τ̄, θ)` and `u ∈ U`, `e_τ̄ⱼ(u) · e_τⱼ(u) = 1`:
`rfd_det_mul_dual` for the form of stage B, with the conjugate-character clause of
`g32c_Enumeration`.
Source: G32 v0.16, Subsection 4.2 (`M_τ̄` dual to `M_τ`, factors `GL(M_τ)` of `U`);
`rfd_det_mul_dual`, `g32rep_form_spec`, `g32rep_char_eq`, `g32c_Enumeration`. -/
theorem g32rep_conj (X : g32p_Cover A) {I K : Type*} (τ τbar : I → FDRep ℂ g32p_G)
    (θ : K → FDRep ℂ g32p_G) (hE : g32c_Enumeration τ τbar θ) (j : I)
    (u : Module.End ℂ (ℂ ⊗[ℚ] HQ X.J 1)) (hu : u ∈ g32c_U X) :
    g32c_char X (τbar j) u hu * g32c_char X (τ j) u hu = 1 :=
  g32rep_conj_aux X τ τbar θ hE j u hu

/-- The character `e_τⱼ` does not vanish on `U`. -/
example (X : g32p_Cover A) {I K : Type*} (τ τbar : I → FDRep ℂ g32p_G)
    (θ : K → FDRep ℂ g32p_G) (hE : g32c_Enumeration τ τbar θ) (j : I)
    (u : Module.End ℂ (ℂ ⊗[ℚ] HQ X.J 1)) (hu : u ∈ g32c_U X) :
    g32c_char X (τ j) u hu ≠ 0 :=
  right_ne_zero_of_mul_eq_one (g32rep_conj X τ τbar θ hE j u hu)

/-- **Orthogonal type.** For a self-dual, non-quaternionic simple `σ` and `u ∈ U`,
`e_σ(u) = 1`: the indicator is `1` (`rfd_indicator_trichotomy`), and `rfd_det_orthogonal`
applies to the alternating form of stage B.
Source: G32 v0.16, Subsection 4.2 (factors `Sp(M_σ)` of `U`); `rfd_indicator_trichotomy`,
`rfd_det_orthogonal`, `g32rep_form_spec`, `g32rep_char_eq`. -/
theorem g32rep_orthogonal (X : g32p_Cover A) (σ : FDRep ℂ g32p_G) (hσ : Simple σ)
    (hsd : g32p_SelfDual σ) (hq : ¬ g32p_Quaternionic σ)
    (u : Module.End ℂ (ℂ ⊗[ℚ] HQ X.J 1)) (hu : u ∈ g32c_U X) :
    g32c_char X σ u hu = 1 :=
  g32rep_orthogonal_aux X σ hσ hsd hq u hu

/-- Every power of `e_σ(u)` is `1` for orthogonal `σ`. -/
example (X : g32p_Cover A) (σ : FDRep ℂ g32p_G) (hσ : Simple σ)
    (hsd : g32p_SelfDual σ) (hq : ¬ g32p_Quaternionic σ)
    (u : Module.End ℂ (ℂ ⊗[ℚ] HQ X.J 1)) (hu : u ∈ g32c_U X) (k : ℕ) :
    g32c_char X σ u hu ^ k = 1 := by
  rw [g32rep_orthogonal X σ hσ hsd hq u hu, one_pow]

end HodgeLean.Foundations.Program
