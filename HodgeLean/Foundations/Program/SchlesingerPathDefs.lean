import HodgeLean.Foundations.Program.BraidCertificateDefs
import HodgeLean.Foundations.Program.HurwitzTransportDefs

/-! # B6-5 stage 5c: Schlesinger data and the normalized path (definitions)

Indexed Fuchsian coefficients, the Schlesinger right-hand side, the sixteen poles of the
pullback system moving along the direction of G32 Proposition 5.9, their residues at the base
cover, the fixed-pole exponents, the Möbius normalization sending three branch points to
`0, 1, ∞`, and the resulting path in the normalized chart. The record of stage 5c outputs
consumed by stage 5d is at the end. No statement is asserted here.
HC no distance; AV milestone no distance.
-/

noncomputable section
open Set Metric Filter
open scoped Topology
namespace HodgeLean.Foundations.Program

/-- The Fuchsian coefficient `s ↦ Σ_q (s − t_q)⁻¹ A_q` with indexed poles and residues.
Source: G32 v0.16, §5.4, Ω = Σ_q A_q ds/(s − t_q); Jimbo–Miwa–Ueno, Physica D 2 (1981), §2. -/
def b65p_coefficient (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E]
    {ι : Type*} [Fintype ι] (t : ι → ℂ) (A : ι → E →L[ℂ] E) (s : ℂ) : E →L[ℂ] E :=
  ∑ q, (s - t q)⁻¹ • A q

example : b65p_coefficient ℂ (fun _ : Fin 1 ↦ (0 : ℂ)) (fun _ ↦ 1) 1 = 1 := by
  simp [b65p_coefficient]

/-- The part of the coefficient that is regular at the pole `t_p`: the sum over `q ≠ p`.
Source: G32 v0.16, §5.3, the Taylor coefficients of Σ_{q≠p} A_q/(s − q) in the local recursion. -/
def b65p_regularPart (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (t : ι → ℂ) (A : ι → E →L[ℂ] E) (p : ι)
    (s : ℂ) : E →L[ℂ] E :=
  ∑ q, if q = p then 0 else (s - t q)⁻¹ • A q

example (t : Fin 1 → ℂ) (A : Fin 1 → ℂ →L[ℂ] ℂ) (s : ℂ) :
    b65p_regularPart ℂ t A 0 s = 0 := by
  simp [b65p_regularPart]

/-- The right-hand side of the Schlesinger equations at the pole `p`, for pole positions `t`
and pole velocities `v`: `Σ_{q≠p} [A_q, A_p] (v_p − v_q)/(t_p − t_q)`, the logarithmic
derivative of `t_p − t_q` written with the velocities.
Source: Schlesinger, J. reine angew. Math. 141 (1912); Jimbo–Miwa–Ueno, Physica D 2 (1981),
§2; G32 v0.16, §5.4, equation (Schlesinger). -/
def b65p_schlesingerField (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (v t : ι → ℂ) (A : ι → E →L[ℂ] E) (p : ι) :
    E →L[ℂ] E :=
  ∑ q, if q = p then 0 else ((v p - v q) / (t p - t q)) • (A q * A p - A p * A q)

example (v t : Fin 1 → ℂ) (A : Fin 1 → ℂ →L[ℂ] ℂ) :
    b65p_schlesingerField ℂ v t A 0 = 0 := by
  simp [b65p_schlesingerField]

/-- Commuting residues give a vanishing Schlesinger field, so constant commuting residues
solve the equations along any distinct moving poles.
Source: the definition of `b65p_schlesingerField`. -/
example (v t : Fin 2 → ℂ) (c : Fin 2 → ℂ) (p : Fin 2) :
    b65p_schlesingerField (Fin 4 → ℂ) v t (fun q ↦ c q • (1 : (Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ)))
      p = 0 := by
  simp [b65p_schlesingerField, smul_smul, mul_comm]

/-- **Non-degeneracy.** For noncommuting residues the field is not zero: the elementary
matrices `E₀₁` and `E₁₀` at the poles `0` and `1`, both moving with velocities `0` and `1`. -/
example : b65p_schlesingerField (Fin 2 → ℂ) ![0, 1] ![0, 1]
    ![b65r_operator (Matrix.single 0 1 1), b65r_operator (Matrix.single 1 0 1)] 0 ≠ 0 := by
  intro h
  have h' := congrArg (fun f : (Fin 2 → ℂ) →L[ℂ] (Fin 2 → ℂ) ↦ f (Pi.single 0 1) 0) h
  simp [b65p_schlesingerField, b65r_operator, Fin.sum_univ_succ] at h'

/-- The four fixed poles of the pullback system: the branch point `0` and the apparent
singularities `3, 1, −2`, in the order of G32 v0.16, §5.5(4).
Source: G32 v0.16, §5.5, "keeping s = 0 and the three apparent singularities fixed". -/
def b65p_fixedPole : Fin 4 → ℂ := ![0, 3, 1, -2]

example : b65p_fixedPole 1 = 3 := rfl

/-- The fibre (`5` or `−7`) of each of the twelve reflection poles, in the final-label order of
the braid certificate (`b65b_boxIndex`, `b65b_boxFibre`).
Source: B65-BRAIDCERT JSON, boxes; G32 v0.16, §5.2, P₅ and P₋₇. -/
def b65p_fibre : Fin 12 → ℤ := ![-7, 5, -7, 5, -7, 5, 5, -7, -7, 5, 5, -7]

example : ∀ k : Fin 12, b65p_fibre (b65b_boxIndex k) = b65b_boxFibre k := by decide

/-- The velocity polynomial `V₅` of the direction of the rank certificate.
Source: G32 v0.16, Proposition 5.9 (prop:rank). -/
def b65p_V5 (s : ℂ) : ℂ :=
  -3/7 * s^5 + 3/7 * s^4 + 3/7 * s^3 + 3/7 * s^2 + 1/7 * s - 2/7

example : b65p_V5 0 = -2/7 := by norm_num [b65p_V5]

/-- The velocity polynomial `V₋₇` of the direction of the rank certificate.
Source: G32 v0.16, Proposition 5.9 (prop:rank). -/
def b65p_Vneg7 (s : ℂ) : ℂ := 3/7 * s^3 - 3/7 * s - 1/7

example : b65p_Vneg7 0 = -1/7 := by norm_num [b65p_Vneg7]

/-- The velocity polynomial attached to a fibre: `V₅` over `5` and `V₋₇` otherwise.
Source: G32 v0.16, §5.5, "move each root t of P₅ to t + θV₅(t)". -/
def b65p_V (e : ℤ) (s : ℂ) : ℂ := if e = 5 then b65p_V5 s else b65p_Vneg7 s

example (s : ℂ) : b65p_V 5 s = b65p_V5 s := by simp [b65p_V]

/-- The sixteen poles at parameter `θ`: the fixed poles, then each reflection pole `p j` moved
to `p j + θ V(p j)`.
Source: G32 v0.16, §5.5, "The direction". -/
def b65p_poles (p : Fin 12 → ℂ) (θ : ℂ) : Fin 4 ⊕ Fin 12 → ℂ :=
  Sum.elim b65p_fixedPole (fun j ↦ p j + θ * b65p_V (b65p_fibre j) (p j))

example (p : Fin 12 → ℂ) (j : Fin 12) : b65p_poles p 0 (Sum.inr j) = p j := by
  simp [b65p_poles]

/-- The velocities of the sixteen poles: zero at the fixed poles, `V(p j)` at the moving ones.
Source: G32 v0.16, §5.5, "The direction". -/
def b65p_velocity (p : Fin 12 → ℂ) : Fin 4 ⊕ Fin 12 → ℂ :=
  Sum.elim 0 (fun j ↦ b65p_V (b65p_fibre j) (p j))

example (p : Fin 12 → ℂ) (q : Fin 4 ⊕ Fin 12) (θ : ℂ) :
    HasDerivAt (fun θ ↦ b65p_poles p θ q) (b65p_velocity p q) θ := by
  rcases q with k | j
  · simpa [b65p_poles, b65p_velocity] using hasDerivAt_const θ (b65p_fixedPole k)
  · simpa [b65p_poles, b65p_velocity] using
      ((hasDerivAt_id θ).mul_const (b65p_V (b65p_fibre j) (p j))).const_add (p j)

/-- **Non-degeneracy.** The reflection poles move: at `p = 0` the pole with label 10 (over `5`)
moves to `V₅(0) = −2/7` at `θ = 1`. -/
example : b65p_poles 0 1 (Sum.inr 10) ≠ b65p_poles 0 0 (Sum.inr 10) := by
  norm_num [b65p_poles, b65p_fibre, b65p_V, b65p_V5]

/-- The residues of the pullback system at the fixed poles: `2B₀` at `0`, `4B₀` at `3`, and
`3B_∞` at `1` and `−2`.
Source: G32 v0.16, §5.5 (subsec:certificate), first paragraph. -/
def b65p_fixedResidue : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ :=
  ![(2 : ℂ) • b65r_B0, (4 : ℂ) • b65r_B0, (3 : ℂ) • b65r_Binf, (3 : ℂ) • b65r_Binf]

example : b65p_fixedResidue 0 = (2 : ℂ) • b65r_B0 := rfl

/-- The residues at the reflection poles: `B₅` over `5` and `B₋₇` over `−7`.
Source: G32 v0.16, §5.5, "residues equal to B₅ at the roots of P₅ and to B₋₇ at the roots of
P₋₇". -/
def b65p_movingResidue (j : Fin 12) : Matrix (Fin 4) (Fin 4) ℂ :=
  if b65p_fibre j = 5 then b65r_B5 else b65r_Bneg7

example : b65p_movingResidue 10 = b65r_B5 := by simp [b65p_movingResidue, b65p_fibre]

/-- The sixteen residues of the base system on `ℂ⁴`, in the pole order of `b65p_poles`.
Source: G32 v0.16, §5.5, first paragraph; `b65r_operator`. -/
def b65p_initialResidue : Fin 4 ⊕ Fin 12 → (Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ) :=
  Sum.elim (fun k ↦ b65r_operator (b65p_fixedResidue k))
    (fun j ↦ b65r_operator (b65p_movingResidue j))

example : b65p_initialResidue (Sum.inr 0) = b65r_operator b65r_Bneg7 := by
  simp [b65p_initialResidue, b65p_movingResidue, b65p_fibre]

/-- **Consistency.** The sixteen base residues sum to zero, so `∞` is a regular point of the
base system: `2B₀ + 4B₀ + 6B_∞ + 6B₅ + 6B₋₇ = 0`. -/
example : ∑ q, b65p_initialResidue q = 0 := by
  have key : ∑ k, b65p_fixedResidue k + ∑ j, b65p_movingResidue j = 0 := by
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, b65p_fixedResidue, b65p_movingResidue,
      b65p_fibre]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_succ]
    norm_num [b65r_Binf]
    module
  have hsum : ∀ {n : Type} [Fintype n] (f : n → Matrix (Fin 4) (Fin 4) ℂ),
      b65r_operator (∑ j, f j) = ∑ j, b65r_operator (f j) := by
    intro n _ f; ext v i; simp [b65r_operator]
  have h := congrArg b65r_operator key
  rw [show b65r_operator (0 : Matrix (Fin 4) (Fin 4) ℂ) = 0 by ext v i; simp [b65r_operator]] at h
  rw [← h, Fintype.sum_sum_type]
  simp only [b65p_initialResidue, Sum.elim_inl, Sum.elim_inr]
  rw [← hsum, ← hsum]
  ext v i; simp [b65r_operator]

/-- **Non-degeneracy.** The residue at a reflection pole is not zero. -/
example : b65p_initialResidue (Sum.inr 10) ≠ 0 := by
  intro h
  have h' := congrArg (fun f : (Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ) ↦ f (Pi.single 2 1) 0) h
  have h10 : b65p_initialResidue (Sum.inr 10) = b65r_operator b65r_B5 := by
    simp [b65p_initialResidue, b65p_movingResidue, b65p_fibre]
  rw [h10] at h'
  change (Matrix.mulVec b65r_B5 (Pi.single 2 1)) 0 = (0 : (Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ)) (Pi.single 2 1) 0 at h'
  rw [Matrix.mulVec_single_one] at h'
  norm_num [b65r_B5] at h'

/-- The exponents at the fixed poles, in increasing order: `(−3/2, −1, −1, 3/2)` at `0`,
`(−3, −2, −2, 3)` at `3` and `(−2, −2, 2, 2)` at `1` and `−2`.
Source: G32 v0.16, §5.5, first paragraph; §5.3, the local form Y_p = P_p H_p (s − p)^Λ_p. -/
def b65p_exponents : Fin 4 → Fin 4 → ℂ :=
  ![![-3/2, -1, -1, 3/2], ![-3, -2, -2, 3], ![-2, -2, 2, 2], ![-2, -2, 2, 2]]

example : b65p_exponents 1 3 = 3 := rfl

/-- The diagonal exponent operator `Λ_p` at a fixed pole.
Source: G32 v0.16, §5.3, Λ_p = diag(λ_{p,1}, …, λ_{p,4}). -/
def b65p_exponent (k : Fin 4) : (Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ) :=
  b65r_operator (Matrix.diagonal (b65p_exponents k))

/-- **Satisfiability of the eigenbasis condition.** At `0` the residue `2B₀` is already the
diagonal exponent operator, so the identity is an eigenbasis in the increasing order. -/
example : b65p_initialResidue (Sum.inl 0) * 1 = 1 * b65p_exponent 0 := by
  rw [mul_one, one_mul]
  simp only [b65p_initialResidue, Sum.elim_inl, b65p_fixedResidue, b65p_exponent,
    b65p_exponents, b65r_B0]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [Matrix.diagonal]

/-- The same at `3`, where the residue is `4B₀`. -/
example : b65p_initialResidue (Sum.inl 1) * 1 = 1 * b65p_exponent 1 := by
  rw [mul_one, one_mul]
  simp only [b65p_initialResidue, Sum.elim_inl, b65p_fixedResidue, b65p_exponent,
    b65p_exponents, b65r_B0]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [Matrix.diagonal]

/-- **Non-degeneracy.** The exponent operator at `0` is not zero (rank four, nonzero exponent). -/
example : b65p_exponent 0 ≠ 0 := by
  intro h
  have h' := congrArg (fun f : (Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ) ↦ f (Pi.single 0 1) 0) h
  norm_num [b65p_exponent, b65p_exponents, b65r_operator, Matrix.mulVec, dotProduct,
    Fin.sum_univ_succ, Matrix.diagonal] at h'

/-- The twelve moving reflection poles at parameter `θ`.
Source: `b65p_poles`. -/
def b65p_moving (p : Fin 12 → ℂ) (θ : ℂ) : Fin 12 → ℂ := fun j ↦ b65p_poles p θ (Sum.inr j)

example (p : Fin 12 → ℂ) : b65p_moving p 0 = p := by
  funext j
  simp [b65p_moving, b65p_poles]

/-- The ten normalized chart coordinates of a configuration of twelve finite branch points and
the branch point `0`: the Möbius map sending `q 10 ↦ 0`, `q 11 ↦ 1`, `0 ↦ ∞`, applied to the
remaining ten points.
Source: G32 v0.16, §3.1, normalization modulo PGL₂; `b65s_normalize`, `b65b_configuration`. -/
def b65p_chartPoint (q : Fin 12 → ℂ) : Fin 10 → ℂ :=
  fun i ↦ b65s_normalize (q 10) (q 11) (q (Fin.castLE (by norm_num) i))

example (q : Fin 12 → ℂ) (i : Fin 10) :
    b65p_chartPoint q i = b65s_normalize (q 10) (q 11) (q (Fin.castLE (by norm_num) i)) := rfl

/-- The normalized Schlesinger path in the chart: `θ ↦` the normalized configuration of the
thirteen branch points at `θ`.
Source: G32 v0.16, §5.5, the covers C_θ; `g32r_PeriodMap.curve`. -/
def b65p_curve (p : Fin 12 → ℂ) (θ : ℂ) : Fin 10 → ℂ := b65p_chartPoint (b65p_moving p θ)

example (p : Fin 12 → ℂ) : b65p_curve p 0 = b65p_chartPoint p := by
  simp only [b65p_curve]
  congr 1
  funext j
  simp [b65p_moving, b65p_poles]

/-- The thirteen branch points at `θ` before normalization, in the order matched with
`b6_branch`: the ten moving points, then the points sent to `0` and `1`, then `0`.
Source: `b6_branch`; G32 v0.16, §5.5. -/
def b65p_source (p : Fin 12 → ℂ) (θ : ℂ) : Fin 13 → OnePoint ℂ :=
  Fin.append (fun i : Fin 10 ↦ ((b65p_moving p θ (Fin.castLE (by norm_num) i) : ℂ) : OnePoint ℂ))
    ![((b65p_moving p θ 10 : ℂ) : OnePoint ℂ), ((b65p_moving p θ 11 : ℂ) : OnePoint ℂ),
      ((0 : ℂ) : OnePoint ℂ)]

example (p : Fin 12 → ℂ) (θ : ℂ) : b65p_source p θ 12 = ((0 : ℂ) : OnePoint ℂ) := rfl

/-- The extension of `b65s_normalize a b` to the sphere: `0 ↦ ∞` and `∞ ↦ b/(b − a)`.
Source: G32 v0.16, §3.1; the Möbius map z ↦ (z − a)b/(z(b − a)). -/
def b65p_mobius (a b : ℂ) (w : OnePoint ℂ) : OnePoint ℂ :=
  w.elim ((b / (b - a) : ℂ) : OnePoint ℂ)
    (fun z ↦ if z = 0 then OnePoint.infty else ((b65s_normalize a b z : ℂ) : OnePoint ℂ))

example (a b : ℂ) : b65p_mobius a b ((0 : ℂ) : OnePoint ℂ) = OnePoint.infty := by
  simp [b65p_mobius]

example (a b : ℂ) (ha : a ≠ 0) :
    b65p_mobius a b ((a : ℂ) : OnePoint ℂ) = ((0 : ℂ) : OnePoint ℂ) := by
  simp [b65p_mobius, ha, b65s_normalize]

/-- The certified marking hypothesis on the base system: transport of the printed pullback
coefficient along the loops `γ i.rev` is the conjugate by one operator `C` of the decoded final
certificate matrix in slot `i`. This is the shape of the conclusion of
`b65b_transported_identification`.
Source: `docs/specs/BraidCertificate.md`, statement 8. -/
def b65p_certifiedTransport (x : b65s_regular) (γ : Fin 13 → Path x x) (i : Fin 13) :
    (Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ) :=
  b65f_transport (Fin 4 → ℂ) b65r_pullback (fun u ↦ ((γ i.rev).extend u).val)

example (x : b65s_regular) (γ : Fin 13 → Path x x) (i : Fin 13) :
    b65p_certifiedTransport x γ i =
      b65f_transport (Fin 4 → ℂ) b65r_pullback (fun u ↦ ((γ i.rev).extend u).val) := rfl

/-- **The stage 5c outputs consumed by stage 5d.** For twelve labelled reflection poles `p`:
a radius, the Schlesinger residues along the moving poles with their initial values, analyticity
and equations, distinct poles, zero residue sum and the identification of the base coefficient
with `b65r_pullback`; the normalized path with the field types of `g32r_PeriodMap.curve_cont`
and `.curve_zero` (for `V = b6t_polydisc (b65p_curve p 0)`), its stay in that polydisc and in
`b6_chart`, and the Möbius normalization at each parameter; analytic normal forms at the four
fixed poles for every ordered eigenbasis of the initial residue; and the certified marked
monodromy along the path for every certified marking of the base system.
This is a record of outputs, not a premise: `b65p_outputs` asserts that it is inhabited.
Source: G32 v0.16, §5.4 (Lemma 5.6), §5.5 (The direction, items (2)–(3)) and Lemma 5.7;
`docs/specs/KernelFrames.md`, review section (the 5d family inputs). -/
structure b65p_Outputs (p : Fin 12 → ℂ) where
  /-- The parameter radius. -/
  radius : ℝ
  /-- The radius is positive. -/
  radius_pos : 0 < radius
  /-- The residues along the path. -/
  residue : ℂ → Fin 4 ⊕ Fin 12 → (Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ)
  /-- Initial residues. -/
  residue_zero : residue 0 = b65p_initialResidue
  /-- The residues are holomorphic in `θ`. -/
  residue_analytic : ∀ q, AnalyticOnNhd ℂ (fun θ ↦ residue θ q) (ball 0 radius)
  /-- The Schlesinger equations along the moving poles. -/
  schlesinger : ∀ θ ∈ ball (0 : ℂ) radius, ∀ q, HasDerivAt (fun θ ↦ residue θ q)
    (b65p_schlesingerField (Fin 4 → ℂ) (b65p_velocity p) (b65p_poles p θ) (residue θ) q) θ
  /-- The sixteen poles stay distinct. -/
  poles_injective : ∀ θ ∈ ball (0 : ℂ) radius, Function.Injective (b65p_poles p θ)
  /-- The point at infinity stays regular. -/
  residue_sum : ∀ θ ∈ ball (0 : ℂ) radius, ∑ q, residue θ q = 0
  /-- At `θ = 0` the system is the printed pullback system. -/
  base_coefficient : ∀ s ∈ b65s_regular,
    b65p_coefficient (Fin 4 → ℂ) (b65p_poles p 0) (residue 0) s = b65r_pullback s
  /-- The path is continuous at `0` (the type of `g32r_PeriodMap.curve_cont`). -/
  curve_cont : ContinuousAt (b65p_curve p) 0
  /-- The base point lies in the chart polydisc (the type of `g32r_PeriodMap.curve_zero`). -/
  curve_zero : b65p_curve p 0 ∈ b6t_polydisc (b65p_curve p 0)
  /-- The path stays in the polydisc and in the normalized chart. -/
  curve_mem : ∀ θ ∈ ball (0 : ℂ) radius,
    b65p_curve p θ ∈ b6t_polydisc (b65p_curve p 0) ∧ b65p_curve p θ ∈ b6_chart
  /-- The Möbius normalization of three branch points to `0, 1, ∞`. -/
  normalization : ∀ θ ∈ ball (0 : ℂ) radius, ∃ M : OnePoint ℂ ≃ₜ OnePoint ℂ,
    ⇑M = b65p_mobius (b65p_moving p θ 10) (b65p_moving p θ 11) ∧
      ∀ k, M (b65p_source p θ k) = b6_branch (b65p_curve p θ) k
  /-- Analytic normal forms at the fixed poles, for every ordered eigenbasis at `θ = 0`. -/
  normal_form : ∀ k : Fin 4, ∀ P₀ : (Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ), IsUnit P₀ →
    residue 0 (Sum.inl k) * P₀ = P₀ * b65p_exponent k →
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ radius ∧
    ∃ P : ℂ → (Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ),
    ∃ H : ℂ → ℂ → (Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ),
      AnalyticOnNhd ℂ P (ball 0 ε) ∧ P 0 = P₀ ∧
      (∀ θ ∈ ball (0 : ℂ) ε, IsUnit (P θ) ∧
        residue θ (Sum.inl k) * P θ = P θ * b65p_exponent k) ∧
      AnalyticOnNhd ℂ (fun w : ℂ × ℂ ↦ H w.1 w.2)
        (ball (b65p_fixedPole k) ε ×ˢ ball 0 ε) ∧
      (∀ θ ∈ ball (0 : ℂ) ε, H (b65p_fixedPole k) θ = 1) ∧
      ∀ θ ∈ ball (0 : ℂ) ε, ∀ s ∈ ball (b65p_fixedPole k) ε,
        (s - b65p_fixedPole k) • deriv (fun s ↦ H s θ) s =
          b65p_exponent k * H s θ - H s θ * b65p_exponent k +
            (s - b65p_fixedPole k) • ((Ring.inverse (P θ) *
              b65p_regularPart (Fin 4 → ℂ) (b65p_poles p θ) (residue θ) (Sum.inl k) s *
                P θ) * H s θ)
  /-- The certified marked monodromy is constant along the path. -/
  marking : ∀ (x : b65s_regular) (γ : Fin 13 → Path x x)
    (C : ((Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ))ˣ),
    (∀ i, b65p_certifiedTransport x γ i =
      C.val * b65r_operator (b65b_decode (b65b_finalIntegral i)) * (C⁻¹).val) →
    ∃ r : ℝ, 0 < r ∧ r ≤ radius ∧ ∀ θ ∈ ball (0 : ℂ) r,
      (∀ i s q, ((γ i s : b65s_regular) : ℂ) ≠ b65p_poles p θ q) ∧
      ∃ Cθ : ((Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ))ˣ, ∀ i,
        b65f_transport (Fin 4 → ℂ) (b65p_coefficient (Fin 4 → ℂ) (b65p_poles p θ) (residue θ))
            (fun u ↦ ((γ i.rev).extend u).val) =
          Cθ.val * b65r_operator (b65b_decode (b65b_finalIntegral i)) * (Cθ⁻¹).val

/-- Projection of the path fields of a record. -/
example (p : Fin 12 → ℂ) (O : b65p_Outputs p) :
    ContinuousAt (b65p_curve p) 0 ∧ b65p_curve p 0 ∈ b6t_polydisc (b65p_curve p 0) :=
  ⟨O.curve_cont, O.curve_zero⟩

end HodgeLean.Foundations.Program
