import HodgeLean.Papers.G34FamilyProofs
import HodgeLean.Papers.G34Boundary

/-! # G34 Theorem A, stage 2: the Hurwitz family and its Prym–Tyurin factor (FROZEN SPEC)

Stage 2 of the premise-first route to G34 v1.5 Theorem A, at `(n, δ) = (4, [1])` of the generic
Weil transfer: the finite combinatorial data of the `G₃₄` Hurwitz family that the repository can
carry and check, the named premise `g34h_PrymFamily` for the family and its `σ`-isotypic
Prym–Tyurin factors `A_σ(C)`, and the bridge `g34h_stageFields_partial` into `wtr_StageFields`.

Claimed:
* for the ten printed roots of Appendix A over any field of characteristic zero with a primitive
  cube root of unity `w`: the Hermitian norms are `2` or `6` as printed, each reflection `s_i`
  is an involution with `rk(s_i - 1) = 1`, `s₁` is conjugate to every `s_i` by `s₁ s_i`, the
  printed tuple `(s₁, s₁, …, s₁₀, s₁₀)` has product one, and at `w = ω` the matrices are the
  skeleton's reflections `skelg34_reflection`;
* for twenty reflections and the reflection representation `σ` of degree `6`: the Chevalley–Weil
  multiplicity is the printed angle count `defectMultiplicity 6 g34Angles` (that is,
  `-12 + 20 = 8`, by `papers_g34_multiplicity_hodge`; and `r - 12` for `r` reflections), the
  holomorphic count is the printed `holomorphicMultiplicity 6 g34Angles` (that is,
  `20 · ½ - 6 = 4`), and Riemann–Hurwitz with `|G| = 39 191 040` gives genus `156 764 161`;
* the printed tuple lies in the Nielsen class, the Nielsen class is stable under simultaneous
  conjugation by `G`, and on every Nielsen tuple the two Chevalley–Weil counts are `8` and `4`;
* from a Prym family: every fibre is a polarized eightfold of Weil type for `ℚ(√-3)`, in the
  exact shape of the stage field `fiber_polarized` of `wtr_StageFields` at `n = 4`, with Hodge
  numbers `(4, 4)` on the Weil eigenspace.

Not claimed: the Prym family itself (Hurwitz spaces, Jacobians, Prym–Tyurin factors, the
Chevalley–Weil formula and G34 Lemma 3.3 are the premise `g34h_PrymFamily`); the order of `G`,
its identification with the Shephard–Todd group `G₃₄`, or the irreducibility of `σ`; any
discriminant, algebraicity or dominance (the boundary and supplier stages). No Prym family is
constructed, so Theorem A itself remains unasserted; the bridge is the implication from the
premise and the other stages' fields.

HC no distance; AV milestone no distance.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace Set
open scoped CategoryTheory.MonObj
open HodgeLean.RealDefs HodgeLean.Foundations HodgeLean.Foundations.WeilPower
open HodgeLean.Foundations.Symplectic HodgeLean.Adapters

namespace HodgeLean.Papers

section Finite

/-- **The Hermitian norms of the printed roots**: `⟨v_i, v_i⟩` is `6, 2, 2, 6, 6, 6, 2, 6, 2, 2`
for `i = 1, …, 10`.
Source: G34 v1.5, Appendix A ("Every `⟨v_i, v_i⟩` is `2` or `6`"). -/
theorem g34h_rootNorm_eq {K : Type*} [Field K] (w : K) (hw : w ^ 2 + w + 1 = 0) (i : Fin 10) :
    g34h_rootNorm w i = ![6, 2, 2, 6, 6, 6, 2, 6, 2, 2] i :=
  g34h_rootNorm_eq_aux w hw i

example {K : Type*} [Field K] (w : K) (hw : w ^ 2 + w + 1 = 0) : g34h_rootNorm w 1 = 2 :=
  g34h_rootNorm_eq w hw 1

/-- **Each printed reflection is an involution**: `s_i² = 1`.
Source: G34 v1.5, Section 9 ("Its product is `1` because every `s_i` is an involution") and
Appendix A. -/
theorem g34h_refl_sq {K : Type*} [Field K] [CharZero K] (w : K) (hw : w ^ 2 + w + 1 = 0)
    (i : Fin 10) : g34h_refl w i * g34h_refl w i = 1 :=
  g34h_refl_sq_aux w hw i

example {K : Type*} [Field K] [CharZero K] (w : K) (hw : w ^ 2 + w + 1 = 0) (i : Fin 10) :
    (g34h_refl w i)⁻¹ = g34h_refl w i :=
  Matrix.inv_eq_left_inv (g34h_refl_sq w hw i)

/-- **`c_σ(s_i) = 1`**: `rk(s_i - 1) = 1`, since `s_i - 1 = -(2 / ⟨v_i, v_i⟩) v_i v̄_iᵀ`.
Source: G34 v1.5, proof of Lemma 9.1 ("A reflection has `c_σ = 1`"). -/
theorem g34h_rank_refl_sub_one {K : Type*} [Field K] [CharZero K] (w : K)
    (hw : w ^ 2 + w + 1 = 0) (i : Fin 10) : (g34h_refl w i - 1).rank = 1 :=
  g34h_rank_refl_sub_one_aux w hw i

example {K : Type*} [Field K] [CharZero K] (w : K) (hw : w ^ 2 + w + 1 = 0) (i : Fin 10) :
    g34h_refl w i ≠ 1 := by
  intro h
  have := g34h_rank_refl_sub_one w hw i
  rw [h, sub_self, Matrix.rank_zero] at this
  exact zero_ne_one this

/-- **The reflections form one conjugacy class**: `(s₁ s_i) s₁ (s_i s₁) = s_i` for every
printed `s_i` (with `(s₁ s_i)(s_i s₁) = 1` by `g34h_refl_sq`), equivalently the braid relation
`(s₁ s_i)³ = 1`.
Source: G34 v1.5, Section 9 ("Its reflections have order two and form one conjugacy class");
checked exactly over `ℚ(ω)` on the printed roots. -/
theorem g34h_refl_conj {K : Type*} [Field K] [CharZero K] (w : K) (hw : w ^ 2 + w + 1 = 0)
    (i : Fin 10) :
    g34h_refl w 0 * g34h_refl w i * g34h_refl w 0 * (g34h_refl w i * g34h_refl w 0) =
      g34h_refl w i :=
  g34h_refl_conj_aux w hw i

example {K : Type*} [Field K] [CharZero K] (w : K) (hw : w ^ 2 + w + 1 = 0) :
    g34h_refl w 0 * g34h_refl w 0 * g34h_refl w 0 * (g34h_refl w 0 * g34h_refl w 0) =
      g34h_refl w 0 :=
  g34h_refl_conj w hw 0

/-- **The matrices are the skeleton's reflections**: at `w = ω`, `g34h_refl ω i` acts on
`EuclideanSpace ℂ (Fin 6)` as `skelg34_reflection i`, the reflection in the hyperplane
`v_i^⊥` for the standard Hermitian form.
Source: G34 v1.5, Appendix A (`s_i(x) = x - 2 ⟨v_i, x⟩ / ⟨v_i, v_i⟩ v_i`); the definitions
`skelg34_root` and `skelg34_reflection`. -/
theorem g34h_refl_eq_skel (i : Fin 10) :
    Matrix.toEuclideanLin (g34h_refl skelg34_omega i) = (skelg34_reflection i).toLinearMap :=
  g34h_refl_eq_skel_aux i

example (i : Fin 10) (x : EuclideanSpace ℂ (Fin 6)) :
    Matrix.toEuclideanLin (g34h_refl skelg34_omega i) x = skelg34_reflection i x := by
  rw [g34h_refl_eq_skel]
  rfl

/-- **The printed tuple has product one**: `s₁ s₁ s₂ s₂ ⋯ s₁₀ s₁₀ = 1`.
Source: G34 v1.5, Section 9 ("Its product is `1` because every `s_i` is an involution"). -/
theorem g34h_tuple_prod {K : Type*} [Field K] [CharZero K] (w : K) (hw : w ^ 2 + w + 1 = 0) :
    (List.ofFn (g34h_tuple w)).prod = 1 :=
  g34h_tuple_prod_aux w hw

example : (List.ofFn (g34h_tuple skelg34_omega)).prod = 1 :=
  g34h_tuple_prod skelg34_omega g34h_omega_sq_add

/-- **Chevalley–Weil multiplicity for the class datum**: the matrix count for twenty reflections
equals the printed angle count `defectMultiplicity 6 g34Angles`, which is `-12 + 20 = 8`
(`papers_g34_multiplicity_hodge`).
Source: G34 v1.5, Proposition 3.1 (first formula) and the proof of Lemma 9.1
("`m_σ = -12 + 20 = 8`"). -/
theorem g34h_multCW_classRep {K : Type*} [Field K] [CharZero K] (w : K)
    (hw : w ^ 2 + w + 1 = 0) : g34h_multCW (g34h_classRep w) = defectMultiplicity 6 g34Angles :=
  g34h_multCW_classRep_aux w hw

example : g34h_multCW (g34h_classRep skelg34_omega) = 8 := by
  rw [g34h_multCW_classRep skelg34_omega g34h_omega_sq_add]
  exact papers_g34_multiplicity_hodge.2.1

/-- **With `r` reflections the multiplicity is `r - 12`**, so eightfolds need exactly twenty.
Source: G34 v1.5, Section 9 ("With `r` reflections the count of Lemma 9.1 gives
`m_σ = r - 12 = 2n`, so eightfolds (`n = 4`) need exactly `r = 20`"). -/
theorem g34h_multCW_reflections {K : Type*} [Field K] [CharZero K] (w : K)
    (hw : w ^ 2 + w + 1 = 0) (r : ℕ) (i : Fin 10) :
    g34h_multCW (fun _ : Fin r => g34h_refl w i) = (r : ℤ) - 12 :=
  g34h_multCW_reflections_aux w hw r i

example {K : Type*} [Field K] [CharZero K] (w : K) (hw : w ^ 2 + w + 1 = 0) :
    g34h_multCW (fun _ : Fin 18 => g34h_refl w 0) ≠ g34h_multCW (g34h_classRep w) := by
  rw [g34h_multCW_reflections w hw 18 0,
    show g34h_classRep w = fun _ : Fin 20 => g34h_refl w 0 from rfl,
    g34h_multCW_reflections w hw 20 0]
  norm_num

/-- **Chevalley–Weil holomorphic count for the class datum**: the inverse of a reflection has
eigenvalues `-1` once and `1` five times, age `½`; the matrix count equals the printed
`holomorphicMultiplicity 6 g34Angles`, which is `20 · ½ - 6 = 4`
(`papers_g34_multiplicity_hodge`).
Source: G34 v1.5, Proposition 3.1 (second formula) and the proof of Lemma 9.1
("`20 · ½ - 6 = 4` for each Hodge number"); FGP, IMRN 2015, Theorem 2.10. -/
theorem g34h_holoCW_classRep (w : ℂ) (hw : w ^ 2 + w + 1 = 0) :
    g34h_holoCW (g34h_classRep w) = (holomorphicMultiplicity 6 g34Angles : ℝ) :=
  g34h_holoCW_classRep_aux w hw

example : g34h_holoCW (g34h_classRep skelg34_omega) = 4 := by
  rw [g34h_holoCW_classRep skelg34_omega g34h_omega_sq_add,
    papers_g34_multiplicity_hodge.2.2.2.1]
  norm_num

/-- **Riemann–Hurwitz for the class datum.** With `|G| = 39 191 040` (the printed order, entered
as a number) and twenty branch points of order `2`,
`2g - 2 = 39 191 040 (-2 + 20 · ½) = 313 528 320`, so `g = 156 764 161`.
Source: G34 v1.5, Example 9.3 ("`2g(C) - 2 = |G₃₄|(-2 + 20 · ½) = 8|G₃₄|`") and Appendix A
(the order). -/
theorem g34h_riemannHurwitz {K : Type*} [Field K] [CharZero K] (w : K)
    (hw : w ^ 2 + w + 1 = 0) :
    (39191040 : ℚ) * (-2 + ∑ j, (1 - 1 / (orderOf (g34h_classRep w j) : ℚ))) =
      2 * 156764161 - 2 :=
  g34h_riemannHurwitz_aux w hw

example {K : Type*} [Field K] [CharZero K] (w : K) (hw : w ^ 2 + w + 1 = 0) :
    (39191040 : ℚ) * (-2 + ∑ j, (1 - 1 / (orderOf (g34h_classRep w j) : ℚ))) =
      8 * 39191040 := by
  rw [g34h_riemannHurwitz w hw]; norm_num

end Finite

section Nielsen

/-- **The printed tuple lies in the Nielsen class of twenty reflections**: each `s_i` is
conjugate in `G` to `s₁`, the product is one, and the ten reflections generate `G`.
Source: G34 v1.5, Section 9 ("So `𝐠` lies in the Nielsen class of twenty reflections"). -/
theorem g34h_tuple_nielsen : g34h_Nielsen (g34h_tuple skelg34_omega) :=
  g34h_tuple_nielsen_aux

/-- The Nielsen class is nonempty. -/
example : ∃ g, g34h_Nielsen g := ⟨_, g34h_tuple_nielsen⟩

/-- **The Nielsen class is stable under simultaneous conjugation by `G`**, so a cover determines
its Nielsen tuple up to this conjugation.
Source: G34 v1.5, Subsection 3.1 ("such a tuple up to simultaneous conjugation"). -/
theorem g34h_nielsen_conj (g : Fin 20 → Matrix (Fin 6) (Fin 6) ℂ) (hg : g34h_Nielsen g)
    (h h' : Matrix (Fin 6) (Fin 6) ℂ) (hh : h ∈ g34h_G) (hh' : h' ∈ g34h_G) (hinv : h * h' = 1) :
    g34h_Nielsen (fun j => h * g j * h') :=
  g34h_nielsen_conj_aux g hg h h' hh hh' hinv

example (g : Fin 20 → Matrix (Fin 6) (Fin 6) ℂ) (hg : g34h_Nielsen g) :
    g34h_Nielsen (fun j => 1 * g j * 1) :=
  g34h_nielsen_conj g hg 1 1 (one_mem _) (one_mem _) (mul_one 1)

/-- **Chevalley–Weil multiplicity on the Nielsen class.** For every Nielsen tuple, `m_σ = 8`:
`rk(σ(g) - 1)` depends only on the conjugacy class, and every class is that of reflections.
Source: G34 v1.5, Proposition 3.1 and Lemma 9.1. -/
theorem g34h_multCW_of_nielsen (g : Fin 20 → Matrix (Fin 6) (Fin 6) ℂ)
    (hg : g34h_Nielsen g) : g34h_multCW g = 8 :=
  g34h_multCW_of_nielsen_aux g hg

example (g : Fin 20 → Matrix (Fin 6) (Fin 6) ℂ) (hg : g34h_Nielsen g) :
    g34h_multCW g = defectMultiplicity 6 g34Angles := by
  rw [g34h_multCW_of_nielsen g hg, papers_g34_multiplicity_hodge.2.1]

/-- **Chevalley–Weil holomorphic count on the Nielsen class.** For every Nielsen tuple,
`dim Hom_G(σ, H⁰(K_C)) = 4`: ages are conjugation invariant.
Source: G34 v1.5, Proposition 3.1 and Lemma 9.1; FGP, IMRN 2015, Theorem 2.10. -/
theorem g34h_holoCW_of_nielsen (g : Fin 20 → Matrix (Fin 6) (Fin 6) ℂ)
    (hg : g34h_Nielsen g) : g34h_holoCW g = 4 :=
  g34h_holoCW_of_nielsen_aux g hg

example (g : Fin 20 → Matrix (Fin 6) (Fin 6) ℂ) (hg : g34h_Nielsen g) :
    (g34h_multCW g : ℝ) - g34h_holoCW g = g34h_holoCW g := by
  rw [g34h_multCW_of_nielsen g hg, g34h_holoCW_of_nielsen g hg]; norm_num

end Nielsen

section Family

/-- **Every fibre of a Prym family is a polarized eightfold of Weil type for `ℚ(√-3)`**, in the
exact shape of the stage field `fiber_polarized` of `wtr_StageFields` at `n = 4`. `dim = 8` and
Weil type come from the link fields `dim_eq` and `hodge` with the counts `m_σ = 8`, `p_σ = 4` on
the Nielsen class (`isWeilType_iff_finrank_eq`); the polarization clauses are the premise's.
Source: G34 v1.5, Lemma 9.1 ("`A_σ(C)` is an abelian eightfold of Weil type for `K`"), from
Proposition 3.1 and Lemma 3.3. -/
theorem g34h_fiber_polarized (P : g34h_PrymFamily) :
    ∀ s, wtr_PolarizedWeil 4 (P.fiber s) :=
  g34h_fiber_polarized_aux P

example (P : g34h_PrymFamily) (s : P.S) : dim (P.fiber s).X.left = 8 :=
  (g34h_fiber_polarized P s).dim_eq

/-- **Hodge numbers `(4, 4)`**: on every fibre of a Prym family, the two Hodge pieces of the
Weil eigenspace both have dimension `4`.
Source: G34 v1.5, Lemma 9.1 ("with Hodge numbers `(4,4)`"). -/
theorem g34h_h10_eq_four (P : g34h_PrymFamily) (s : P.S) :
    g32h_h10 (P.fiber s) = 4 ∧ g32h_h01 (P.fiber s) = 4 :=
  g34h_h10_eq_four_aux P s

example (P : g34h_PrymFamily) (s : P.S) : g32h_h10 (P.fiber s) = g32h_h01 (P.fiber s) :=
  (g34h_h10_eq_four P s).1.trans (g34h_h10_eq_four P s).2.symm

/-- **The bridge to the stage fields.** From a Prym family `P` and the fields that the other
stages supply over it, the `wtr_StageFields F` at `(4, [1])` with `S := P.S`, `fiber := P.fiber`
and `fiber_polarized := g34h_fiber_polarized P`; the discriminant, algebraicity, dominance,
spreading and transport fields are copied from `R`.
Source: G34 v1.5, Section 3 and Lemma 9.1; the fields of `wtr_StageFields`. -/
def g34h_stageFields_partial (F : wtr_UniversalFamily 4 1) (P : g34h_PrymFamily)
    (R : g34h_RemainingFields F P) : wtr_StageFields F where
  S := P.S
  fiber := P.fiber
  fiber_polarized := g34h_fiber_polarized P
  fiber_disc := fun s => R.fiber_disc s _
  fiber_alg := R.fiber_alg
  dominant := R.dominant
  spread := R.spread
  transport := R.transport

/-- The bridge fills `S` and `fiber` from stage 2 and nothing else. -/
example (F : wtr_UniversalFamily 4 1) (P : g34h_PrymFamily) (R : g34h_RemainingFields F P) :
    (g34h_stageFields_partial F P R).fiber = P.fiber ∧
      (g34h_stageFields_partial F P R).fiber_alg = R.fiber_alg :=
  ⟨rfl, rfl⟩

/-- With the boundary stage: the parabolic-polarization comparison on each fibre and a boundary
period map over `P.fiber` give the fields `fiber_disc` (`g34b_fiber_disc`) and `dominant`
(`g34b_dominant`) of `g34h_RemainingFields`. -/
example (F : wtr_UniversalFamily 4 1) (P : g34h_PrymFamily)
    (hpar : ∀ s, g34b_ParabolicPolarization (g34h_fiber_polarized P s))
    (Φ : g34b_BoundaryPeriodMap F P.fiber) (fiber_alg : ∀ s, wtr_WeilAlg (P.fiber s))
    (spread : ∃ C : Set (Set (wtr_Domain 4)), C.Countable ∧
      (∀ Z ∈ C, IsClosedAnalytic (Fin (4 ^ 2) → ℂ) Z) ∧ {m | wtr_WeilAlg (F.univ m)} = ⋃₀ C)
    (transport : ∀ P Q : wtr_Variety 4, wtr_KIsog P Q → (wtr_WeilAlg P ↔ wtr_WeilAlg Q)) :
    g34h_RemainingFields F P :=
  ⟨fun s _ => g34b_fiber_disc P.fiber (g34h_fiber_polarized P) hpar s, fiber_alg,
    g34b_dominant F P.fiber Φ, spread, transport⟩

end Family

end HodgeLean.Papers
