import HodgeLean.Papers.G32FamilyProofs

/-! # G32 Theorem A, stage 2: the Hurwitz family and its Prym factor (FROZEN SPEC)

Stage 2 of the premise-first route to G32 v0.16 Theorem A: the finite combinatorial data of the
`G₃₂` Hurwitz family that the repository can carry and check, the named premise
`g32h_PrymFamily` for the family and its `ρ`-isotypic factors `A_ρ(C)`, and the bridge
`g32h_stageFields_partial` into `g32m_StageFields`.

Claimed:
* for the class datum (six reflections of class `𝓡₁`, six of class `𝓡₂`, one element of class
  `𝓘`) and the natural representation `ρ` of the printed `r₁, r₂, x, y`: the Chevalley–Weil
  multiplicity is `-8 + 12 + 2 = 6` (and `4` without the point of class `𝓘`), the holomorphic
  count is `6 · ⅔ + 6 · ⅓ + 1 - 4 = 3`, and Riemann–Hurwitz with `|G| = 155 520` gives genus
  `505 441`;
* Katz's rigidity count for the tuple `(r₁, r₂, x, y)`: the four class dimensions sum to
  `2 (4² - 1) = 30`;
* the Nielsen class is stable under simultaneous conjugation by `G`, and on every Nielsen tuple
  the two Chevalley–Weil counts are `6` and `3`;
* from a Prym family: every fibre is a polarized sixfold of Weil type for `ℚ(√-3)`, in the exact
  shape of the stage field `fiber_polarized`, with Hodge numbers `(3, 3)` on the `i√3`-eigenspace;
  with the remaining stage fields, the Nielsen class is nonempty.

Not claimed: the Prym family itself (Hurwitz spaces, Jacobians, Prym–Tyurin factors, the
Chevalley–Weil formula and G32 Lemma 3.3 are the premise `g32h_PrymFamily`); nonemptiness of the
Nielsen class on its own (the cover `C₀` of G32 Lemma 5.2 needs the monodromy of a pullback); the
order of `G`, its generation by three of the matrices, or the identification of the pullback local
system; any discriminant, algebraicity or dominance (stages 5, 3 and 4). No Prym family is
constructed, so Theorem A itself remains unasserted.

HC no distance; AV milestone no distance.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace Set
open scoped CategoryTheory.MonObj
open HodgeLean.RealDefs HodgeLean.Foundations HodgeLean.Foundations.WeilPower
open HodgeLean.Foundations.Symplectic HodgeLean.Adapters

namespace HodgeLean.Papers

section Finite

/-- **Chevalley–Weil multiplicity for the class datum.** A reflection has `rk(ρ(g) - 1) = 1` and
`x²` has `rk(x² - 1) = 2`, so `m_ρ = -2 · 4 + 12 · 1 + 2 = 6`.
Source: G32 v0.16, Proposition 3.1 (first formula) and the proof of Lemma 3.6
("`m_ρ = -8 + 12 + 2 = 6`"). -/
theorem g32h_multCW_classRep {K : Type*} [Field K] [CharZero K] (w : K)
    (hw : w ^ 2 + w + 1 = 0) : g32h_multCW (g32h_classRep w) = 6 :=
  g32h_multCW_classRep_aux w hw

example : g32h_multCW (g32h_classRep g32h_omega) = 6 :=
  g32h_multCW_classRep g32h_omega g32h_omega_sq_add

/-- **Without the point of class `𝓘` the multiplicity is four.** For the twelve reflections
alone, `m_ρ = -8 + 12 = 4`, which would give fourfolds.
Source: G32 v0.16, Subsection 1.4 ("Without the point in `𝓘` the multiplicity would be four"). -/
theorem g32h_multCW_without_involution {K : Type*} [Field K] [CharZero K] (w : K)
    (hw : w ^ 2 + w + 1 = 0) :
    g32h_multCW (fun j : Fin 12 => g32h_classRep w j.castSucc) = 4 :=
  g32h_multCW_without_involution_aux w hw

example {K : Type*} [Field K] [CharZero K] (w : K) (hw : w ^ 2 + w + 1 = 0) :
    g32h_multCW (fun j : Fin 12 => g32h_classRep w j.castSucc) ≠
      g32h_multCW (g32h_classRep w) := by
  rw [g32h_multCW_without_involution w hw, g32h_multCW_classRep w hw]
  norm_num

/-- **Chevalley–Weil holomorphic count for the class datum.** The inverse of a reflection of
class `𝓡₁` has age `⅔`, of class `𝓡₂` age `⅓` (the two swap if `w` is the other primitive cube
root), and `x⁻²` has age `1`; so `dim Hom_G(ρ, H⁰(K_C)) = 6 · ⅔ + 6 · ⅓ + 1 - 4 = 3`.
Source: G32 v0.16, Proposition 3.1 (second formula) and the proof of Lemma 3.6; FGP, IMRN 2015,
Theorem 2.10. -/
theorem g32h_holoCW_classRep (w : ℂ) (hw : w ^ 2 + w + 1 = 0) :
    g32h_holoCW (g32h_classRep w) = 3 :=
  g32h_holoCW_classRep_aux w hw

example : (g32h_multCW (g32h_classRep g32h_omega) : ℝ) - g32h_holoCW (g32h_classRep g32h_omega) =
    3 := by
  rw [g32h_multCW_classRep g32h_omega g32h_omega_sq_add,
    g32h_holoCW_classRep g32h_omega g32h_omega_sq_add]
  norm_num

/-- **Riemann–Hurwitz for the class datum.** With `|G| = 155 520` (the printed order, entered as
a number) and the orders `3, 3, 2` of `r₁, r₂, x²`,
`2g - 2 = 155 520 (-2 + 12 · ⅔ + ½) = 1 010 880`, so `g = 505 441`.
Source: G32 v0.16, the proof of Lemma 3.6 (Riemann–Hurwitz) and Subsection 1.4. -/
theorem g32h_riemannHurwitz {K : Type*} [Field K] [CharZero K] (w : K)
    (hw : w ^ 2 + w + 1 = 0) :
    (155520 : ℚ) * (-2 + ∑ j, (1 - 1 / (orderOf (g32h_classRep w j) : ℚ))) =
      2 * 505441 - 2 :=
  g32h_riemannHurwitz_aux w hw

example {K : Type*} [Field K] [CharZero K] (w : K) (hw : w ^ 2 + w + 1 = 0) :
    (155520 : ℚ) * (-2 + ∑ j, (1 - 1 / (orderOf (g32h_classRep w j) : ℚ))) = 1010880 := by
  rw [g32h_riemannHurwitz w hw]; norm_num

/-- **Katz's rigidity count for `(r₁, r₂, x, y)`.** The conjugacy classes of `r₁, r₂, x, y` in
`GL₄(ℂ)` have dimensions `6, 6, 10, 8` (centralizers of dimensions `10, 10, 6, 8`), with sum
`30 = 2 (4² - 1)`: the dimension condition of Katz's theorem.
Source: G32 v0.16, Subsection 5.2 ("The dimensions of the four classes are
`6 + 6 + 10 + 8 = 30 = 2(4² - 1)`"); Katz, *Rigid Local Systems*, Ann. of Math. Stud. 139 (1996),
Theorem 1.1.2. -/
theorem g32h_rigidity_count (w : ℂ) (hw : w ^ 2 + w + 1 = 0) :
    ((16 : ℤ) - g32h_centralizerDim (g32R1 w)) + (16 - g32h_centralizerDim (g32R2 w)) +
      (16 - g32h_centralizerDim (g32X w)) + (16 - g32h_centralizerDim (g32Y w)) =
      2 * (4 ^ 2 - 1) :=
  g32h_rigidity_count_aux w hw

example (w : ℂ) (hw : w ^ 2 + w + 1 = 0) :
    ((16 : ℤ) - g32h_centralizerDim (g32R1 w)) + (16 - g32h_centralizerDim (g32R2 w)) +
      (16 - g32h_centralizerDim (g32X w)) + (16 - g32h_centralizerDim (g32Y w)) = 30 := by
  rw [g32h_rigidity_count w hw]; norm_num

end Finite

section Nielsen

/-- **The Nielsen class is stable under simultaneous conjugation by `G`**, so a cover determines
its Nielsen tuple up to this conjugation.
Source: G32 v0.16, Subsection 3.1 ("such a tuple up to simultaneous conjugation"). -/
theorem g32h_nielsen_conj (g : Fin 13 → Matrix (Fin 4) (Fin 4) ℂ) (hg : g32h_Nielsen g)
    (h h' : Matrix (Fin 4) (Fin 4) ℂ) (hh : h ∈ g32h_G) (hh' : h' ∈ g32h_G) (hinv : h * h' = 1) :
    g32h_Nielsen (fun j => h * g j * h') :=
  g32h_nielsen_conj_aux g hg h h' hh hh' hinv

example (g : Fin 13 → Matrix (Fin 4) (Fin 4) ℂ) (hg : g32h_Nielsen g) :
    g32h_Nielsen (fun j => 1 * g j * 1) :=
  g32h_nielsen_conj g hg 1 1 (one_mem _) (one_mem _) (mul_one 1)

/-- **Chevalley–Weil multiplicity on the Nielsen class.** For every Nielsen tuple, `m_ρ = 6`:
`rk(ρ(g) - 1)` depends only on the conjugacy class, and the classes form the class datum.
Source: G32 v0.16, Proposition 3.1 and Lemma 3.6 ("For every `C ∈ Hur`"). -/
theorem g32h_multCW_of_nielsen (g : Fin 13 → Matrix (Fin 4) (Fin 4) ℂ)
    (hg : g32h_Nielsen g) : g32h_multCW g = 6 :=
  g32h_multCW_of_nielsen_aux g hg

example (g : Fin 13 → Matrix (Fin 4) (Fin 4) ℂ) (hg : g32h_Nielsen g) :
    g32h_multCW g = g32h_multCW (g32h_classRep g32h_omega) := by
  rw [g32h_multCW_of_nielsen g hg, g32h_multCW_classRep g32h_omega g32h_omega_sq_add]

/-- **Chevalley–Weil holomorphic count on the Nielsen class.** For every Nielsen tuple,
`dim Hom_G(ρ, H⁰(K_C)) = 3`: ages are conjugation invariant.
Source: G32 v0.16, Proposition 3.1 and Lemma 3.6; FGP, IMRN 2015, Theorem 2.10. -/
theorem g32h_holoCW_of_nielsen (g : Fin 13 → Matrix (Fin 4) (Fin 4) ℂ)
    (hg : g32h_Nielsen g) : g32h_holoCW g = 3 :=
  g32h_holoCW_of_nielsen_aux g hg

example (g : Fin 13 → Matrix (Fin 4) (Fin 4) ℂ) (hg : g32h_Nielsen g) :
    (g32h_multCW g : ℝ) - g32h_holoCW g = g32h_holoCW g := by
  rw [g32h_multCW_of_nielsen g hg, g32h_holoCW_of_nielsen g hg]; norm_num

end Nielsen

section Family

/-- **Every fibre of a Prym family is a polarized sixfold of Weil type for `ℚ(√-3)`**, in the
exact shape of the stage field `fiber_polarized`. `dim = 6` and Weil type come from the link
fields `dim_eq` and `hodge` with the counts `m_ρ = 6`, `p_ρ = 3` on the Nielsen class
(`isWeilType_iff_finrank_eq`); the polarization clauses are the premise's.
Source: G32 v0.16, Lemma 3.6 (`A_ρ(C)` is a polarized abelian sixfold of Weil type for `K`),
from Proposition 3.1 and Lemma 3.3. -/
theorem g32h_fiber_polarized (P : g32h_PrymFamily) :
    ∀ s, g32t_PolarizedWeil (P.fiber s) :=
  g32h_fiber_polarized_aux P

example (P : g32h_PrymFamily) (s : P.S) : dim (P.fiber s).X.left = 6 :=
  (g32h_fiber_polarized P s).dim_eq

/-- **Hodge numbers `(3, 3)`**: on every fibre of a Prym family, `V_s ∩ H^{1,0}` and
`V_s ∩ H^{0,1}` both have dimension `3`.
Source: G32 v0.16, Lemma 3.6 ("Hodge numbers `(3,3)`"). -/
theorem g32h_h10_eq_three (P : g32h_PrymFamily) (s : P.S) :
    g32h_h10 (P.fiber s) = 3 ∧ g32h_h01 (P.fiber s) = 3 :=
  g32h_h10_eq_three_aux P s

example (P : g32h_PrymFamily) (s : P.S) : g32h_h10 (P.fiber s) = g32h_h01 (P.fiber s) :=
  (g32h_h10_eq_three P s).1.trans (g32h_h10_eq_three P s).2.symm

/-- **The bridge to the stage fields.** From a Prym family `P` and the fields that stages 3–6
supply over it, the `g32m_StageFields` with `S := P.S`, `fiber := P.fiber` and
`fiber_polarized := g32h_fiber_polarized P`; the discriminant, algebraicity, dominance, spreading
and transport fields are copied from `R`.
Source: G32 v0.16, Section 3 and Lemma 3.6; the fields of `g32m_StageFields`. -/
def g32h_stageFields_partial (F : g32m_UniversalFamily) (P : g32h_PrymFamily)
    (R : g32h_RemainingFields F P) : g32m_StageFields F where
  S := P.S
  fiber := P.fiber
  fiber_polarized := g32h_fiber_polarized P
  fiber_disc := fun s => R.fiber_disc s _
  fiber_alg := R.fiber_alg
  dominant := R.dominant
  spread := R.spread
  transport := R.transport

/-- The bridge fills `S` and `fiber` from stage 2 and nothing else. -/
example (F : g32m_UniversalFamily) (P : g32h_PrymFamily) (R : g32h_RemainingFields F P) :
    (g32h_stageFields_partial F P R).fiber = P.fiber ∧
      (g32h_stageFields_partial F P R).fiber_alg = R.fiber_alg :=
  ⟨rfl, rfl⟩

/-- **With dominance, the Nielsen class is nonempty.** The dominant open set is nonempty and each
of its points is an isogeny target of some fibre, so `P.S` is inhabited and its monodromy tuple
is a Nielsen tuple.
Source: G32 v0.16, Definition 3.5 (`Hur°` is the component of `C₀`) and Corollary 5.11. -/
theorem g32h_exists_nielsen (F : g32m_UniversalFamily) (P : g32h_PrymFamily)
    (R : g32h_RemainingFields F P) : ∃ g, g32h_Nielsen g :=
  g32h_exists_nielsen_aux F P R

example (F : g32m_UniversalFamily) (P : g32h_PrymFamily) (R : g32h_RemainingFields F P) :
    ∃ g : Fin 13 → Matrix (Fin 4) (Fin 4) ℂ, (List.ofFn g).prod = 1 :=
  let ⟨g, hg⟩ := g32h_exists_nielsen F P R
  ⟨g, hg.2.1⟩

end Family

end HodgeLean.Papers
