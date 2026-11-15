import HodgeLean.Foundations.Program.RoucheRootCountProofs

/-!
# Rouché and Pellet root counts, and the twelve certified boxes (FROZEN SPEC)

Three general statements concern complex polynomials and use Mathlib notions only:
symmetric Rouché on a circle, and the two Pellet tests (exactly one zero, no zero) in an
open disc, all counted with multiplicity through `Polynomial.roots`. They are not stated
for holomorphic functions in general.

Two application statements concern the sextics `P₅` and `P₋₇` of G32 §5.2 and the twelve
boxes of the B65-BRAIDCERT certificate: the exact rational Pellet inequalities of checker
part A, and the isolating-box statement set aside from `BraidCertificate`, here under the
name `rou_b65b_isolating_boxes`. The latter is the implication from the Pellet statement at
radii `h` and `3h/2` together with the rational inequalities and the disc–square inclusions
`D(c, h) ⊆ square ⊆ D(c, 3h/2)`. Nothing is claimed about disjointness of the boxes, the
lasso discs, crossing words or the braid marking.
HC no distance; AV milestone no distance.
-/

noncomputable section
namespace HodgeLean.Foundations.Program

open Polynomial

/-- Symmetric Rouché for polynomials: strict dominance `‖p − q‖ < ‖q‖` on the circle of
radius `r` gives the same number of roots, with multiplicity, in the open disc.
Source: Rouché, *J. École Polytech.* 39 (1862), 193–224; Ahlfors, *Complex Analysis*,
3rd ed., §5.2.3, Rouché's theorem; Estermann's symmetric form `|f − g| < |g|`. -/
theorem rou_rouche (p q : ℂ[X]) (c : ℂ) (r : ℝ)
    (h : ∀ z ∈ Metric.sphere c r, ‖(p - q).eval z‖ < ‖q.eval z‖) :
    rou_discCount p c r = rou_discCount q c r :=
  rou_rouche_aux p q c r h

example (p q : ℂ[X]) (c : ℂ) (r : ℝ)
    (h : ∀ z ∈ Metric.sphere c r, ‖(p - q).eval z‖ < ‖q.eval z‖) :
    rou_discCount p c r = rou_discCount q c r :=
  rou_rouche p q c r h

/-- Pellet's test for one zero: if the linear Taylor coefficient at `c` dominates the others
on radius `r > 0`, then `p` has exactly one zero, with multiplicity, in `D(c, r)`.
Source: Pellet, *Bull. Sci. Math.* (2) 5 (1881), 393–395; Marden, *Geometry of
Polynomials*, 2nd ed., §27, Theorem (27,1) with `k = 1`; proof by `rou_rouche` against
`a₁ (X − c)`. -/
theorem rou_pellet_one (p : ℂ[X]) (c : ℂ) (r : ℝ) (hr : 0 < r)
    (h : rou_pelletTail p c r 1 < ‖(taylor c p).coeff 1‖ * r) :
    rou_discCount p c r = 1 :=
  rou_pellet_one_aux p c r hr h

example (p : ℂ[X]) (c : ℂ) (r : ℝ) (hr : 0 < r)
    (h : rou_pelletTail p c r 1 < ‖(taylor c p).coeff 1‖ * r) :
    rou_discCount p c r = 1 :=
  rou_pellet_one p c r hr h

/-- Pellet's test for no zero: if the constant Taylor coefficient at `c` dominates the others
on radius `r`, then `p` has no zero in `D(c, r)`.
Source: Pellet, *Bull. Sci. Math.* (2) 5 (1881), 393–395; Marden, *Geometry of
Polynomials*, 2nd ed., §27, Theorem (27,1) with `k = 0`. -/
theorem rou_pellet_zero (p : ℂ[X]) (c : ℂ) (r : ℝ)
    (h : rou_pelletTail p c r 0 < ‖(taylor c p).coeff 0‖) :
    rou_discCount p c r = 0 :=
  rou_pellet_zero_aux p c r h

example (p : ℂ[X]) (c : ℂ) (r : ℝ)
    (h : rou_pelletTail p c r 0 < ‖(taylor c p).coeff 0‖) :
    rou_discCount p c r = 0 :=
  rou_pellet_zero p c r h

/-- The exact rational Pellet inequalities of checker part A for the twelve boxes: the own
sextic passes the one-zero test at radii `h = 1/10000` and `3h/2`, and the other sextic
(`ε ↦ −2 − ε` swaps `5` and `−7`) passes the no-zero test at `3h/2`. Squared moduli are
compared, and `|re| + |im|` majorizes each modulus.
Source: B65-BRAIDCERT checker `chk_b65.gp` part A, `pellet1` and `pellet0`, multiplied
through by `ρ`; JSON boxes. -/
theorem rou_b65b_pellet_rational :
    ∀ i : Fin 12,
      rou_ratTail (rou_sextic (b65b_boxFibre i)) (b65b_boxCentre i).1 (b65b_boxCentre i).2
          (1/10000) 1 ^ 2 <
        rou_normSq (rou_shift (rou_sextic (b65b_boxFibre i))
          (b65b_boxCentre i).1 (b65b_boxCentre i).2 1) * (1/10000) ^ 2 ∧
      rou_ratTail (rou_sextic (b65b_boxFibre i)) (b65b_boxCentre i).1 (b65b_boxCentre i).2
          (3/20000) 1 ^ 2 <
        rou_normSq (rou_shift (rou_sextic (b65b_boxFibre i))
          (b65b_boxCentre i).1 (b65b_boxCentre i).2 1) * (3/20000) ^ 2 ∧
      rou_ratTail (rou_sextic (-2 - b65b_boxFibre i)) (b65b_boxCentre i).1
          (b65b_boxCentre i).2 (3/20000) 0 ^ 2 <
        rou_normSq (rou_shift (rou_sextic (-2 - b65b_boxFibre i))
          (b65b_boxCentre i).1 (b65b_boxCentre i).2 0) :=
  rou_b65b_pellet_rational_aux

example (i : Fin 12) :
    rou_ratTail (rou_sextic (b65b_boxFibre i)) (b65b_boxCentre i).1 (b65b_boxCentre i).2
        (1/10000) 1 ^ 2 <
      rou_normSq (rou_shift (rou_sextic (b65b_boxFibre i))
        (b65b_boxCentre i).1 (b65b_boxCentre i).2 1) * (1/10000) ^ 2 :=
  (rou_b65b_pellet_rational i).1

/-- Each certified box contains exactly one root of its own sextic.
Source: B65-BRAIDCERT checker part A; JSON boxes; G32 v0.16, §5.2; implication from
`rou_pellet_one` at radii `h` and `3h/2`, `rou_b65b_pellet_rational` and the inclusions
`D(c, h) ⊆ square ⊆ D(c, 3h/2)`. Former signature of `b65b_isolating_boxes`, archived in
docs/specs/BraidCertificate.md. -/
theorem rou_b65b_isolating_boxes :
    ∀ i : Fin 12, ∃! z : ℂ,
      |z.re - ((b65b_boxCentre i).1 : ℝ)| < (1/10000 : ℝ) ∧
      |z.im - ((b65b_boxCentre i).2 : ℝ)| < (1/10000 : ℝ) ∧
      b65r_P (b65b_boxFibre i) z = 0 :=
  rou_b65b_isolating_boxes_aux

example (i : Fin 12) : ∃! z : ℂ,
    |z.re - ((b65b_boxCentre i).1 : ℝ)| < (1/10000 : ℝ) ∧
    |z.im - ((b65b_boxCentre i).2 : ℝ)| < (1/10000 : ℝ) ∧
    b65r_P (b65b_boxFibre i) z = 0 :=
  rou_b65b_isolating_boxes i

/-! ## Satisfiable-instance checks

Each general hypothesis holds for an explicit polynomial of positive degree with a nonzero
constant term, and the counts involved are nonzero where `rou_pellet_one` predicts one. -/

/-- The Rouché hypothesis holds for `X − 1/2` against `X` on the unit circle. -/
example : ∀ z ∈ Metric.sphere (0 : ℂ) 1,
    ‖((X - C (1/2 : ℂ)) - X).eval z‖ < ‖(X : ℂ[X]).eval z‖ := by
  intro z hz
  rw [mem_sphere_zero_iff_norm] at hz
  simp [hz]
  norm_num

/-- The comparison polynomial `X` has one root in the unit disc: the count is not zero. -/
example : rou_discCount X 0 1 = 1 := by
  classical
  simp [rou_discCount, roots_X, Multiset.filter_singleton]

/-- The one-zero Pellet hypothesis holds for `X − 1/2` at centre `0`, radius `1`. -/
example : rou_pelletTail (X - C (1/2 : ℂ)) 0 1 1 <
    ‖(taylor 0 (X - C (1/2 : ℂ))).coeff 1‖ * 1 := by
  simp [rou_pelletTail, Finset.sum_range_succ, coeff_X, coeff_C]
  norm_num

/-- The no-zero Pellet hypothesis holds for `X + 1` at centre `0`, radius `1/2`. -/
example : rou_pelletTail (X + C (1 : ℂ)) 0 (1/2) 0 <
    ‖(taylor 0 (X + C (1 : ℂ))).coeff 0‖ := by
  simp [rou_pelletTail, Finset.sum_range_succ, coeff_X, coeff_one]
  norm_num

/-- The rational coefficients `rou_sextic ε` are those of `b65r_P ε`. -/
example (ε : ℚ) (z : ℂ) :
    ∑ j : Fin 7, ((rou_sextic ε j : ℚ) : ℂ) * z ^ (j : ℕ) = b65r_P ε z := by
  simp [rou_sextic, b65r_P, Fin.sum_univ_succ]
  ring

/-- The two fibres are swapped by `ε ↦ −2 − ε`, so the no-zero test is on the other sextic. -/
example : ∀ i : Fin 12, -2 - b65b_boxFibre i ≠ b65b_boxFibre i := by decide

/-! ## Chain check toward the braid-certificate marking

The isolating boxes give the root witnesses `p` in the first conjunct of the archived
`b65b_path_lasso_transport` signature (docs/specs/BraidCertificate.md). -/

example : ∃ p : Fin 12 → ℂ, ∀ k : Fin 12,
    |(p (b65b_boxIndex k)).re - ((b65b_boxCentre k).1 : ℝ)| < (1/10000 : ℝ) ∧
    |(p (b65b_boxIndex k)).im - ((b65b_boxCentre k).2 : ℝ)| < (1/10000 : ℝ) ∧
    b65r_P (b65b_boxFibre k) (p (b65b_boxIndex k)) = 0 := by
  have hinj : Function.Injective b65b_boxIndex := by decide
  choose f hf _ using rou_b65b_isolating_boxes
  exact ⟨Function.extend b65b_boxIndex f 0, fun k ↦ by rw [hinj.extend_apply]; exact hf k⟩

end HodgeLean.Foundations.Program
