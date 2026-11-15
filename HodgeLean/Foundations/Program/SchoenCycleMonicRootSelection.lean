import HodgeLean.Foundations.Program.SchoenCycleCanonicalFamily
import Mathlib.RingTheory.Polynomial.Vieta

/-! # Small exact root selections near a total monic collision -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 400000
open Filter Topology Polynomial MvPolynomial
open scoped BigOperators Classical
open HodgeLean.Foundations.AnalyticDivisorAlgebraic5
namespace HodgeLean.Foundations.Program

/-- Choose a full exact root tuple of the monic polynomial with the specified coefficients.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.3, printed pp. 13–14;
ACGH, Geometry of Algebraic Curves I, Chapter I, §3. -/
def s2e_monicCoefficientRootSelection (d : ℕ) (a : Fin d → ℂ) : Fin d → ℂ :=
  (s2e_monic_polynomial_exists_root_tuple
    (monicPoly (fun j (z : Fin d → ℂ) => z j) a)
    (spec_monicPoly_aux (fun j (z : Fin d → ℂ) => z j) a).1
    (spec_monicPoly_aux (fun j (z : Fin d → ℂ) => z j) a).2.1).choose

/-- Every selected root tuple presents the exact prescribed monic polynomial.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.3, printed pp. 13–14;
ACGH, Geometry of Algebraic Curves I, Chapter I, §3. -/
theorem s2e_monicCoefficientRootSelection_spec (d : ℕ) (a : Fin d → ℂ) :
    monicPoly (fun j (z : Fin d → ℂ) => z j) a =
      ∏ i, (Polynomial.X - Polynomial.C (s2e_monicCoefficientRootSelection d a i)) :=
  (s2e_monic_polynomial_exists_root_tuple
    (monicPoly (fun j (z : Fin d → ℂ) => z j) a)
    (spec_monicPoly_aux (fun j (z : Fin d → ℂ) => z j) a).1
    (spec_monicPoly_aux (fun j (z : Fin d → ℂ) => z j) a).2.1).choose_spec

/-- Below its leading degree, the prescribed monic polynomial has exactly the input coefficient vector.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.3, printed pp. 13–14;
ACGH, Geometry of Algebraic Curves I, Chapter I, §3. -/
theorem s2e_monicCoefficientPolynomial_coeff (d : ℕ) (a : Fin d → ℂ) (j : Fin d) :
    (monicPoly (fun i (z : Fin d → ℂ) => z i) a).coeff j = a j := by
  classical
  simp [monicPoly, Polynomial.coeff_add, Polynomial.coeff_X_pow,
    Polynomial.coeff_C_mul, Nat.ne_of_lt j.isLt, Fin.val_inj]

/-- Every coefficient of a full root tuple is the signed elementary symmetric polynomial in those exact roots.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.3, printed pp. 13–14;
ACGH, Geometry of Algebraic Curves I, Chapter I, §3. -/
theorem s2e_rootTuple_signed_coefficient (d : ℕ) (z : Fin d → ℂ) (j : Fin d) :
    (∏ i, (Polynomial.X - Polynomial.C (z i))).coeff j =
      (-1 : ℂ) ^ (d - j.val) *
        MvPolynomial.aeval z (MvPolynomial.esymm (Fin d) ℂ (d - j.val)) := by
  rw [MvPolynomial.aeval_esymm_eq_multiset_esymm]
  have h := Multiset.prod_X_sub_C_coeff
    ((Finset.univ : Finset (Fin d)).val.map z) (k := j.val)
    (by simpa only [Multiset.card_map, Finset.card_val, Finset.card_univ,
      Fintype.card_fin] using j.isLt.le)
  simpa only [Multiset.card_map, Finset.card_val, Finset.card_univ, Fintype.card_fin,
    Multiset.map_map, Function.comp_def, Finset.prod] using h

/-- The selected exact roots recover every prescribed signed block coefficient.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.3, printed pp. 13–14;
ACGH, Geometry of Algebraic Curves I, Chapter I, §3. -/
theorem s2e_monicCoefficientRootSelection_coefficient (d : ℕ) (a : Fin d → ℂ) (j : Fin d) :
    (-1 : ℂ) ^ (d - j.val) * MvPolynomial.aeval (s2e_monicCoefficientRootSelection d a)
      (MvPolynomial.esymm (Fin d) ℂ (d - j.val)) = a j := by
  rw [← s2e_rootTuple_signed_coefficient,
    ← s2e_monicCoefficientRootSelection_spec, s2e_monicCoefficientPolynomial_coeff]

/-- The entire selected root tuple tends to the total collision as its coefficient vector tends to zero.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.3, printed pp. 13–14;
ACGH, Geometry of Algebraic Curves I, Chapter I, §3. -/
theorem s2e_monicCoefficientRootSelection_tendsto_zero (d : ℕ) :
    Tendsto (s2e_monicCoefficientRootSelection d) (𝓝 0) (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hc (j : Fin d) : ContinuousAt (fun z : Fin d → ℂ => z j) 0 :=
    (continuous_apply j).continuousAt
  filter_upwards [s2e_monic_rootTuples_eventually_small
    (fun j (z : Fin d → ℂ) => z j) hc (fun _ => rfl) hε] with a ha
  exact ha (s2e_monicCoefficientRootSelection d a) (s2e_monicCoefficientRootSelection_spec d a)

/-- At the zero coefficient vector the selected exact root tuple is exactly the total collision.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.3, printed pp. 13–14;
ACGH, Geometry of Algebraic Curves I, Chapter I, §3. -/
theorem s2e_monicCoefficientRootSelection_zero (d : ℕ) :
    s2e_monicCoefficientRootSelection d 0 = 0 := by
  apply pure_le_nhds_iff.mp
  have h := (s2e_monicCoefficientRootSelection_tendsto_zero d).mono_left
    (pure_le_nhds (0 : Fin d → ℂ))
  simpa only [Tendsto, Filter.map_pure] using h

end HodgeLean.Foundations.Program
