import HodgeLean.Foundations.AlgebraicGeometry.ComplexTopology.EuclideanTruncation
import HodgeLean.Foundations.Program.SchoenTowerHardt6RbCompactCompatibleTriangulation
import HodgeLean.Foundations.Program.SchoenTowerT11bRefinement

/-! Compact polynomial models using the existing Boolean triangulation interface.
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
open HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.ComplexTopology

def equationFormula {n : ℕ} (q : MvPolynomial (Fin n) ℝ) : s2v_t11b_Formula n :=
  .inter (.nonneg q) (.nonneg (-q))

lemma realize_equationFormula {n : ℕ} (q : MvPolynomial (Fin n) ℝ)
    (y : EuclideanSpace ℝ (Fin n)) :
    y ∈ (equationFormula q).realize ↔ MvPolynomial.eval y q = 0 := by
  simp only [equationFormula, s2v_t11b_Formula.realize, Set.mem_inter_iff,
    Set.mem_setOf_eq, map_neg, neg_nonneg]
  exact ⟨fun h => le_antisymm h.2 h.1, fun h => ⟨h.symm.le, h.le⟩⟩

def realCarrierFormula {n m : ℕ} (a b : Fin m → MvPolynomial (Fin n) ℝ) :
    s2v_t11b_Formula n :=
  .inter (.conjunction (List.ofFn fun j => equationFormula (a j)))
    (.conjunction (List.ofFn fun j => equationFormula (b j)))

lemma realize_realCarrierFormula {n m : ℕ} (a b : Fin m → MvPolynomial (Fin n) ℝ) :
    (realCarrierFormula a b).realize = realPolynomialCarrier a b := by
  ext y
  simp only [realCarrierFormula, s2v_t11b_Formula.realize, Set.mem_inter_iff,
    s2v_t11b_realize_conjunction, List.mem_ofFn, forall_exists_index, forall_apply_eq_imp_iff,
    realize_equationFormula, realPolynomialCarrier, Set.mem_setOf_eq]

def truncationFormula {n m : ℕ} (a b : Fin m → MvPolynomial (Fin n) ℝ)
    (x : EuclideanSpace ℝ (Fin n)) (r : ℝ) : s2v_t11b_Formula n :=
  .inter (realCarrierFormula a b) (.nonneg (radialPolynomial x r))

lemma realize_truncationFormula {n m : ℕ} (a b : Fin m → MvPolynomial (Fin n) ℝ)
    (x : EuclideanSpace ℝ (Fin n)) {r : ℝ} (hr : 0 ≤ r) :
    (truncationFormula a b x r).realize =
      realPolynomialCarrier a b ∩ Metric.closedBall x r := by
  ext y
  change (y ∈ (realCarrierFormula a b).realize ∧
    0 ≤ MvPolynomial.eval y (radialPolynomial x r)) ↔ _
  rw [realize_realCarrierFormula, radialPolynomial_nonneg_iff x y hr]
  rfl

lemma polynomial_truncation_triangulation {n m : ℕ}
    (a b : Fin m → MvPolynomial (Fin n) ℝ)
    (x : EuclideanSpace ℝ (Fin n)) {r : ℝ} (hr : 0 ≤ r) :
    ∃ K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin n)),
      K.faces.Finite ∧ Nonempty
        (↥(realPolynomialCarrier a b ∩ Metric.closedBall x r) ≃ₜ K.space) := by
  let f := truncationFormula a b x r
  have hf : IsCompact f.realize := by
    rw [show f.realize = realPolynomialCarrier a b ∩ Metric.closedBall x r from
      realize_truncationFormula a b x hr]
    exact compact_realPolynomial_truncation a b x r
  obtain ⟨K, hK, h, hmarks, hgraph⟩ :=
    s2v_hardt6rb_compact_compatible_triangulation n f hf
      (Fin.elim0 : Fin 0 → s2v_t11b_Formula n)
  exact ⟨K, hK, ⟨(Homeomorph.setCongr
    (realize_truncationFormula a b x hr).symm).trans h.symm⟩⟩

end HodgeLean.Foundations.ComplexTopology
