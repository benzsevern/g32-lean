import HodgeLean.Foundations.AlgebraicGeometry.ComplexTopology.CompactModel
import HodgeLean.Foundations.Program.SchoenTowerHardt6RbClosedMarkSubcomplex

/-! # Actual compact polynomial models with simultaneous closed subcomplex marks -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open HodgeLean.Foundations.Program HodgeLean.Foundations.ComplexTopology
namespace HodgeLean.Foundations.QuotientDuality

/-- A compact polynomial truncation has one actual finite triangulation retaining all specified complex polynomial zero loci.
Source: Bochnak, Coste and Roy, Real Algebraic Geometry, theorem 9.2.1;
Coste, An Introduction to Semialgebraic Geometry, theorem 4.4.
HC no distance; AV milestone no distance. -/
lemma properCycle_marked_polynomial_truncation {n m r : ℕ}
    (p : Fin m → MvPolynomial (Fin n) ℂ)
    (c : Fin r → ℕ) (q : (j : Fin r) → Fin (c j) → MvPolynomial (Fin n) ℂ)
    (x : EuclideanSpace ℝ (Fin (n + n))) (R : ℝ) (hR : 0 ≤ R) :
    ∃ a b : Fin m → MvPolynomial (Fin (n + n)) ℝ,
      (∀ z : Fin n → ℂ, z ∈ zeroSet p ↔
        complexEuclideanCoordinates n z ∈ realPolynomialCarrier a b) ∧
      ∃ (K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin (n + n)))),
        K.faces.Finite ∧
        ∃ h : K.space ≃ₜ ↥(realPolynomialCarrier a b ∩ Metric.closedBall x R : Set (EuclideanSpace ℝ (Fin (n + n)) )),
          ∀ j : Fin r, ∃ D : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin (n + n))),
            D.faces.Finite ∧ D.faces ⊆ K.faces ∧
              ∀ z : K.space,
                (∀ k, MvPolynomial.eval
                  ((complexEuclideanCoordinates n).symm (h z).val) (q j k) = 0) ↔
                  z.val ∈ D.space := by
  obtain ⟨a, b, hab⟩ := real_equations_in_euclidean_coordinates p
  choose qa qb hq using fun j => real_equations_in_euclidean_coordinates (q j)
  let f := truncationFormula a b x R
  let g : Fin r → s2v_t11b_Formula (n + n) := fun j => realCarrierFormula (qa j) (qb j)
  have hf : IsCompact f.realize := by
    rw [show f.realize = realPolynomialCarrier a b ∩ Metric.closedBall x R from
      realize_truncationFormula a b x hR]
    exact compact_realPolynomial_truncation a b x R
  obtain ⟨K, hK, h0, hmarks, _⟩ :=
    s2v_hardt6rb_compact_compatible_triangulation (n + n) f hf g
  let h : K.space ≃ₜ ↥(realPolynomialCarrier a b ∩ Metric.closedBall x R : Set (EuclideanSpace ℝ (Fin (n + n)) )) :=
    h0.trans (Homeomorph.setCongr (realize_truncationFormula a b x hR))
  refine ⟨a, b, hab, K, hK, h, ?_⟩
  intro j
  obtain ⟨S, hS, hsel⟩ := hmarks j
  have hg : IsClosed (g j).realize := by
    rw [show (g j).realize = realPolynomialCarrier (qa j) (qb j) from
      realize_realCarrierFormula (qa j) (qb j)]
    exact isClosed_realPolynomialCarrier (qa j) (qb j)
  have hb : IsClosed (Subtype.val ⁻¹' (g j).realize : Set f.realize) :=
    hg.preimage continuous_subtype_val
  obtain ⟨D, hD, hDK, hDmark⟩ :=
    s2v_hardt6rb_closed_mark_subcomplex K hK f.realize (g j).realize h0 hb S hS hsel
  refine ⟨D, hD, hDK, ?_⟩
  intro z
  have hp := hq j ((complexEuclideanCoordinates n).symm (h z).val)
  rw [Homeomorph.apply_symm_apply] at hp
  have hgz : (∀ k, MvPolynomial.eval
      ((complexEuclideanCoordinates n).symm (h z).val) (q j k) = 0) ↔ (h z).val ∈ (g j).realize := by
    rw [show (g j).realize = realPolynomialCarrier (qa j) (qb j) from
      realize_realCarrierFormula (qa j) (qb j)]
    exact hp
  exact hgz.trans (hDmark z)

end HodgeLean.Foundations.QuotientDuality
