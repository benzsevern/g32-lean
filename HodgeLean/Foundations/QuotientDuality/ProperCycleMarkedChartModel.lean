import HodgeLean.Foundations.QuotientDuality.ProperCycleMarkedPolynomialModel
import HodgeLean.Foundations.AlgebraicGeometry.ComplexTopology.MarkedDefs

/-! # Actual marked compact models in the original chart domain -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open HodgeLean.Foundations.ComplexTopology
namespace HodgeLean.Foundations.QuotientDuality

/-- Restrict an actual homeomorphism onto a subset by a further target condition.
Source: Munkres, Topology, section 18, restrictions of homeomorphisms.
HC no distance; AV milestone no distance. -/
def properCycle_homeomorph_restrict_inter {A B : Type*} [TopologicalSpace A]
    [TopologicalSpace B] {S : Set B} (e : A ≃ₜ S) (T : Set B) :
    {a : A | (e a).val ∈ T} ≃ₜ ↥(S ∩ T) where
  toFun z := ⟨(e z.val).val, (e z.val).property, z.property⟩
  invFun z := ⟨e.symm ⟨z.val, z.property.1⟩, by simpa using z.property.2⟩
  left_inv z := by apply Subtype.ext; exact e.symm_apply_apply z.val
  right_inv z := by
    apply Subtype.ext
    change (e (e.symm ⟨z.val, z.property.1⟩)).val = z.val
    exact congrArg (fun t : S => t.val) (e.apply_symm_apply ⟨z.val, z.property.1⟩)
  continuous_toFun := (continuous_subtype_val.comp (e.continuous.comp continuous_subtype_val)).subtype_mk _
  continuous_invFun := (e.symm.continuous.comp (continuous_subtype_val.subtype_mk _)).subtype_mk _

/-- A specified polynomial subset chart has an actual compact finite model retaining every original mark.
Source: Bochnak, Coste and Roy, Real Algebraic Geometry, theorem 9.2.1;
Munkres, Topology, section 18.
HC no distance; AV milestone no distance. -/
lemma properCycle_marked_chart_truncation {X : Type} [TopologicalSpace X] {r : ℕ}
    {D : Fin r → Set X} (c : Marked.SubsetChart X D)
    (x : EuclideanSpace ℝ (Fin (c.n + c.n))) (R : ℝ) (hR : 0 ≤ R) :
    ∃ (K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin (c.n + c.n)))),
      K.faces.Finite ∧
      ∃ h : K.space ≃ₜ {z : c.domain |
          complexEuclideanCoordinates c.n (c.coordinates z).val ∈ Metric.closedBall x R},
        ∀ j : Fin r, ∃ L : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin (c.n + c.n))),
          L.faces.Finite ∧ L.faces ⊆ K.faces ∧
            ∀ z : K.space, (h z).val.val ∈ D j ↔ z.val ∈ L.space := by
  obtain ⟨a, b, hab, K, hK, h, hmarks⟩ :=
    properCycle_marked_polynomial_truncation c.equations c.count c.marked x R hR
  let ec : c.domain ≃ₜ realPolynomialCarrier a b :=
    c.coordinates.trans ((complexEuclideanCoordinates c.n).sets (by ext z; exact hab z))
  let et := properCycle_homeomorph_restrict_inter ec (Metric.closedBall x R)
  let h' := h.trans et.symm
  refine ⟨K, hK, h', ?_⟩
  intro j
  obtain ⟨L, hL, hLK, hLmark⟩ := hmarks j
  refine ⟨L, hL, hLK, ?_⟩
  intro z
  have hz : (c.coordinates (h' z).val).val =
      (complexEuclideanCoordinates c.n).symm (h z).val := by
    change (c.coordinates (c.coordinates.symm _)).val = _
    rw [Homeomorph.apply_symm_apply]
    rfl
  refine (c.membership (h' z).val j).trans ?_
  change (∀ k, MvPolynomial.eval (c.coordinates (h' z).val).val (c.marked j k) = 0) ↔ _
  rw [hz]
  exact hLmark z

end HodgeLean.Foundations.QuotientDuality
