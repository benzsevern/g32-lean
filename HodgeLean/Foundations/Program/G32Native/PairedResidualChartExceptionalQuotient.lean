import HodgeLean.Foundations.AlgebraicGeometry.RegularPairChart
import HodgeLean.Foundations.Program.G32Native.PairedResidualIdealAlgebra
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Monic

/-! # The exceptional quotient of a regular-pair chart -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Polynomial AlgebraicGeometry.RegularPairChart
namespace HodgeLean.Foundations.Program.G32Native.FibreC

/-- Modulo the exceptional denominator, the ratio is a free polynomial coordinate over the centre. -/
theorem residual_chart_exceptional_quotient {R : Type*} [CommRing R] (u v : R) :
    ∃ f : ring u v →+* Polynomial (R ⧸ Ideal.span {u, v}),
      RingHom.ker f = Ideal.span {coeff u v v} ∧
      f (ratio u v) = X ∧
      ∀ r, f (coeff u v r) = C (Ideal.Quotient.mk (Ideal.span {u, v}) r) := by
  let I : Ideal R := Ideal.span {u, v}
  let J : Ideal (Polynomial R) := Ideal.span {C u - X * C v}
  let F := mapRingHom (Ideal.Quotient.mk I)
  have hu : Ideal.Quotient.mk I u = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
  have hv : Ideal.Quotient.mk I v = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
  have hF : J ≤ RingHom.ker F := by
    apply Ideal.span_le.mpr
    rintro p rfl
    change F (C u - X * C v) = 0
    simp [F, hu, hv]
  let f := Ideal.Quotient.lift J F (fun p hp => hF hp)
  have hk : RingHom.ker f = Ideal.span {coeff u v v} := by
    change RingHom.ker (Ideal.Quotient.lift J F (fun p hp => hF hp)) = _
    rw [Ideal.ker_quotient_lift F hF]
    change (RingHom.ker (mapRingHom (Ideal.Quotient.mk I))).map (Ideal.Quotient.mk J) = _
    rw [Polynomial.ker_mapRingHom, Ideal.mk_ker, Ideal.map_map]
    change I.map (coeff u v) = Ideal.span {coeff u v v}
    rw [Ideal.map_span, Set.image_pair]
    exact centre_principal u v
  refine ⟨f, hk, ?_, ?_⟩
  · change (mapRingHom (Ideal.Quotient.mk I)) X = X
    exact map_X _
  · intro r
    change (mapRingHom (Ideal.Quotient.mk I)) (C r) = C (Ideal.Quotient.mk I r)
    exact map_C _

#print axioms residual_chart_exceptional_quotient
end HodgeLean.Foundations.Program.G32Native.FibreC
