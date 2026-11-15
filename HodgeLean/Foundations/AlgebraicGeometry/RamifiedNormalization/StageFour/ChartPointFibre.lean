import HodgeLean.Foundations.AlgebraicGeometry.RegularPairChart
import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.AffineScheme
import Mathlib.Topology.Algebra.Polynomial

noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open Polynomial
namespace AlgebraicGeometry.RamifiedNormalization.StageFour

/-- Evaluation at a prescribed ratio on a regular-pair chart above a centre point. -/
def centreChartEvaluation
    {R : Type} [CommRing R] [Algebra ℂ R]
    (u v : R) (φ : R →ₐ[ℂ] ℂ) (hu : φ u = 0) (hv : φ v = 0) (z : ℂ) :
    RegularPairChart.ring u v →ₐ[ℂ] ℂ := by
  have hrel : φ u = z * φ v := by rw [hu, hv, mul_zero]
  let H := RegularPairChart.universal u v φ.toRingHom z hrel
  let f := Classical.choose H
  have hf := (Classical.choose_spec H).1.1
  refine { f with commutes' := ?_ }
  intro c
  change f (RegularPairChart.coeff u v (algebraMap ℂ R c)) = c
  have he := RingHom.congr_fun hf (algebraMap ℂ R c)
  exact he.trans (φ.commutes c)

/-- The centre-chart evaluation retains the original coefficients and prescribed ratio. -/
theorem centreChartEvaluation_spec
    {R : Type} [CommRing R] [Algebra ℂ R]
    (u v : R) (φ : R →ₐ[ℂ] ℂ) (hu : φ u = 0) (hv : φ v = 0) (z : ℂ) :
    (centreChartEvaluation u v φ hu hv z).toRingHom.comp (RegularPairChart.coeff u v) =
      φ.toRingHom ∧
      centreChartEvaluation u v φ hu hv z (RegularPairChart.ratio u v) = z := by
  exact (Classical.choose_spec (RegularPairChart.universal u v φ.toRingHom z
    (by change φ u = z * φ v; rw [hu, hv, mul_zero]))).1

/-- Every quotient representative evaluates by the original coefficient map and ratio. -/
theorem centreChartEvaluation_mk
    {R : Type} [CommRing R] [Algebra ℂ R]
    (u v : R) (φ : R →ₐ[ℂ] ℂ) (hu : φ u = 0) (hv : φ v = 0)
    (z : ℂ) (p : R[X]) :
    centreChartEvaluation u v φ hu hv z
      (Ideal.Quotient.mk (Ideal.span {C u - X * C v}) p) = p.eval₂ φ.toRingHom z := by
  let ev := centreChartEvaluation u v φ hu hv z
  have hs := centreChartEvaluation_spec u v φ hu hv z
  have he : ev.toRingHom.comp (Ideal.Quotient.mk (Ideal.span {C u - X * C v})) =
      eval₂RingHom φ.toRingHom z := by
    apply Polynomial.ringHom_ext
    · intro r
      exact (RingHom.congr_fun hs.1 r).trans (eval₂_C φ.toRingHom z).symm
    · exact hs.2.trans (eval₂_X φ.toRingHom z).symm
  exact RingHom.congr_fun he p

/-- The prescribed centre-chart evaluations vary continuously with the literal ratio. -/
theorem continuous_centreChartEvaluation
    {R : Type} [CommRing R] [Algebra ℂ R]
    (u v : R) (φ : R →ₐ[ℂ] ℂ) (hu : φ u = 0) (hv : φ v = 0) :
    Continuous (centreChartEvaluation u v φ hu hv) := by
  rw [continuous_induced_rng]
  refine continuous_pi fun a => ?_
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
  change Continuous (fun z : ℂ => centreChartEvaluation u v φ hu hv z
    (Ideal.Quotient.mk (Ideal.span {C u - X * C v}) p))
  simp_rw [centreChartEvaluation_mk]
  exact p.continuous_eval₂ φ.toRingHom

/-- The actual scalar-preserving centre-chart point fibre has its literal ratio as a homeomorphism. -/
def centreChartPointHomeomorph
    {R : Type} [CommRing R] [Algebra ℂ R]
    (u v : R) (φ : R →ₐ[ℂ] ℂ) (hu : φ u = 0) (hv : φ v = 0) :
    {p : RegularPairChart.ring u v →ₐ[ℂ] ℂ //
      p.toRingHom.comp (RegularPairChart.coeff u v) = φ.toRingHom} ≃ₜ ℂ where
  toFun p := p.val (RegularPairChart.ratio u v)
  invFun z := ⟨centreChartEvaluation u v φ hu hv z,
    (centreChartEvaluation_spec u v φ hu hv z).1⟩
  left_inv p := by
    apply Subtype.ext
    apply AlgHom.coe_ringHom_injective
    have hrel : φ.toRingHom u = p.val (RegularPairChart.ratio u v) * φ.toRingHom v := by
      change φ u = p.val (RegularPairChart.ratio u v) * φ v
      rw [hu, hv, mul_zero]
    exact (RegularPairChart.universal u v φ.toRingHom _ hrel).unique
      (centreChartEvaluation_spec u v φ hu hv _)
      ⟨p.property, rfl⟩
  right_inv z := (centreChartEvaluation_spec u v φ hu hv z).2
  continuous_toFun := (ComplexPoint.continuous_affineAlgebraHom_apply
    (RegularPairChart.ring u v) (RegularPairChart.ratio u v)).comp continuous_subtype_val
  continuous_invFun := (continuous_centreChartEvaluation u v φ hu hv).subtype_mk _

end AlgebraicGeometry.RamifiedNormalization.StageFour
