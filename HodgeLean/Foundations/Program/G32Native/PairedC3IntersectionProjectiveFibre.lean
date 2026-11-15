import HodgeLean.Foundations.Program.G32Native.PairedC3IntersectionAffineFibre
import HodgeLean.Foundations.Program.G32Native.PairedC3ProjectiveChartOpen
import HodgeLean.Foundations.Program.G32Native.PairedC3MarkedChartInclusion

/-! # The intersection quotient in the projective target -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry Polynomial
open AlgebraicGeometry.RamifiedNormalization.StageFour
namespace HodgeLean.Foundations.Program.G32Native

/-- The original intersection quotient is the marked fibre in either
projective chart when its ideal is the normalized parameter minus one. -/
theorem pairedC3_intersection_projective_fibre
    (B : Type) [CommRing B] (N J : Ideal B) [Algebra ℂ (B ⧸ J)]
    (i : Fin 2) (z : B ⧸ J)
    (hN : N.map (Ideal.Quotient.mk J) = Ideal.span {z - 1}) :
    let c := algebraMap ℂ (B ⧸ J)
    let q := Ideal.Quotient.factor (show J ≤ N ⊔ J from le_sup_right)
    IsPullback (Spec.map (CommRingCat.ofHom (q.comp c)))
      (Spec.map (CommRingCat.ofHom q))
      (projectiveLineChart i (1 : ℂ)).left (projectiveLineChart i z).left := by
  let c := algebraMap ℂ (B ⧸ J)
  let q := Ideal.Quotient.factor (show J ≤ N ⊔ J from le_sup_right)
  have hs := pairedC3_intersection_affine_fibre ℂ B N J c z 1
    (by simpa only [map_one] using hN)
  letI := pairedC3_projective_chart_open i
  have h := pairedC3_marked_square_chart_inclusion _ _ _ _
    (projectiveLineChart i (Polynomial.X : Polynomial ℂ)).left hs
  have hz := pairedC3_projective_chart_restriction (aeval z) i (Polynomial.X : Polynomial ℂ)
  have h1 := pairedC3_projective_chart_restriction
    (aeval (1 : ℂ)) i (Polynomial.X : Polynomial ℂ)
  simp only [aeval_X] at hz h1
  have he : (aeval (1 : ℂ) : Polynomial ℂ →ₐ[ℂ] ℂ).toRingHom = evalRingHom 1 := by
    apply Polynomial.ringHom_ext
    · intro a
      simp only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, aeval_C,
        Algebra.algebraMap_self, RingHom.id_apply, coe_evalRingHom, eval_C]
    · simp only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, aeval_X,
        coe_evalRingHom, eval_X]
  rw [he] at h1
  change Spec.map (CommRingCat.ofHom (eval₂RingHom c z)) ≫
    (projectiveLineChart i (Polynomial.X : Polynomial ℂ)).left =
      (projectiveLineChart i z).left at hz
  rw [h1, hz] at h
  exact h

#print axioms pairedC3_intersection_projective_fibre
end HodgeLean.Foundations.Program.G32Native
