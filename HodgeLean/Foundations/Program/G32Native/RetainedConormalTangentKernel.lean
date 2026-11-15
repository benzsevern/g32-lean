import HodgeLean.Foundations.Program.G32Native.RetainedConormalTangentAnnihilation
import HodgeLean.Foundations.Program.G32Native.ConormalEvaluationSurjectivity

/-! # The original conormal evaluation kernel is the immersion tangent range

The inclusion comes from differentiated original equations. The retained
transverse rank and the immersion dimension make that inclusion an equality.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry Topology
namespace HodgeLean.Foundations.TubularEuler
open BundleThom

/-- The evaluation kernel of the retained conormal is exactly the range of the
original immersion derivative, with its original affine presentation fixed.
Source: Hartshorne, Algebraic Geometry, II.8, tangent-conormal sequence;
rank-nullity and `retainedConormal_comp_immersion_derivative_zero`.
HC no distance; AV milestone no distance. -/
theorem retained_conormal_kernel_eq_tangent_range
    (X Y : Over (Spec ↧ℂ)) (j : Y ⟶ X) [IsClosedImmersion j.left]
    (m k : ℕ) [SmoothOfRelativeDimension (m + k) X.hom] [SmoothOfRelativeDimension m Y.hom]
    (A : X.left.Opens) (hA : IsAffineOpen A) (x : ComplexPoint Y)
    (hx : x ∈ Point.overOpen (j.left ⁻¹ᵁ A)) (z : ComplexPoint X)
    (hz : Point.map j x ∈ (chartAt (Fin (m + k) → ℂ) z).source)
    (hD : Function.Injective (retainedAffineConormalDifferential X Y j (m + k) A hA x hx z hz))
    (hRank : Module.finrank ℂ
      (retainedAffineConormalDifferential X Y j (m + k) A hA x hx z hz).range = k)
    (S : (Fin m → ℂ) →L[ℂ] (Fin (m + k) → ℂ))
    (hS : HasFDerivAt (fun b => (chartAt (Fin (m + k) → ℂ) z)
        (Point.map j ((chartAt (Fin m → ℂ) x).symm b))) S
      ((chartAt (Fin m → ℂ) x) x))
    (hSi : Function.Injective S) :
    let D := retainedAffineConormalDifferential X Y j (m + k) A hA x hx z hz
    let T : (Fin (m + k) → ℂ) →ₗ[ℂ] i1_normalFibre j.left x :=
      ((ContinuousLinearMap.coeLM ℂ).comp D).flip
    T.ker = S.toLinearMap.range := by
  let D := retainedAffineConormalDifferential X Y j (m + k) A hA x hx z hz
  let T : (Fin (m + k) → ℂ) →ₗ[ℂ] i1_normalFibre j.left x :=
    ((ContinuousLinearMap.coeLM ℂ).comp D).flip
  change T.ker = S.toLinearMap.range
  letI := FiniteDimensional.of_injective D hD
  have hC : Module.finrank ℂ (i1_conormalFibre j.left x) = k :=
    (LinearMap.finrank_range_of_inj hD).symm.trans hRank
  have hN : Module.finrank ℂ (i1_normalFibre j.left x) = k := by
    change Module.finrank ℂ (Module.Dual ℂ (i1_conormalFibre j.left x)) = k
    rw [Subspace.dual_finrank_eq, hC]
  have hT : Function.Surjective T := by
    intro n
    obtain ⟨v, hv⟩ := injective_covector_evaluation_surjective D hD n
    exact ⟨v, LinearMap.ext hv⟩
  have hle : S.toLinearMap.range ≤ T.ker := by
    rintro _ ⟨v, rfl⟩
    apply LinearMap.ext
    intro a
    have h := retainedConormal_comp_immersion_derivative_zero X Y j (m + k) m
      A hA x hx z hz S hS a
    exact congrArg (fun L : (Fin m → ℂ) →L[ℂ] ℂ => L v) h
  have hnull := T.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hT, finrank_top, hN] at hnull
  have hdim : Module.finrank ℂ T.ker = m := by
    simp only [Module.finrank_pi, Module.finrank_self, Fintype.card_fin, mul_one] at hnull
    omega
  apply (Submodule.eq_of_le_of_finrank_eq hle ?_).symm
  rw [LinearMap.finrank_range_of_inj hSi, hdim]
  simp

#print axioms retained_conormal_kernel_eq_tangent_range

end HodgeLean.Foundations.TubularEuler
