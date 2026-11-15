import HodgeLean.Foundations.QuotientDuality.ProperCycleIntrinsicClass

/-! # Normalization and homology line of the specified intrinsic class -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicTopology.Singular
open HodgeLean.Adapters HodgeLean.Foundations.Program HodgeLean.Foundations.Analytic
namespace HodgeLean.Foundations.QuotientDuality

/-- The specified intrinsic class spans the original ordinary top homology with unique rational coefficient.
Source: Bredon, Sheaf Theory, second edition, V.9; properCycle_intrinsic_extension_aux.
HC no distance; AV milestone no distance. -/
lemma properCycle_intrinsic_class_generates
    (V : Over (Spec ↧ℂ)) [IsIntegral V.left] [IsProjective V.hom]
    (d : ℕ) (hdim : topologicalKrullDim V.left = (d : ℕ)) :
    Function.Bijective (LinearMap.toSpanSingleton ℚ
      (Homology ℚ (a3b4_an V.hom) (2 * d)) (properCycle_intrinsic_class V d hdim)) :=
  (properCycle_intrinsic_extension_aux V d hdim).exists.choose_spec.2

/-- The selected intrinsic class has the original complex normalization in every actual holomorphic chart.
Source: Bredon, Sheaf Theory, second edition, V.9; properCycle_intrinsic_extension_aux.
HC no distance; AV milestone no distance. -/
lemma properCycle_intrinsic_class_chart
    (V : Over (Spec ↧ℂ)) [IsIntegral V.left] [IsProjective V.hom]
    (d : ℕ) (hdim : topologicalKrullDim V.left = (d : ℕ))
    (e : OpenPartialHomeomorph (ComplexPoint V) (Fin d → ℂ))
    (he : ∀ i, (f4_analytification V).IsHolFun (fun z : e.source => e z i))
    (x : ComplexPoint V) (hx : x ∈ e.source) :
    localOrientation (a3b4_an V.hom) (2 * d) (properCycle_intrinsic_class V d hdim) x =
      localClassOfChart d e x hx :=
  (properCycle_intrinsic_extension_aux V d hdim).exists.choose_spec.1 e he x hx

/-- The specified intrinsic top class identifies the actual ordinary top homology with one rational dimension.
Source: Bredon, Sheaf Theory, second edition, V.9; properCycle_intrinsic_class_generates.
HC no distance; AV milestone no distance. -/
lemma properCycle_intrinsic_homology_finrank
    (V : Over (Spec ↧ℂ)) [IsIntegral V.left] [IsProjective V.hom]
    (d : ℕ) (hdim : topologicalKrullDim V.left = (d : ℕ)) :
    Module.finrank ℚ (Homology ℚ (a3b4_an V.hom) (2 * d)) = 1 := by
  let E := LinearEquiv.ofBijective
    (LinearMap.toSpanSingleton ℚ (Homology ℚ (a3b4_an V.hom) (2 * d))
      (properCycle_intrinsic_class V d hdim)) (properCycle_intrinsic_class_generates V d hdim)
  rw [← E.finrank_eq]
  exact Module.finrank_self ℚ

end HodgeLean.Foundations.QuotientDuality
