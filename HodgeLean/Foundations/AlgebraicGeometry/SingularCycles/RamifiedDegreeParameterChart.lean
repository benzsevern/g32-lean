import HodgeLean.Foundations.AlgebraicGeometry.SingularCycles.RamifiedDegreeAffineChart
import HodgeLean.Foundations.AlgebraicGeometry.SingularCycles.RamifiedDegreeAffineParameters
import HodgeLean.Foundations.AlgebraicGeometry.SingularCycles.RamifiedDegreeParameters

/-! # Centered regular parameter charts at smooth complex points

The witnesses combine affine étale coordinates, their actual holomorphic
point chart, and their regular maximal-ideal generators in the target stalk.
HC no distance; AV milestone no distance.
-/

noncomputable section
open CategoryTheory AlgebraicGeometry HodgeLean.Adapters
set_option maxHeartbeats 400000
namespace AlgebraicGeometry.SingularCycles

theorem exists_centered_regular_parameter_chart
    (X : Over (Spec ↧ℂ)) [Smooth X.hom]
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    (d : ℕ) (e₀ : OpenPartialHomeomorph (ComplexPoint X) ((Fin 0 → ℂ) × (Fin d → ℂ)))
    (he₀ : a3b4_IsHolChart X.hom e₀) (x : ComplexPoint X) (hx₀ : x ∈ (pointChart e₀).source) :
    ∃ (U : X.left.Opens) (_hU : IsAffineOpen U) (hxU : x.underlying ∈ U)
      (g : Fin d → Γ(X.left, U))
      (e : OpenPartialHomeomorph (ComplexPoint X) ((Fin 0 → ℂ) × (Fin d → ℂ))),
      a3b4_IsHolChart X.hom e ∧ x ∈ (pointChart e).source ∧ pointChart e x = 0 ∧
      (pointChart e).source ⊆ Point.overOpen (X := X) U ∧
      (∀ y ∈ (pointChart e).source, ∀ k, pointChart e y k = Point.evaluate U (g k) y) ∧
      RingTheory.Sequence.IsRegular (X.left.presheaf.stalk x.underlying)
        (List.ofFn fun k => X.left.presheaf.germ U x.underlying hxU (g k)) ∧
      Ideal.ofList (List.ofFn fun k => X.left.presheaf.germ U x.underlying hxU (g k)) =
        IsLocalRing.maximalIdeal (X.left.presheaf.stalk x.underlying) := by
  obtain ⟨U, hU, hxU, φ, hφ⟩ := exists_affine_etale_point_coordinates X d e₀ he₀ x hx₀
  letI : Algebra ℂ Γ(X.left, U) := overSpecAlgebra X U
  let u := a3b4a_gysin_affine_evaluation X.hom U x hxU
  let ψ := centeredCoordinateHom φ u
  have hψ : ψ.toRingHom.Etale := centeredCoordinateHom_etale φ u hφ
  have hzero (k : Fin d) : Point.evaluate U (ψ (MvPolynomial.X k)) x = 0 := by
    have hh := congrArg (fun v : MvPolynomial (Fin d) ℂ →ₐ[ℂ] ℂ => v (MvPolynomial.X k))
      (centeredCoordinateHom_evaluation φ u)
    change u (ψ (MvPolynomial.X k)) = MvPolynomial.aeval (0 : Fin d → ℂ) (MvPolynomial.X k) at hh
    rw [MvPolynomial.aeval_X] at hh
    exact (Point.evaluationHom_apply (X := X) U ⟨x, hxU⟩ (ψ (MvPolynomial.X k))).symm.trans hh
  obtain ⟨e, he, hxe, he0, hsource, hvalues⟩ :=
    affine_etale_holomorphic_point_chart X U hU x hxU d ψ hψ hzero
  refine ⟨U, hU, hxU, (fun k => ψ (MvPolynomial.X k)), e,
    he, hxe, he0, hsource, hvalues, ?_, ?_⟩
  · exact affine_etale_parameter_germs_are_regular X d e₀ he₀ x hx₀ U hU hxU ψ hψ hzero
  · exact affine_etale_parameter_germs_generate_maximal X U hU x hxU d ψ hψ hzero

end AlgebraicGeometry.SingularCycles
