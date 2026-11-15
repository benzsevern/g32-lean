import HodgeLean.Foundations.Program.SchoenTowerL1aSectionParameterRestriction

/-! Realization of localized coordinates on actual principal affine charts.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program
attribute [local instance] overSpecAlgebra

/-- A localized etale coordinate family and its actual principal branch equations restrict to an affine chart containing the specified point. -/
theorem s2v_l1b_principal_evaluation_chart
    (X : Over (Spec ↧ℂ)) [IsAffine X.left]
    {ι : Type} (c : ι → Γ(X.left, ⊤)) (s : Fin 2 → ι)
    (I : Fin 2 → X.left.IdealSheafData)
    (hI : ∀ k, (I k).ideal ⟨⊤, isAffineOpen_top X.left⟩ = Ideal.span {c (s k)})
    (p : ComplexPoint X) (d : Γ(X.left, ⊤))
    (hd : Point.evaluate ⊤ d p ≠ 0)
    (hEt : (MvPolynomial.eval₂Hom (algebraMap ℂ (Localization.Away d))
      (fun i => algebraMap Γ(X.left, ⊤) (Localization.Away d) (c i))).Etale) :
    ∃ (U : Over (Spec ↧ℂ)) (hU : IsAffine U.left) (j : U ⟶ X)
      (p' : ComplexPoint U),
      IsOpenImmersion j.left ∧ Point.map j p' = p ∧
      (MvPolynomial.eval₂Hom U.hom.appTop.hom (fun i => j.left.appTop.hom (c i))).Etale ∧
      ∀ k, ((I k).comap j.left).ideal ⟨⊤, @isAffineOpen_top _ hU⟩ =
        Ideal.span {j.left.appTop.hom (c (s k))} := by
  let O := X.left.basicOpen d
  let U := ComplexPoint.openScheme X O
  let j : U ⟶ X := ComplexPoint.openInclusion X O
  have hp : p.underlying ∈ O :=
    (Point.mem_overOpen_basicOpen_iff_evaluate_ne_zero d p
      (show p ∈ Point.overOpen ⊤ from trivial)).mpr hd
  let p' := ComplexPoint.asOpenPoint X O p hp
  letI : IsAffine U.left := (isAffineOpen_top X.left).basicOpen d
  have hcomp : ((algebraMap Γ(X.left, ⊤) (Localization.Away d)).comp
      (MvPolynomial.aeval (R := ℂ) c).toRingHom) =
      MvPolynomial.eval₂Hom (algebraMap ℂ (Localization.Away d))
        (fun i => algebraMap Γ(X.left, ⊤) (Localization.Away d) (c i)) := by
    apply MvPolynomial.ringHom_ext
    · intro t
      change algebraMap Γ(X.left, ⊤) (Localization.Away d)
        ((MvPolynomial.aeval (R := ℂ) c) (MvPolynomial.C t)) = _
      rw [MvPolynomial.aeval_C, MvPolynomial.eval₂Hom_C]
      exact (IsScalarTower.algebraMap_apply ℂ Γ(X.left, ⊤) (Localization.Away d) t).symm
    · intro i
      change algebraMap Γ(X.left, ⊤) (Localization.Away d)
        ((MvPolynomial.aeval (R := ℂ) c) (MvPolynomial.X i)) = _
      rw [MvPolynomial.aeval_X, MvPolynomial.eval₂Hom_X']
  refine ⟨U, inferInstance, j, p', inferInstanceAs (IsOpenImmersion O.ι), ?_, ?_, ?_⟩
  · apply Over.OverMorphism.ext
    exact ComplexPoint.liftToOpen_fac X O p hp
  · apply s2v_l1a_etale_principal_section_parameters j c d
      (s2v_l1a_openScheme_sections_localization X.left d)
    rw [hcomp]
    exact hEt
  · intro k
    rw [s2v_l1a_affine_ideal_pullback, hI k, Ideal.map_span, Set.image_singleton]


end HodgeLean.Foundations.Program
