import HodgeLean.Foundations.Program.SchoenCycleProjectiveSectionEvaluation
import HodgeLean.Foundations.Program.SchoenCycleProjectiveChartDomainPoints

/-! # Actual hyperplane points on standard affine charts -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexProjectiveSpace
open scoped BigOperators
namespace HodgeLean.Foundations.Program

/-- On an actual standard affine chart, the projective hyperplane point set is exactly the zero set of its actual regular linear section.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.3(iv), printed p. 14;
Lemma 2.4, printed p. 15; Hartshorne, Algebraic Geometry, II.7. -/
theorem s2e_projective_linear_pointSet_iff_evaluate
    (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (k : ℕ) (hd : Module.finrank ℂ V = k + 1) (L : V →ₗ[ℂ] ℂ) (i : Fin (k + 1))
    (R : ComplexPoint (Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ))))
    (hR : R.underlying ∈ (s2e_standardProjectiveAffineOpen i).1) :
    (∃ (w : V) (hw : w ≠ 0),
      (s2e_finiteDimensionalProjectivePointEquiv (V := V) k hd).symm R =
        Projectivization.mk ℂ w hw ∧ L w = 0) ↔
      Point.evaluate (s2e_standardProjectiveAffineOpen i).1
        (s2e_standardProjectiveLinearSection V k hd L i) R = 0 := by
  obtain ⟨⟨v, hv⟩, rfl⟩ := surjective_vectorToComplexPoint R
  have hi := (s2e_standardProjectiveAffineOpen_mem_iff v hv i).mp hR
  let b := Module.finBasisOfFinrankEq ℂ V hd
  let u := b.equivFun.symm v
  have hu : u ≠ 0 := b.equivFun.symm.map_ne_zero_iff.mpr hv
  have he : (s2e_finiteDimensionalProjectivePointEquiv (V := V) k hd).symm
      (vectorToComplexPoint v hv) = Projectivization.mk ℂ u hu :=
    s2e_finiteDimensionalProjectivePointEquiv_symm_vector k hd v hv
  rw [s2e_standardProjectiveLinearSection_evaluate V k hd L v i hi]
  have hu_sum : (∑ j, v j • Module.finBasisOfFinrankEq ℂ V hd j) = u :=
    (b.equivFun_symm_apply v).symm
  rw [hu_sum, he, mul_eq_zero, or_iff_right (inv_ne_zero hi)]
  constructor
  · rintro ⟨w, hw, hh, hwL⟩
    obtain ⟨c, hc⟩ := (Projectivization.mk_eq_mk_iff' ℂ u w hu hw).mp hh
    rw [← hc, map_smul, hwL, smul_zero]
  · intro huL
    exact ⟨u, hu, rfl, huL⟩

end HodgeLean.Foundations.Program
