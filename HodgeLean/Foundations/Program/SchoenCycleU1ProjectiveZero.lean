import HodgeLean.Foundations.Program.SchoenCycleU1ProjectiveChartAlgebra
import HodgeLean.Foundations.Program.SchoenCycleU1SpecOver

/-! # Scheme-valued points of zero-dimensional projective space -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexProjectiveSpace
attribute [local instance] MvPolynomial.gradedAlgebra
namespace HodgeLean.Foundations.Program

/-- Zero-dimensional projective space has a unique point over every complex
algebra, including nonreduced algebras.
Source: Hartshorne, Algebraic Geometry, II.7, the unique standard chart of projective zero-space. -/
theorem s2e_u1_projective_zero_algebra_point_unique
    (A : Type) [CommRing A] [Algebra ℂ A]
    (f g : s2e_u1_specOver A ⟶
      Over.mk (ProjectiveSpace.toBase (Fin 1) (Spec ↧ℂ))) : f = g := by
  let e := Proj.awayι (UniversalGrading 0) (MvPolynomial.X (0 : Fin 1))
    (MvPolynomial.isHomogeneous_X _ _) zero_lt_one
  have htop : Proj.basicOpen (UniversalGrading 0) (MvPolynomial.X (0 : Fin 1)) = ⊤ := by
    apply top_unique
    rw [← iSup_coordinateBasicOpen_eq_top 0]
    apply iSup_le
    intro i
    rw [Fin.eq_zero i]
  let qf := f.left ≫ Limits.pullback.snd (Limits.terminal.from (Spec ↧ℂ))
    (Limits.terminal.from (Proj (UniversalGrading 0)))
  let qg := g.left ≫ Limits.pullback.snd (Limits.terminal.from (Spec ↧ℂ))
    (Limits.terminal.from (Proj (UniversalGrading 0)))
  have hr (q : Spec (CommRingCat.of A) ⟶ Proj (UniversalGrading 0)) :
      Set.range q ⊆ Set.range e := by
    change Set.range q ⊆ e.opensRange
    dsimp only [e]
    rw [Proj.opensRange_awayι, htop]
    exact Set.subset_univ _
  let lf := IsOpenImmersion.lift e qf (hr qf)
  let lg := IsOpenImmersion.lift e qg (hr qg)
  have hp : (Spec.preimage lf).hom = (Spec.preimage lg).hom := by
    apply s2e_u1_projective_chart_ringHom_ext (0 : Fin 1)
    intro j
    have hj : j = 0 := Fin.eq_zero j
    subst j
    rw [chartCoordinate_self, map_one, map_one]
  have hl : lf = lg := by
    rw [← Spec.map_preimage lf, ← Spec.map_preimage lg]
    congr 1
    exact CommRingCat.hom_ext hp
  have hq : qf = qg := by
    calc
      qf = lf ≫ e := (IsOpenImmersion.lift_fac e qf (hr qf)).symm
      _ = lg ≫ e := congrArg (fun l => l ≫ e) hl
      _ = qg := IsOpenImmersion.lift_fac e qg (hr qg)
  ext1
  apply Limits.pullback.hom_ext
  · exact (Over.w f).trans (Over.w g).symm
  · exact hq

end HodgeLean.Foundations.Program
