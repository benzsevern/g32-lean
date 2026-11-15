import HodgeLean.Foundations.Program.SchoenTowerI2aActualBranchSections

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
open scoped BigOperators
namespace HodgeLean.Foundations.Program

/-- One actual affine open neighborhood of the specified point makes every
absent branch equation a unit.
Source: Hartshorne, Algebraic Geometry, II.2, principal opens and localization. -/
theorem s2v_i2a_absent_branch_unit_neighborhood
    (U : Over (Spec ↧ℂ)) [IsAffine U.left] (p : ComplexPoint U)
    {T : Type} [Fintype T] (J : Finset T) (f : T → Γ(U.left, ⊤))
    (hf : ∀ t, t ∉ J → Point.evaluate ⊤ (f t) p ≠ 0) :
    ∃ (U' : Over (Spec ↧ℂ)) (hU' : IsAffine U'.left) (v : U' ⟶ U)
      (p' : ComplexPoint U'), IsOpenImmersion v.left ∧ Point.map v p' = p ∧
        ∀ t, t ∉ J → IsUnit (v.left.appTop.hom (f t)) := by
  classical
  let φ := s2t_affinePointAlgHom U p
  let absent : Finset T := Finset.univ \ J
  let d : Γ(U.left, ⊤) := ∏ t ∈ absent, f t
  have hd : Point.evaluate ⊤ d p ≠ 0 := by
    rw [← s2t_affinePointAlgHom_apply]
    change φ (∏ t ∈ absent, f t) ≠ 0
    rw [map_prod]
    apply Finset.prod_ne_zero_iff.mpr
    intro t ht
    change (s2t_affinePointAlgHom U p) (f t) ≠ 0
    rw [s2t_affinePointAlgHom_apply]
    exact hf t (Finset.mem_sdiff.mp ht).2
  let O := U.left.basicOpen d
  let U' := ComplexPoint.openScheme U O
  let v : U' ⟶ U := ComplexPoint.openInclusion U O
  have hpO : p ∈ Point.overOpen O :=
    (Point.mem_overOpen_basicOpen_iff_evaluate_ne_zero d p
      (show p ∈ Point.overOpen ⊤ from trivial)).mpr hd
  let p' := ComplexPoint.asOpenPoint U O p hpO
  letI : IsAffine U'.left := (isAffineOpen_top U.left).basicOpen d
  letI : Algebra Γ(U.left, ⊤) Γ(U'.left, ⊤) := v.left.appTop.hom.toAlgebra
  letI : IsLocalization.Away d Γ(U'.left, ⊤) :=
    s2v_l1a_openScheme_sections_localization U.left d
  have hunit : IsUnit (algebraMap Γ(U.left, ⊤) Γ(U'.left, ⊤) d) :=
    IsLocalization.map_units Γ(U'.left, ⊤) ⟨d, Submonoid.mem_powers d⟩
  refine ⟨U', inferInstance, v, p', inferInstanceAs (IsOpenImmersion O.ι), ?_, ?_⟩
  · apply Over.OverMorphism.ext
    exact ComplexPoint.liftToOpen_fac U O p hpO
  · intro t ht
    have hmem : t ∈ absent := Finset.mem_sdiff.mpr ⟨Finset.mem_univ t, ht⟩
    exact isUnit_of_dvd_unit
      (map_dvd v.left.appTop.hom (Finset.dvd_prod_of_mem f hmem)) hunit

end HodgeLean.Foundations.Program
