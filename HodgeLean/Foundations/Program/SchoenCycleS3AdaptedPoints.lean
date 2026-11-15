import HodgeLean.Foundations.Program.SchoenCycleProjectivePoints

/-! # Residue loci in fixed projective coordinates -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexProjectiveSpace
namespace HodgeLean.Foundations.Program

/-- A linear functional vanishes on a projective line exactly when it vanishes on its representative. -/
theorem s2e_projective_line_functional_zero {V : Type*}
    [AddCommGroup V] [Module ℂ V] (L : V →ₗ[ℂ] ℂ)
    (v : V) (hv : v ≠ 0) :
    (∃ (w : V) (hw : w ≠ 0),
      Projectivization.mk ℂ v hv = Projectivization.mk ℂ w hw ∧ L w = 0) ↔ L v = 0 := by
  constructor
  · rintro ⟨w, hw, he, hz⟩
    obtain ⟨c, hc⟩ := (Projectivization.mk_eq_mk_iff' ℂ v w hv hw).mp he
    rw [← hc, map_smul, hz, smul_zero]
  · intro hz
    exact ⟨v, hv, rfl, hz⟩

/-- Fixed homogeneous coordinates detect the residue locus through the fixed basis. -/
theorem s2e_fixed_projective_functional_locus {V : Type*}
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (k : ℕ) (hd : Module.finrank ℂ V = k + 1) (L : V →ₗ[ℂ] ℂ)
    (v : CoordinateSpace k) (hv : v ≠ 0) :
    (∃ (w : V) (hw : w ≠ 0),
      (s2e_finiteDimensionalProjectivePointEquiv (V := V) k hd).symm
        (vectorToComplexPoint v hv) = Projectivization.mk ℂ w hw ∧ L w = 0) ↔
      L ((Module.finBasisOfFinrankEq ℂ V hd).equivFun.symm v) = 0 := by
  rw [s2e_finiteDimensionalProjectivePointEquiv_symm_vector]
  exact s2e_projective_line_functional_zero L _ _

/-- The image of the projective functional locus is the set of its nonzero fixed-coordinate representatives. -/
theorem s2e_fixed_projective_functional_underlying {V : Type*}
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (k : ℕ) (hd : Module.finrank ℂ V = k + 1) (L : V →ₗ[ℂ] ℂ) :
    AlgebraicGeometry.Point.underlying ''
      {R : ComplexPoint (Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ))) |
        ∃ (w : V) (hw : w ≠ 0),
          (s2e_finiteDimensionalProjectivePointEquiv (V := V) k hd).symm R =
            Projectivization.mk ℂ w hw ∧ L w = 0} =
      {p | ∃ (v : CoordinateSpace k) (hv : v ≠ 0),
        L ((Module.finBasisOfFinrankEq ℂ V hd).equivFun.symm v) = 0 ∧
          p = (vectorToComplexPoint v hv).underlying} := by
  ext p
  constructor
  · rintro ⟨R, hR, rfl⟩
    obtain ⟨v, rfl⟩ := surjective_vectorToComplexPoint R
    exact ⟨v.val, v.property,
      (s2e_fixed_projective_functional_locus k hd L v.val v.property).mp hR, rfl⟩
  · rintro ⟨v, hv, hz, rfl⟩
    exact ⟨vectorToComplexPoint v hv,
      (s2e_fixed_projective_functional_locus k hd L v hv).mpr hz, rfl⟩


/-- The fixed projective parameter map evaluates a coefficient line in its fixed basis. -/
theorem s2e_fixed_projective_parameter_mk {V : Type*}
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (k : ℕ) (hd : Module.finrank ℂ V = k + 1) (v : V) (hv : v ≠ 0) :
    s2e_finiteDimensionalProjectivePointEquiv k hd (Projectivization.mk ℂ v hv) =
      vectorToComplexPoint ((Module.finBasisOfFinrankEq ℂ V hd).equivFun v)
        ((Module.finBasisOfFinrankEq ℂ V hd).equivFun.map_ne_zero_iff.mpr hv) := rfl

/-- An adapted coefficient line has the fixed coordinates given by the basis change. -/
theorem s2e_adapted_projective_parameter_mk {V : Type*}
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (k : ℕ) (hd : Module.finrank ℂ V = k + 1)
    (b : (Fin (k + 1) → ℂ) ≃ₗ[ℂ] V) (v : Fin (k + 1) → ℂ) (hv : v ≠ 0) :
    (s2e_finiteDimensionalProjectivePointEquiv k hd).symm
      (vectorToComplexPoint ((b.trans (Module.finBasisOfFinrankEq ℂ V hd).equivFun) v)
        ((b.trans (Module.finBasisOfFinrankEq ℂ V hd).equivFun).map_ne_zero_iff.mpr hv)) =
      Projectivization.mk ℂ (b v) (b.map_ne_zero_iff.mpr hv) := by
  apply (s2e_finiteDimensionalProjectivePointEquiv k hd).injective
  rw [Equiv.apply_symm_apply, s2e_fixed_projective_parameter_mk]
  rfl

/-- The actual coefficient-zero locus is parametrized by vectors in any chosen coefficient basis. -/
theorem s2e_coefficient_locus_change_basis {V : Type*}
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (k : ℕ) (hd : Module.finrank ℂ V = k + 1)
    (b : (Fin (k + 1) → ℂ) ≃ₗ[ℂ] V) (L : V →ₗ[ℂ] ℂ) :
    Point.underlying ''
      {R : ComplexPoint (Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ))) |
        ∃ (v : V) (hv : v ≠ 0),
          (s2e_finiteDimensionalProjectivePointEquiv k hd).symm R =
            Projectivization.mk ℂ v hv ∧ L v = 0} =
    {p | ∃ (w : Fin (k + 1) → ℂ) (hw : w ≠ 0), L (b w) = 0 ∧
      p = (vectorToComplexPoint
        ((b.trans (Module.finBasisOfFinrankEq ℂ V hd).equivFun) w)
        ((b.trans (Module.finBasisOfFinrankEq ℂ V hd).equivFun).map_ne_zero_iff.mpr hw)).underlying} := by
  ext p
  constructor
  · rintro ⟨R, ⟨v, hv, he, hz⟩, rfl⟩
    have hw : b.symm v ≠ 0 := b.symm.map_ne_zero_iff.mpr hv
    refine ⟨b.symm v, hw, ?_, ?_⟩
    · simpa only [b.apply_symm_apply] using hz
    · have hR := congrArg (s2e_finiteDimensionalProjectivePointEquiv k hd) he
      rw [Equiv.apply_symm_apply, s2e_fixed_projective_parameter_mk] at hR
      rw [hR]
      simp only [LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
  · rintro ⟨w, hw, hz, rfl⟩
    refine ⟨_, ⟨b w, b.map_ne_zero_iff.mpr hw,
      s2e_adapted_projective_parameter_mk k hd b w hw, hz⟩, rfl⟩

end HodgeLean.Foundations.Program
