import HodgeLean.Foundations.Program.CurveJacobian

noncomputable section
open CategoryTheory AlgebraicTopology.Singular
open scoped Manifold ContDiff
namespace HodgeLean.Foundations.Program

variable (C : Type) [TopologicalSpace C] [ChartedSpace ℂ C] [IsManifold 𝓘(ℂ, ℂ) ω C]
  [T2Space C] [CompactSpace C] [ConnectedSpace C]

/-- A rational class evaluates on the period lattice by the real periods of its representing form. -/
def s0_periodCharacter : Cohomology ℚ (TopCat.of C) 1 →ₗ[ℚ] (b3_periodLattice ℂ C →+ ℚ) where
  toFun a :=
    { toFun := fun l ↦ (b3Rest2_rat (Module.finrank_self ℂ) a l).choose
      map_zero' := by
        apply Rat.cast_injective (α := ℝ)
        rw [(b3Rest2_rat (Module.finrank_self ℂ) a 0).choose_spec]
        simp
      map_add' := fun l m ↦ by
        apply Rat.cast_injective (α := ℝ)
        rw [Rat.cast_add, (b3Rest2_rat (Module.finrank_self ℂ) a (l + m)).choose_spec,
          (b3Rest2_rat (Module.finrank_self ℂ) a l).choose_spec,
          (b3Rest2_rat (Module.finrank_self ℂ) a m).choose_spec]
        simp only [AddSubgroup.coe_add, Pi.add_apply, Complex.add_re, mul_add] }
  map_add' a b := by
    ext l
    apply Rat.cast_injective (α := ℝ)
    change (((b3Rest2_rat (Module.finrank_self ℂ) (a + b) l).choose : ℚ) : ℝ) =
      (((b3Rest2_rat (Module.finrank_self ℂ) a l).choose +
        (b3Rest2_rat (Module.finrank_self ℂ) b l).choose : ℚ) : ℝ)
    rw [(b3Rest2_rat (Module.finrank_self ℂ) (a + b) l).choose_spec]
    simp only [AddMonoidHom.add_apply, Rat.cast_add]
    rw [(b3Rest2_rat (Module.finrank_self ℂ) a l).choose_spec,
      (b3Rest2_rat (Module.finrank_self ℂ) b l).choose_spec,
      b3Rest2_T_add, b3Rest2_lattice_add_apply, Complex.add_re, mul_add]
  map_smul' q a := by
    ext l
    apply Rat.cast_injective (α := ℝ)
    change (((b3Rest2_rat (Module.finrank_self ℂ) (q • a) l).choose : ℚ) : ℝ) =
      ((q * (b3Rest2_rat (Module.finrank_self ℂ) a l).choose : ℚ) : ℝ)
    rw [(b3Rest2_rat (Module.finrank_self ℂ) (q • a) l).choose_spec]
    simp only [AddMonoidHom.smul_apply, smul_eq_mul, RingHom.id_apply, Rat.cast_mul]
    rw [(b3Rest2_rat (Module.finrank_self ℂ) a l).choose_spec,
      b3Rest2_T_smul, b3Rest2_lattice_smul_apply]
    simp only [Complex.mul_re, Complex.ratCast_re, Complex.ratCast_im, zero_mul, sub_zero]
    ring

#print axioms s0_periodCharacter

/-- Rational period characters recover the normalized real periods on each lattice element. -/
theorem s0_periodCharacter_spec (a : Cohomology ℚ (TopCat.of C) 1)
    (l : b3_periodLattice ℂ C) :
    ((s0_periodCharacter C a l : ℚ) : ℝ) =
      (b3Rest2_s : ℝ) * (l.1 (b3Rest2_T (Module.finrank_self ℂ) a)).re :=
  (b3Rest2_rat (Module.finrank_self ℂ) a l).choose_spec

#print axioms s0_periodCharacter_spec
end HodgeLean.Foundations.Program
