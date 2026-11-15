import HodgeLean.Adapters.TorusCohomology
import HodgeLean.Adapters.Polarization

/-! # Nondegeneracy and the top cup power

This reduces O3 to nonvanishing of the top cup power. Nonvanishing for ample
classes still needs intersection theory (`deg D^g > 0`), C9 and the point class.
HC no distance; AV milestone no distance.
-/
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open HodgeLean.RealDefs HodgeLean.Foundations
namespace HodgeLean.Adapters

variable (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]

/-- The iterated cup power of a degree-two class, starting at the unit.
Source: `RealDefs.lefschetzPow`, applied to `unitClass`. -/
def cupPow (μ : CupProduct X) (η : HQ X 2) (g : ℕ) : HQ X (2 * g) :=
  lefschetzPow X μ η g (by omega) (unitClass X)

example (μ : CupProduct X) (η : HQ X 2) : cupPow X μ η 0 = unitClass X := rfl

/-- Multiplicativity transports the exterior power to the iterated cup power.
Source: `RealDefs.cupWedgeMap_polarizationPow` and `polarizationPow_eq_wedgePow`. -/
theorem cupWedgeEquiv_wedgePow {μ : CupProduct X} (T : TorusCohomology μ)
    (η : HQ X 2) (g : ℕ) :
    T.cupWedgeEquiv (2 * g) (Symplectic.wedgePow ((T.cupWedgeEquiv 2).symm η) g) =
      cupPow X μ η g := by
  simpa [TorusCohomology.cupWedgeEquiv_apply, polarizationPow_eq_wedgePow,
    CupProduct.cupWedgeMap_zero, cupPow] using
    cupWedgeMap_polarizationPow μ ((T.cupWedgeEquiv 2).symm η)
      ((T.cupWedgeEquiv 2).apply_symm_apply η) g (by omega)

/-- Under C7, nondegeneracy is exactly nonvanishing of the top cup power.
Source: `Symplectic.isNondegenerate_iff_wedgePow_ne_zero` and `cupWedgeEquiv_wedgePow`. -/
theorem nd_iff_cupPow_ne_zero {μ : CupProduct X} (T : TorusCohomology μ)
    (η : HQ X 2) :
    Symplectic.IsNondegenerate ((T.cupWedgeEquiv 2).symm η) ↔
      cupPow X μ η (dim X.left) ≠ 0 := by
  let := T.finite
  rw [Symplectic.isNondegenerate_iff_wedgePow_ne_zero T.finrank_eq,
    ← cupWedgeEquiv_wedgePow X T η (dim X.left)]
  exact (not_congr (T.cupWedgeEquiv _).map_eq_zero_iff).symm

omit [GrpObj X] in
/-- A positive power of the zero class vanishes.
Source: `RealDefs.lefschetzPow_succ` and bilinearity of `CupProduct.cup`. -/
theorem cupPow_zero_of_pos (μ : CupProduct X) {g : ℕ} (hg : 0 < g) :
    cupPow X μ 0 g = 0 := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hg)
  unfold cupPow
  erw [lefschetzPow_succ μ 0 r _ (m' := 2 * r) (by omega) (by omega)]
  simp

/-- In positive dimension the zero class fails both equivalent premises.
Source: `cupPow_zero_of_pos` and `nd_iff_cupPow_ne_zero`. -/
theorem zero_fails_nd_and_cupPow {μ : CupProduct X} (T : TorusCohomology μ)
    (hg : 0 < dim X.left) :
    ¬ Symplectic.IsNondegenerate ((T.cupWedgeEquiv 2).symm 0) ∧
      ¬ cupPow X μ 0 (dim X.left) ≠ 0 := by
  have h : ¬ cupPow X μ 0 (dim X.left) ≠ 0 := by
    simp [cupPow_zero_of_pos X μ hg]
  exact ⟨fun hn => h ((nd_iff_cupPow_ne_zero X T 0).mp hn), h⟩

/-- In dimension zero the top cup power is the nonzero unit, so both premises hold.
Source: `CupProduct.unitClass_ne_zero` and `nd_iff_cupPow_ne_zero`. -/
theorem nd_and_cupPow_of_dim_zero {μ : CupProduct X} (T : TorusCohomology μ)
    (hg : dim X.left = 0) (η : HQ X 2) :
    Symplectic.IsNondegenerate ((T.cupWedgeEquiv 2).symm η) ∧
      cupPow X μ η (dim X.left) ≠ 0 := by
  have h : cupPow X μ η (dim X.left) ≠ 0 := by
    rw [hg]
    exact μ.unitClass_ne_zero
  exact ⟨(nd_iff_cupPow_ne_zero X T η).mpr h, h⟩


example (η : HQ X 2) :
    Symplectic.IsNondegenerate (((torusCohomology_cupProductOf X).cupWedgeEquiv 2).symm η) ↔
      cupPow X (cupProductOf X) η (dim X.left) ≠ 0 :=
  nd_iff_cupPow_ne_zero X (torusCohomology_cupProductOf X) η

/-- O3 for abelian X is reduced to nonvanishing of the top cup power, which remains
an explicit input until the curves lane's divisor stages J1--J2 prove it for ample classes.
Source: `hardLefschetz_abelian` and `nd_iff_cupPow_ne_zero`.
HC no distance; AV milestone no distance. -/
theorem hardLefschetz_abelian_of_cupPow {η : HQ X 2}
    (hη : cupPow X (cupProductOf X) η (dim X.left) ≠ 0) :
    HardLefschetz X (cupProductOf X) η :=
  hardLefschetz_abelian X ((nd_iff_cupPow_ne_zero X
    (torusCohomology_cupProductOf X) η).mpr hη)

example {η : HQ X 2} (hη : cupPow X (cupProductOf X) η (dim X.left) ≠ 0) :
    HardLefschetz X (cupProductOf X) η := hardLefschetz_abelian_of_cupPow X hη

/-- For the actual abelian cohomology package the Blocks premise is precisely
nonvanishing of the same top cup power; there is no extra comparison hypothesis.
Source: `polarizationTopPowerNonzero_iff_isNondegenerate` and `nd_iff_cupPow_ne_zero`. -/
theorem polarizationTopPowerNonzero_iff_cupPow_ne_zero
    (hF : FiniteBetti X) (hB : BettiDeRhamIso X) (hD : HodgeDecomposition X)
    {μ : CupProduct X} (T : TorusCohomology μ) (η : HQ X 2) :
    let := T.finite
    HodgeBlocks.PolarizationTopPowerNonzero (abelianVarietyCohomologyOf hF hB hD T)
      ((T.cupWedgeEquiv 2).symm η) ↔ cupPow X μ η (dim X.left) ≠ 0 := by
  let := T.finite
  exact (polarizationTopPowerNonzero_iff_isNondegenerate
    (abelianVarietyCohomologyOf hF hB hD T) _).trans (nd_iff_cupPow_ne_zero X T η)

#print axioms cupPow
#print axioms cupWedgeEquiv_wedgePow
#print axioms nd_iff_cupPow_ne_zero
#print axioms hardLefschetz_abelian_of_cupPow
#print axioms polarizationTopPowerNonzero_iff_cupPow_ne_zero
#print axioms zero_fails_nd_and_cupPow
#print axioms nd_and_cupPow_of_dim_zero

end HodgeLean.Adapters
