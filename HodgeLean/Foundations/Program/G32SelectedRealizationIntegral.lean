import HodgeLean.Foundations.Program.G32SelectedRealizationProjector

noncomputable section
set_option maxRecDepth 2000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Papers HodgeLean.Foundations
open scoped TensorProduct CategoryTheory.MonObj
namespace HodgeLean.Foundations.Program

theorem g32y_period_lattice_ext (X : Over (Spec ↧ℂ)) [GrpObj X]
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    {a b : abelianPeriodLattice X}
    (h : ∀ x, abelianPeriod X x a = abelianPeriod X x b) : a = b := by
  obtain ⟨e, he⟩ := spec_abelianPeriod_equiv X
  refine (abelianLatticeBasis X).ext_elem fun i => ?_
  let χ : abelianPeriodLattice X →+ ℚ :=
    (Int.castAddHom ℚ).comp ((abelianLatticeBasis X).coord i).toAddMonoidHom
  have hχ := h (e.symm χ)
  rw [← he, ← he, LinearEquiv.apply_symm_apply] at hχ
  have h2 : ((abelianLatticeBasis X).repr a i : ℚ) = (abelianLatticeBasis X).repr b i := hχ
  exact_mod_cast h2

theorem g32y_lattice_scaled_idempotent (X : Over (Spec ↧ℂ)) [GrpObj X]
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (f : AbelianEnd X) (φ : abelianPeriodLattice X →+ abelianPeriodLattice X)
    (hφ : ∀ x l, abelianPeriod X (abelianEndAction X f x) l = abelianPeriod X x (φ l))
    (N : ℕ) (hf : abelianEndAction X f ∘ₗ abelianEndAction X f =
      (N : ℚ) • abelianEndAction X f) :
    ∀ l, φ (φ l) = N • φ l := by
  intro l
  apply g32y_period_lattice_ext X
  intro x
  have hh := LinearMap.congr_fun hf x
  change abelianEndAction X f (abelianEndAction X f x) = (N : ℚ) • abelianEndAction X f x at hh
  calc
    abelianPeriod X x (φ (φ l)) =
        abelianPeriod X (abelianEndAction X f (abelianEndAction X f x)) l := by
      rw [hφ, hφ]
    _ = abelianPeriod X ((N : ℚ) • abelianEndAction X f x) l := by rw [hh]
    _ = abelianPeriod X x (N • φ l) := by
      rw [map_smul, Pi.smul_apply, hφ]
      have hp (l) : abelianPeriodEquiv X x l = abelianPeriod X x l :=
        Classical.choose_spec (spec_abelianPeriod_equiv X) x l
      rw [← hp (φ l), ← hp (N • φ l), (abelianPeriodEquiv X x).map_nsmul]
      simp only [nsmul_eq_mul, smul_eq_mul]

end HodgeLean.Foundations.Program
