import HodgeLean.Adapters.LefschetzOneOneAlgebraicAbelianDefs
import HodgeLean.Adapters.RiemannFormHermitian

noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
open HodgeLean.RealDefs HodgeLean.Foundations HodgeLean.Foundations.AppellHumbert
open HodgeLean.Foundations.AutomorphyChernClass
open HodgeLean.Foundations.AnalyticDivisorAlgebraic7
open HodgeLean.Foundations.AnalyticDivisorAlgebraic11
open HodgeLean.Foundations.AnalyticDivisorAlgebraic14
open Filter Set Topology
namespace HodgeLean.Adapters

/-- A nowhere-zero section trivializes the integral alternating form.
Source: `spec_chernForm_coboundary` and `spec_chernForm_datumOfX`. -/
theorem bh5_nowhere_zero_form_aux
    (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] (A : bh4_AHData X)
    (θ : (Fin (dim X.left) → ℂ) → ℂ)
    (hθ : θ ∈ sections (datumOfX X A.H A.E A.integral A.chi A.semicharacter))
    (hnz : ∀ z, θ z ≠ 0) : A.E = 0 := by
  let T := datumOfX X A.H A.E A.integral A.chi A.semicharacter
  have hc := spec_chernForm_coboundary θ hθ.1.continuous hnz (holLog T)
    (fun l z ↦ by
      rw [hθ.2 l z, mul_div_cancel_right₀ _ (hnz z)]
      exact (spec_holLog_isLog T).1 l z) (spec_holLog_isLog T).2
  ext l m
  have h := spec_chernForm_datumOfX X A.H A.E A.integral A.chi A.semicharacter
    (holLog T) (spec_holLog_isLog T).1 (spec_holLog_isLog T).2 l m
  have hc' := congrFun (congrFun hc l) m
  change chernForm (holLog T) l m = 0 at hc'
  change A.E l m = 0
  exact neg_eq_zero.mp (h.symm.trans hc')

/-- Positivity in positive dimension forces a nonzero integral form.
Source: `spec_hermitian_eq_of_imaginary_lattice`; Birkenhake--Lange, Lemma 1.3.1. -/
theorem bh5_positive_form_ne_zero_aux
    (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] (A : bh4_AHData X) (hpos : A.H.IsPositiveDefinite)
    (hdim : 0 < dim X.left) : A.E ≠ 0 := by
  intro he
  letI : IsZLattice ℝ (abelianPeriodLattice X) :=
    (datumOfX X A.H A.E A.integral A.chi A.semicharacter).isZLattice
  letI : DiscreteTopology (abelianPeriodLattice X) :=
    (datumOfX X A.H A.E A.integral A.chi A.semicharacter).discrete
  have hH : A.H = HermitianForm.zero :=
    spec_hermitian_eq_of_imaginary_lattice (abelianPeriodLattice X) A.H
      HermitianForm.zero (fun l m ↦ by
        rw [← A.integral l m, he]
        simp [HermitianForm.imaginary, HermitianForm.zero])
  let v : Fin (dim X.left) → ℂ := fun _ ↦ 1
  have hv : v ≠ 0 := by
    intro h
    have := congrFun h ⟨0, hdim⟩
    exact one_ne_zero this
  have hp := hpos v hv
  rw [hH] at hp
  exact (lt_irrefl (0 : ℝ)) hp

/-- Composition through the integral form, with exactly the stage-four theta target.
Source: Birkenhake--Lange, section 3.1; the preceding two lemmas. -/
theorem bh5_theta_zero_aux
    (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] (A : bh4_AHData X) (hpos : A.H.IsPositiveDefinite)
    (hdim : 0 < dim X.left) (θ : (Fin (dim X.left) → ℂ) → ℂ)
    (hθ : θ ∈ sections (datumOfX X A.H A.E A.integral A.chi A.semicharacter)) :
    ∃ z, θ z = 0 := by
  by_contra! hnz
  exact bh5_positive_form_ne_zero_aux X A hpos hdim
    (bh5_nowhere_zero_form_aux X A θ hθ hnz)

end HodgeLean.Adapters
