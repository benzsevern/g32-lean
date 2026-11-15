import HodgeLean.Foundations.Program.SchoenTowerL1bEtaleDerivations
import HodgeLean.Foundations.Program.SchoenTowerL1bConormal
import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-! # Independence of selected étale coordinate germs -/
noncomputable section
set_option maxHeartbeats 200000
open IsLocalRing
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Program

/-- Distinct formally étale coordinates in the maximal ideal have
independent cotangent classes; their dual derivations detect coefficients.
Source: Hartshorne, Algebraic Geometry, II.8; EGA IV, 17.11.1. -/
theorem paired_c3_etale_cotangent_independent
    {K A σ ι : Type*} [CommRing K] [CommRing A] [IsLocalRing A]
    [Algebra K A] [Algebra (MvPolynomial σ K) A]
    [IsScalarTower K (MvPolynomial σ K) A]
    [Algebra.FormallyEtale (MvPolynomial σ K) A]
    [Fintype ι] [DecidableEq ι] [DecidableEq σ]
    (v : ι ↪ σ)
    (hm : ∀ i, algebraMap (MvPolynomial σ K) A (MvPolynomial.X (v i)) ∈ maximalIdeal A) :
    LinearIndependent (ResidueField A) (fun i => (maximalIdeal A).toCotangent
      ⟨algebraMap (MvPolynomial σ K) A (MvPolynomial.X (v i)), hm i⟩) := by
  apply s2v_l1b_conormal_independent (maximalIdeal A) _ hm
    (fun i => s2v_l1b_etaleCoordinateDerivation K A σ (v i))
  intro i j
  simpa only [v.injective.eq_iff] using
    s2v_l1b_etaleCoordinateDerivation_apply K A σ (v i) (v j)

#print axioms paired_c3_etale_cotangent_independent
end HodgeLean.Foundations.Program.G32Native
