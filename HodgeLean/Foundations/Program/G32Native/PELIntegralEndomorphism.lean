import HodgeLean.Foundations.Program.G32Native.PELIntegralTranspose
import HodgeLean.Adapters.GagaWiring

noncomputable section
set_option maxHeartbeats 200000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open scoped TensorProduct CategoryTheory.MonObj
open HodgeLean.Papers HodgeLean.RealDefs HodgeLean.Adapters
namespace HodgeLean.Foundations.Program.GeneralTypeIII

/-- A Hodge operator preserving integer-valued periods is induced by an actual
abelian endomorphism, with no denominator multiplier.
Source: Birkenhake–Lange, Complex Abelian Varieties, Proposition 1.2.1;
Serre, GAGA, §3, Proposition 13. -/
theorem integral_hodge_endomorphism
    (X : Over (Spec ↧ℂ)) [GrpObj X] [IsCommMonObj X]
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (T : Module.End ℚ (HQ X 1))
    (hT : (complexHolomorphicH1 X).map (T.baseChange ℂ) ≤ complexHolomorphicH1 X)
    (hZ : ∀ x : HQ X 1, b60b_periodLinearEquiv X x ∈ integralDual _ →
      b60b_periodLinearEquiv X (T x) ∈ integralDual _) :
    ∃ f : AbelianEnd X, abelianEndAction X f = T := by
  let e := b60b_periodLinearEquiv X
  have he (x : HQ X 1) (l : abelianPeriodLattice X) :
      e x l = abelianPeriod X x l :=
    Classical.choose_spec (spec_abelianPeriod_equiv X) x l
  let U := e.conjAlgEquiv ℚ T
  have hU : ∀ x ∈ integralDual (b2_abelianLattice X), U x ∈ integralDual _ := by
    intro x hx
    change e (T (e.symm x)) ∈ _
    apply hZ
    change e (e.symm x) ∈ integralDual _
    simpa only [LinearEquiv.apply_symm_apply] using hx
  obtain ⟨φ, hφ⟩ := integralDual_transpose (abelianLatticeBasis X) U hU
  have hp (x : HQ X 1) (l : abelianPeriodLattice X) :
      abelianPeriod X (T x) l = abelianPeriod X x (φ l) := by
    have hh := hφ (e x) l
    change e (T (e.symm (e x))) l = e x (φ l) at hh
    rw [LinearEquiv.symm_apply_apply] at hh
    simpa only [he] using hh
  obtain ⟨A, hA⟩ := (spec_hodge_iff_complexLinear X T φ.toAddMonoidHom hp).1 hT
  obtain ⟨f, hf⟩ := gagaw_spec_exists_abelianEnd_of_lattice X A fun l hl => by
    have hh := (φ ⟨l, hl⟩).property
    change (φ.toAddMonoidHom ⟨l, hl⟩).val ∈ abelianPeriodLattice X at hh
    rwa [hA] at hh
  obtain ⟨φf, hφf⟩ := spec_abelianEndAction_period X f
  have heq : φf = φ.toAddMonoidHom := AddMonoidHom.ext fun l =>
    Subtype.ext ((spec_latticeRepresentation_eq_analytic X f A hf φf hφf l).trans
      (hA l).symm)
  refine ⟨f, LinearMap.ext fun x => e.injective ?_⟩
  ext l
  rw [he, he, hφf, heq, hp]
  rfl

#print axioms integral_hodge_endomorphism
end HodgeLean.Foundations.Program.GeneralTypeIII
