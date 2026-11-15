import HodgeLean.Foundations.Program.SchoenTowerL1bAdicSection
import Mathlib.RingTheory.Smooth.Field

noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- Arbitrary characteristic-zero field extensions are formally smooth,
using a transcendence basis and separability of the remaining extension. -/
theorem s2v_l1b_charZero_field_formallySmooth
    {k L : Type*} [Field k] [CharZero k] [Field L] [Algebra k L] :
    Algebra.FormallySmooth k L := by
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis k L
  haveI := hs.isAlgebraic_field
  exact Algebra.FormallySmooth.of_algebraicIndependent_of_isSeparable hs.1

/-- A characteristic-zero local algebra has an injective residue-field
section into its adic ring without a finite type restriction. -/
theorem s2v_l1b_charZero_residue_field_section
    {k R : Type*} [Field k] [CharZero k] [CommRing R] [IsLocalRing R]
    [Algebra k R] :
    let I := IsLocalRing.maximalIdeal R
    ∃ σ : (R ⧸ I) →ₐ[k] AdicCompletion I R,
      Function.Injective σ ∧
      ((AdicCompletion.evalOneₐ I).restrictScalars k).comp σ = AlgHom.id k (R ⧸ I) := by
  let I := IsLocalRing.maximalIdeal R
  letI : I.IsMaximal := IsLocalRing.maximalIdeal.isMaximal R
  letI : Field (R ⧸ I) := Ideal.Quotient.field I
  letI : Algebra.FormallySmooth k (R ⧸ I) := s2v_l1b_charZero_field_formallySmooth
  obtain ⟨σ, hσ⟩ := s2v_l1b_adic_coefficient_lift I (AlgHom.id k (R ⧸ I))
  refine ⟨σ, ?_, hσ⟩
  intro a b hab
  have h := congrArg (fun x => AdicCompletion.evalOneₐ I x) hab
  have ha := congrArg (fun f => f a) hσ
  have hb := congrArg (fun f => f b) hσ
  exact ha.symm.trans (h.trans hb)

end HodgeLean.Foundations.Program
