import HodgeLean.Foundations.Program.SchoenCycleU1UnramifiedLocus
import HodgeLean.Foundations.Program.SchoenCycleU1DerivationDual

/-! # A local dual-number lifting criterion -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- Uniqueness of local dual-number lifts at maximal points detects unramifiedness.
Source: Hartshorne, Algebraic Geometry, II.8; Stacks Project, Tag 00UM. -/
theorem s2e_u1_unramified_of_unique_local_dual_lifts
    (A B : Type*) [CommRing A] [CommRing B] [Algebra A B]
    [Algebra.EssFiniteType A B]
    (hdual : ∀ (q : Ideal B) [q.IsMaximal],
      Subsingleton (Localization.AtPrime q →ₐ[A]
        DualNumber (IsLocalRing.ResidueField (Localization.AtPrime q)))) :
    Algebra.FormallyUnramified A B := by
  apply s2e_u1_unramified_of_maximal_residue_derivations A B
  intro q hq d
  have hd := (hdual q).elim (s2e_u1_derivationDualLift d) (s2e_u1_derivationDualLift 0)
  apply Derivation.ext
  intro x
  have hx := congrArg (fun f => TrivSqZeroExt.snd (f x)) hd
  simpa only [s2e_u1_derivationDualLift, AlgHom.coe_mk, RingHom.coe_mk,
    MonoidHom.coe_mk, OneHom.coe_mk, TrivSqZeroExt.snd_add,
    TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add, Derivation.zero_apply] using hx

end HodgeLean.Foundations.Program
