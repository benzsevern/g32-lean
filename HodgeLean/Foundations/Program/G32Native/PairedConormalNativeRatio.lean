import HodgeLean.Foundations.Program.G32Native.PairedConormalNativeProjective
import HodgeLean.Ported.NYLL.SchemeTheory.ProjectiveSpace.Basic
import Mathlib.Algebra.MvPolynomial.Division
import Mathlib.RingTheory.Ideal.Maximal

/-! # Reduced coordinate equations in the native projective charts -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
attribute [local instance] MvPolynomial.gradedAlgebra
namespace HodgeLean.Foundations.Program.G32Native

/-- Every coordinate ratio generates a radical ideal on the actual native
chart over a domain, including the chart where the ratio is one. -/
theorem paired_nativeRatio_span_radical (R : Type) [CommRing R] [IsDomain R]
    (k : ℕ) (i j : Fin (k + 1)) :
    (Ideal.span {ProjSpace.ratio R k i j}).IsRadical := by
  classical
  by_cases h : j = i
  · subst j
    rw [ProjSpace.ratio_self, Ideal.span_singleton_one]
    exact Ideal.radical_eq_iff.mp (Ideal.radical_top _)
  · letI : Algebra R (HomogeneousLocalization.Away
      (MvPolynomial.homogeneousSubmodule (Fin (k + 1)) R) (MvPolynomial.X i)) :=
      Proj.instAlgebraAway R (MvPolynomial.X i)
    let e := (Proj.dehom R i (MvPolynomial.X i) rfl).toRingEquiv
    have he : e (MvPolynomial.X ⟨j, h⟩) = ProjSpace.ratio R k i j := by
      change (Proj.dehomAux R i (MvPolynomial.X i) rfl) (MvPolynomial.X ⟨j, h⟩) = _
      rw [Proj.dehomAux, MvPolynomial.aeval_X]
      rfl
    let I : Ideal (MvPolynomial {a : Fin (k + 1) // a ≠ i} R) :=
      Ideal.span {MvPolynomial.X ⟨j, h⟩}
    have hprime : Prime (MvPolynomial.X ⟨j, h⟩ :
        MvPolynomial {a : Fin (k + 1) // a ≠ i} R) := MvPolynomial.X_prime
    letI : I.IsPrime := Ideal.isPrime_span_singleton_of_prime hprime
    have hp : (Ideal.map e.toRingHom I).IsPrime :=
      Ideal.map_isPrime_of_surjective e.surjective (by
        rw [(RingHom.injective_iff_ker_eq_bot e).mp e.injective]
        exact bot_le)
    have hr := hp.isRadical
    dsimp only [I] at hr
    rw [Ideal.map_span, Set.image_singleton] at hr
    change (Ideal.span {e (MvPolynomial.X ⟨j, h⟩)}).IsRadical at hr
    rw [he] at hr
    exact hr

end HodgeLean.Foundations.Program.G32Native
