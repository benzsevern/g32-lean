import HodgeLean.Foundations.Program.SchoenSelectedGeometryLineAlgebraSmooth
import Mathlib.RingTheory.Spectrum.Prime.Jacobson

noncomputable section
set_option maxHeartbeats 400000
open Set Topology AlgebraicGeometry ComplexAlgHom
namespace HodgeLean.Foundations.Program

/-- Smoothness of a finitely presented complex algebra can be tested at scalar evaluations. -/
theorem s0_algebra_smooth_of_evaluations
    (S : Type) [CommRing S] [Algebra ℂ S] [Algebra.FinitePresentation ℂ S]
    (h : ∀ w : S →ₐ[ℂ] ℂ,
      letI : (RingHom.ker w).IsPrime := RingHom.ker_isPrime w
      Algebra.IsSmoothAt ℂ (RingHom.ker w)) : Algebra.Smooth ℂ S := by
  letI : IsJacobsonRing S := isJacobsonRing_of_finiteType (A := ℂ)
  have hall : Algebra.smoothLocus ℂ S = Set.univ := by
    rw [Set.eq_univ_iff_forall]
    intro p
    by_contra hp
    obtain ⟨q, hq, hqc⟩ := nonempty_inter_closedPoints
      (show (Algebra.smoothLocus ℂ S)ᶜ.Nonempty from ⟨p, hp⟩)
      (Algebra.isOpen_smoothLocus (R := ℂ) (A := S)).isClosed_compl.isLocallyClosed
    letI : q.asIdeal.IsMaximal := (PrimeSpectrum.isClosed_singleton_iff_isMaximal q).mp hqc
    letI := Ideal.Quotient.field q.asIdeal
    letI : Module.Finite ℂ (S ⧸ q.asIdeal) :=
      finite_of_finite_type_of_isJacobsonRing ℂ (S ⧸ q.asIdeal)
    let e : ℂ ≃ₐ[ℂ] S ⧸ q.asIdeal := AlgEquiv.ofBijective (Algebra.ofId ℂ _)
      IsAlgClosed.algebraMap_bijective_of_isIntegral
    let w : S →ₐ[ℂ] ℂ := e.symm.toAlgHom.comp (Ideal.Quotient.mkₐ ℂ q.asIdeal)
    have hw : RingHom.ker w = q.asIdeal := by
      ext s
      change e.symm (Ideal.Quotient.mk q.asIdeal s) = 0 ↔ s ∈ q.asIdeal
      rw [← map_zero e.symm, e.symm.injective.eq_iff, Ideal.Quotient.eq_zero_iff_mem]
    have hs := h w
    exact hq (by simpa only [Algebra.smoothLocus, Set.mem_setOf_eq, hw] using hs)
  exact ⟨(Algebra.smoothLocus_eq_univ_iff.mp hall), inferInstance⟩

#print axioms s0_algebra_smooth_of_evaluations
end HodgeLean.Foundations.Program
