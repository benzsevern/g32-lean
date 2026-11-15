import HodgeLean.Foundations.Program.SchoenTowerAdicAction
import Mathlib.RingTheory.Smooth.AdicCompletion
import Mathlib.RingTheory.Etale.Basic

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace HodgeLean.Foundations.Program

/-- Every positive-power residue reduces to the first adic residue. -/
theorem s2t_adic_evalOne_transition {A : Type*} [CommRing A] (I : Ideal A)
    (n : ℕ) (hn : n ≠ 0) (x : AdicCompletion I A) :
    Ideal.Quotient.factor (I.pow_le_self hn) (AdicCompletion.evalₐ I n x) =
      AdicCompletion.evalOneₐ I x := by
  have hmn : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
  have hcomm (z : A ⧸ I ^ n) :
      Ideal.Quotient.factor (I.pow_le_self hn) z =
      Ideal.Quotient.factor (show I ^ 1 ≤ I by rw [pow_one])
        (Ideal.Quotient.factorPow I hmn z) := by
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective z
    rfl
  rw [hcomm, s2t_adic_eval_transition, AdicCompletion.factorₐ_evalₐ_one]

/-- Reduction from a positive power to the first power has nilpotent kernel. -/
theorem s2t_adic_firstReduction_nilpotent {A : Type*} [CommRing A] (I : Ideal A)
    (n : ℕ) (hn : n ≠ 0) :
    IsNilpotent (RingHom.ker (Ideal.Quotient.factor (I.pow_le_self hn))) := by
  refine ⟨n, ?_⟩
  rw [Ideal.Quotient.factor_ker, ← Ideal.map_pow, Ideal.map_quotient_self]
  rfl

/-- Maps from a formally unramified algebra to an adic ring are determined by first residues.
Source: EGA IV, 17.1.1, infinitesimal uniqueness for unramified morphisms. -/
theorem s2t_unramified_adic_hom_ext {R S A : Type*}
    [CommRing R] [CommRing S] [CommRing A] [Algebra R S] [Algebra R A]
    [Algebra.FormallyUnramified R S] (I : Ideal A)
    (f g : S →ₐ[R] AdicCompletion I A)
    (h : ((AdicCompletion.evalOneₐ I).restrictScalars R).comp f =
      ((AdicCompletion.evalOneₐ I).restrictScalars R).comp g) : f = g := by
  apply AlgHom.ext
  intro x
  apply AdicCompletion.ext_evalₐ
  intro n
  by_cases hn : n = 0
  · subst n
    haveI : Subsingleton (A ⧸ I ^ 0) := by rw [pow_zero, Ideal.one_eq_top]; infer_instance
    exact Subsingleton.elim _ _
  · have hh := Algebra.FormallyUnramified.lift_unique_of_ringHom
      (Ideal.Quotient.factor (I.pow_le_self hn)) (s2t_adic_firstReduction_nilpotent I n hn)
      (((AdicCompletion.evalₐ I n).restrictScalars R).comp f)
      (((AdicCompletion.evalₐ I n).restrictScalars R).comp g) (by
        ext y
        change Ideal.Quotient.factor (I.pow_le_self hn) (AdicCompletion.evalₐ I n (f y)) =
          Ideal.Quotient.factor (I.pow_le_self hn) (AdicCompletion.evalₐ I n (g y))
        rw [s2t_adic_evalOne_transition I n hn, s2t_adic_evalOne_transition I n hn]
        exact congrArg (fun k : S →ₐ[R] A ⧸ I => k y) h)
    exact congrArg (fun k : S →ₐ[R] A ⧸ I ^ n => k x) hh

/-- Every first residue map from a formally étale algebra has a unique adic lift.
Source: EGA IV, 17.1.1, infinitesimal lifting for étale morphisms. -/
theorem s2t_etale_existsUnique_adic_lift {R S A : Type*}
    [CommRing R] [CommRing S] [CommRing A] [Algebra R S] [Algebra R A]
    [Algebra.FormallyEtale R S] (I : Ideal A) (f : S →ₐ[R] A ⧸ I) :
    ∃! g : S →ₐ[R] AdicCompletion I A,
      ((AdicCompletion.evalOneₐ I).restrictScalars R).comp g = f := by
  obtain ⟨g, hg⟩ := Algebra.FormallySmooth.exists_adicCompletionEvalOneₐ_comp_eq f
  refine ⟨g, hg, ?_⟩
  intro g' hg'
  exact s2t_unramified_adic_hom_ext I g' g (hg'.trans hg.symm)

end HodgeLean.Foundations.Program
