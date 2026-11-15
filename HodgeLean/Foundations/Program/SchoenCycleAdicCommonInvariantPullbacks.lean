import HodgeLean.Foundations.Program.SchoenCycleAdicAlgebraMapComp
import HodgeLean.Foundations.Program.SchoenCycleCommonInvariantMap

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- Two invariant formal identifications retaining the actual composite pullback identify the canonical intermediate adic map bijectively.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Mumford–Fogarty–Kirwan, Geometric Invariant Theory, Chapter 1, §1. -/
theorem s2e_adic_map_bijective_of_common_invariant_pullbacks
    {k A B C : Type*} [CommRing k] [CommRing A] [CommRing B] [CommRing C]
    [Algebra k A] [Algebra k B] [Algebra k C]
    (I : Ideal A) (J : Ideal B) (L : Ideal C)
    (f : A →ₐ[k] B) (g : B →ₐ[k] C)
    (hf : ∀ n a, a ∈ I ^ n → f a ∈ J ^ n)
    (hg : ∀ n b, b ∈ J ^ n → g b ∈ L ^ n)
    (K : Subalgebra k (AdicCompletion L C))
    (E : AdicCompletion I A ≃ₐ[k] K) (F : AdicCompletion J B ≃ₐ[k] K)
    (hE : ∀ x, (E x).val = s2e_adic_algebra_map I L (g.comp f)
      (fun n a ha => hg n (f a) (hf n a ha)) x)
    (hF : ∀ y, (F y).val = s2e_adic_algebra_map J L g hg y) :
    Function.Bijective (s2e_adic_algebra_map I J f hf) := by
  apply s2e_actual_map_bijective_of_common_invariant_coordinates K E F
  intro x
  rw [hF, hE]
  exact DFunLike.congr_fun (s2e_adic_algebra_map_comp I J L f g hf hg) x

#print axioms s2e_adic_map_bijective_of_common_invariant_pullbacks
end HodgeLean.Foundations.Program
