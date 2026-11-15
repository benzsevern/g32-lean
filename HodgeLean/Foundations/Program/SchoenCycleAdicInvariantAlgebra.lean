import HodgeLean.Foundations.Program.SchoenCycleAdicInvariantBaseNaturality
import HodgeLean.Foundations.Program.SchoenCycleAdicBaseMapComparison
import HodgeLean.Foundations.Program.SchoenCycleAdicScalarNaturality
import Mathlib.Algebra.Algebra.Subalgebra.Lattice

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- Affine invariant descent identifies the actual extended-ideal adic invariant algebra.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Mumford–Fogarty–Kirwan, Geometric Invariant Theory, Chapter 1, §1. -/
def s2e_adic_invariant_base_algebra_equiv
    {R B G : Type*} [CommRing R] [Algebra ℂ R] [CommRing B] [Algebra R B]
    [Group G] [Fintype G] (I : Ideal R) (a : G →* (B ≃ₐ[R] B))
    (hinj : Function.Injective (algebraMap R B))
    (hdescent : ∀ b : B, (∀ g, a g b = b) → ∃ r : R, algebraMap R B r = b) :
    let J := I.map (algebraMap R B)
    let α := fun g => s2e_adic_algebra_map J J (a g).toAlgHom
      (s2e_linear_preserves_extended_ideal_powers I (a g).toLinearMap)
    AdicCompletion I R ≃ₐ[R]
      (⨅ g, AlgHom.equalizer (α g) (AlgHom.id R (AdicCompletion J B)) :
        Subalgebra R (AdicCompletion J B)) := by
  let J := I.map (algebraMap R B)
  let α := fun g => s2e_adic_algebra_map J J (a g).toAlgHom
    (s2e_linear_preserves_extended_ideal_powers I (a g).toLinearMap)
  let F : Subalgebra R (AdicCompletion J B) :=
    ⨅ g, AlgHom.equalizer (α g) (AlgHom.id R (AdicCompletion J B))
  let E := s2e_adic_invariant_base_equiv I a hinj hdescent
  let S := s2e_adic_scalar_change_equiv (B := B) I
  let f := s2e_adic_algebra_map I J (Algebra.ofId R B)
    (s2e_base_map_preserves_extended_ideal_powers I)
  have hval (x : AdicCompletion I R) : S (E x).val = f x := by
    rw [s2e_adic_invariant_base_val]
    exact s2e_adic_scalar_change_base_map I x
  have hmem (x : AdicCompletion I R) : f x ∈ F := by
    simp only [F, Algebra.mem_iInf, AlgHom.mem_equalizer]
    intro g
    change α g (f x) = f x
    rw [← hval]
    rw [← s2e_adic_scalar_change_naturality]
    have hh := (E x).property
    simp only [Submodule.mem_iInf, LinearMap.mem_fixedSubmodule_iff] at hh
    exact congrArg S (hh g)
  let φ : AdicCompletion I R →ₐ[R] F := f.codRestrict F hmem
  apply AlgEquiv.ofBijective φ
  constructor
  · intro x y hxy
    apply E.injective
    apply Subtype.ext
    apply S.injective
    rw [hval, hval]
    exact congrArg Subtype.val hxy
  · intro y
    have hy : S.symm y.val ∈
        (⨅ g, (AdicCompletion.map I (a g).toLinearMap).fixedSubmodule :
          Submodule (AdicCompletion I R) (AdicCompletion I B)) := by
      simp only [Submodule.mem_iInf, LinearMap.mem_fixedSubmodule_iff]
      intro g
      apply S.injective
      refine (s2e_adic_scalar_change_naturality I (a g).toAlgHom _).trans ?_
      rw [S.apply_symm_apply]
      have hh := y.property
      simp only [F, Algebra.mem_iInf, AlgHom.mem_equalizer] at hh
      exact hh g
    obtain ⟨x, hx⟩ := E.surjective ⟨S.symm y.val, hy⟩
    refine ⟨x, Subtype.ext ?_⟩
    change f x = y.val
    rw [← hval, hx]
    exact S.apply_symm_apply y.val

#print axioms s2e_adic_invariant_base_algebra_equiv
end HodgeLean.Foundations.Program
