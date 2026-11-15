import HodgeLean.Foundations.Program.SchoenCycleAdicGroupInvariants

/-! # Adic invariant base-ring comparison -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- Invariant descent gives a linear identification of the adic base module with the invariant part of the adic algebra.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Mumford–Fogarty–Kirwan, Geometric Invariant Theory, Chapter 1, §1, invariant affine quotients. -/
def s2e_adic_invariant_base_equiv
    {R B G : Type*} [CommRing R] [Algebra ℂ R] [CommRing B] [Algebra R B]
    [Group G] [Fintype G] (I : Ideal R) (a : G →* (B ≃ₐ[R] B))
    (hinj : Function.Injective (algebraMap R B))
    (hdescent : ∀ b : B, (∀ g, a g b = b) → ∃ r : R, algebraMap R B r = b) :
    AdicCompletion I R ≃ₗ[AdicCompletion I R]
      (⨅ g, (AdicCompletion.map I (a g).toLinearMap).fixedSubmodule :
        Submodule (AdicCompletion I R) (AdicCompletion I B)) := by
  classical
  let F : Submodule R B := ⨅ g, (a g).toLinearMap.fixedSubmodule
  let f : R →ₗ[R] F := (Algebra.linearMap R B).codRestrict F (fun r => by
    simp only [F, Submodule.mem_iInf, LinearMap.mem_fixedSubmodule_iff]
    intro g
    exact (a g).commutes r)
  have hf : Function.Bijective f := by
    constructor
    · intro r s hrs
      exact hinj (congrArg Subtype.val hrs)
    · intro b
      have hb : ∀ g, a g b.val = b.val := by
        have hh := b.property
        simpa only [F, Submodule.mem_iInf, LinearMap.mem_fixedSubmodule_iff,
          AlgEquiv.toLinearMap_apply] using hh
      obtain ⟨r, hr⟩ := hdescent b.val hb
      exact ⟨r, Subtype.ext hr⟩
  let e : R ≃ₗ[R] F := LinearEquiv.ofBijective f hf
  let α : G →* (B ≃ₗ[R] B) :=
    { toFun := fun g => (a g).toLinearEquiv
      map_one' := by ext b; exact DFunLike.congr_fun a.map_one b
      map_mul' := fun g h => by ext b; exact DFunLike.congr_fun (a.map_mul g h) b }
  exact (AdicCompletion.congr I e).trans (s2e_adic_finite_group_invariants_equiv I α)

#print axioms s2e_adic_invariant_base_equiv
end HodgeLean.Foundations.Program
