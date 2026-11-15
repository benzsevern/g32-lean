import HodgeLean.Foundations.Program.SchoenCycleAdicInvariantAlgebra

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- The actual group action is linear over its actual invariant coefficient algebra.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Mumford–Fogarty–Kirwan, Geometric Invariant Theory, Chapter 1, §1. -/
def s2e_invariant_coefficient_base_action
    {B G : Type*} [CommRing B] [Algebra ℂ B] [Group G]
    (α : G →* (B ≃ₐ[ℂ] B)) :
    let F : Subalgebra ℂ B := ⨅ g, AlgHom.equalizer (α g).toAlgHom (AlgHom.id ℂ B)
    G →* (B ≃ₐ[F] B) := by
  dsimp only
  let F : Subalgebra ℂ B := ⨅ g, AlgHom.equalizer (α g).toAlgHom (AlgHom.id ℂ B)
  let e (g : G) : B ≃ₐ[F] B :=
    AlgEquiv.ofRingEquiv (f := (α g).toRingEquiv) (fun p => Algebra.mem_iInf.mp p.property g)
  refine { toFun := e, map_one' := ?_, map_mul' := ?_ }
  · apply AlgEquiv.ext
    intro b
    change α 1 b = b
    rw [map_one, AlgEquiv.one_apply]
  · intro g h
    apply AlgEquiv.ext
    intro b
    change α (g * h) b = α g (α h b)
    rw [map_mul, AlgEquiv.mul_apply]

/-- The invariant coefficient adic algebra identifies with the actual invariants in its extended-ideal adic algebra.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Mumford–Fogarty–Kirwan, Geometric Invariant Theory, Chapter 1, §1. -/
def s2e_invariant_coefficient_adic_equiv
    {B G : Type*} [CommRing B] [Algebra ℂ B] [Group G] [Fintype G]
    (α : G →* (B ≃ₐ[ℂ] B))
    (I : Ideal (⨅ g, AlgHom.equalizer (α g).toAlgHom (AlgHom.id ℂ B) : Subalgebra ℂ B)) :
    let F : Subalgebra ℂ B := ⨅ g, AlgHom.equalizer (α g).toAlgHom (AlgHom.id ℂ B)
    let J := I.map (algebraMap F B)
    let γ := s2e_invariant_coefficient_base_action α
    let β (g : G) := s2e_adic_algebra_map J J (γ g).toAlgHom
      (s2e_linear_preserves_extended_ideal_powers I (γ g).toLinearMap)
    AdicCompletion I F ≃ₐ[F]
      (⨅ g, AlgHom.equalizer (β g) (AlgHom.id F (AdicCompletion J B)) : Subalgebra F (AdicCompletion J B)) := by
  dsimp only
  apply s2e_adic_invariant_base_algebra_equiv I (s2e_invariant_coefficient_base_action α)
    Subtype.val_injective
  intro b hb
  refine ⟨⟨b, ?_⟩, rfl⟩
  simp only [Algebra.mem_iInf, AlgHom.mem_equalizer, AlgHom.id_apply]
  exact hb

end HodgeLean.Foundations.Program
