import HodgeLean.Foundations.Program.SchoenCycleFormalFactorAction
import HodgeLean.Foundations.Program.SchoenCycleOrbitProductInvariants
import HodgeLean.Foundations.Program.SchoenCycleIntertwiningInvariantAlgebras

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- The invariant formal algebra over a transitive finite support orbit is the stabilizer-invariant retained formal factor, through the canonical projection.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Mumford–Fogarty–Kirwan, Geometric Invariant Theory, Chapter 1, §1. -/
theorem s2e_formal_orbit_stabilizer_invariants
    {k A G ι : Type*} [CommRing k] [CommRing A] [Algebra k A]
    [Group G] [MulAction G ι]
    (J : Ideal A) (I : ι → Ideal A) (hJI : ∀ i, J ≤ I i)
    (α : G →* (A ≃ₐ[k] A))
    (hJ : ∀ (g : G) (n : ℕ) (a : A), a ∈ J ^ n → α g a ∈ J ^ n)
    (hI : ∀ (g : G) (i : ι) (n : ℕ) (a : A), a ∈ I i ^ n → α g a ∈ I (g • i) ^ n)
    (E : AdicCompletion J A ≃ₐ[k] (∀ i, AdicCompletion (I i) A))
    (hE : ∀ (x : AdicCompletion J A) (i : ι), E x i =
      s2e_adic_algebra_map J (I i) (AlgHom.id k A)
        (fun n a ha => (Ideal.pow_right_mono (hJI i) n) ha) x)
    (i₀ : ι) (htrans : ∀ i, ∃ g : G, g • i₀ = i) :
    let a := s2e_adic_group_algebra_action J α hJ
    let β (g : MulAction.stabilizer G i₀) :=
      s2e_adic_algebra_map (I i₀) (I i₀) (α g.val).toAlgHom
        (fun n r hr => by
          change α g.val r ∈ I i₀ ^ n
          simpa only [(show g.val • i₀ = i₀ from g.property)] using hI g.val i₀ n r hr)
    ∃ F : (⨅ g : G, AlgHom.equalizer (a g).toAlgHom
        (AlgHom.id k (AdicCompletion J A)) : Subalgebra k (AdicCompletion J A)) ≃ₐ[k]
      (⨅ g : MulAction.stabilizer G i₀, AlgHom.equalizer (β g)
        (AlgHom.id k (AdicCompletion (I i₀) A)) : Subalgebra k (AdicCompletion (I i₀) A)),
      ∀ v, (F v).val = E v.val i₀ := by
  dsimp only
  let a := s2e_adic_group_algebra_action J α hJ
  let δ := (AlgEquiv.autCongr E).toMonoidHom.comp a
  let β (g : MulAction.stabilizer G i₀) :=
    s2e_adic_algebra_map (I i₀) (I i₀) (α g.val).toAlgHom
      (fun n r hr => by
          change α g.val r ∈ I i₀ ^ n
          simpa only [(show g.val • i₀ = i₀ from g.property)] using hI g.val i₀ n r hr)
  have hβ (g : MulAction.stabilizer G i₀) (v : ∀ i, AdicCompletion (I i) A) :
      (δ g.val v) i₀ = β g (v i₀) := by
    change E (s2e_adic_algebra_map J J (α g.val).toAlgHom (hJ g.val) (E.symm v)) i₀ = _
    rw [hE]
    rw [s2e_adic_projection_naturality J (I i₀) (I i₀) (hJI i₀) (hJI i₀)
      (α g.val).toAlgHom (hJ g.val)
      (fun n r hr => by
          change α g.val r ∈ I i₀ ^ n
          simpa only [(show g.val • i₀ = i₀ from g.property)] using hI g.val i₀ n r hr)]
    change β g (s2e_adic_algebra_map J (I i₀) (AlgHom.id k A) _ (E.symm v)) = _
    rw [← hE, E.apply_symm_apply]
  have hlocal := s2e_formal_factor_action_locality J I hJI α hJ hI E hE
  obtain ⟨D, hD⟩ := s2e_transitive_product_invariant_algebra
    (fun i => AdicCompletion (I i) A) δ i₀ htrans hlocal β hβ
  let C := s2e_intertwining_invariant_algebras_equiv E
    (fun g => (a g).toAlgHom) (fun g => (δ g).toAlgHom) (by
      intro g
      apply AlgHom.ext
      intro x
      change E (a g (E.symm (E x))) = E (a g x)
      rw [E.symm_apply_apply])
  refine ⟨C.trans D, ?_⟩
  intro v
  exact hD (C v)

end HodgeLean.Foundations.Program
