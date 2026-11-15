import HodgeLean.Foundations.Program.SchoenCycleAdicAlgebraAction
import HodgeLean.Foundations.Program.SchoenCycleAdicProjectionNaturality

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- Transport of the actual adic group action depends only on the transported factor's original value.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Mumford–Fogarty–Kirwan, Geometric Invariant Theory, Chapter 1, §1. -/
theorem s2e_formal_factor_action_locality
    {k A G ι : Type*} [CommRing k] [CommRing A] [Algebra k A]
    [Group G] [MulAction G ι]
    (J : Ideal A) (I : ι → Ideal A) (hJI : ∀ i, J ≤ I i)
    (α : G →* (A ≃ₐ[k] A))
    (hJ : ∀ (g : G) (n : ℕ) (a : A), a ∈ J ^ n → α g a ∈ J ^ n)
    (hI : ∀ (g : G) (i : ι) (n : ℕ) (a : A), a ∈ I i ^ n → α g a ∈ I (g • i) ^ n)
    (E : AdicCompletion J A ≃ₐ[k] (∀ i, AdicCompletion (I i) A))
    (hE : ∀ (x : AdicCompletion J A) (i : ι), E x i =
      s2e_adic_algebra_map J (I i) (AlgHom.id k A)
        (fun n a ha => (Ideal.pow_right_mono (hJI i) n) ha) x) :
    let δ := (AlgEquiv.autCongr E).toMonoidHom.comp (s2e_adic_group_algebra_action J α hJ)
    ∀ (g : G) (i : ι) (v w : ∀ j, AdicCompletion (I j) A),
      v i = w i → (δ g v) (g • i) = (δ g w) (g • i) := by
  dsimp only
  have hc (g : G) (i : ι) (x : AdicCompletion J A) :
      E (s2e_adic_algebra_map J J (α g).toAlgHom (hJ g) x) (g • i) =
        s2e_adic_algebra_map (I i) (I (g • i)) (α g).toAlgHom (hI g i) (E x i) := by
    calc
      _ = s2e_adic_algebra_map J (I (g • i)) (AlgHom.id k A)
          (fun n a ha => (Ideal.pow_right_mono (hJI (g • i)) n) ha)
          (s2e_adic_algebra_map J J (α g).toAlgHom (hJ g) x) := hE _ _
      _ = s2e_adic_algebra_map (I i) (I (g • i)) (α g).toAlgHom (hI g i)
          (s2e_adic_algebra_map J (I i) (AlgHom.id k A)
            (fun n a ha => (Ideal.pow_right_mono (hJI i) n) ha) x) :=
        s2e_adic_projection_naturality J (I i) (I (g • i)) (hJI i) (hJI (g • i))
          (α g).toAlgHom (hJ g) (hI g i) x
      _ = _ := congrArg _ (hE x i).symm
  intro g i v w hvw
  change E (s2e_adic_algebra_map J J (α g).toAlgHom (hJ g) (E.symm v)) (g • i) =
    E (s2e_adic_algebra_map J J (α g).toAlgHom (hJ g) (E.symm w)) (g • i)
  rw [hc, hc, E.apply_symm_apply, E.apply_symm_apply, hvw]

end HodgeLean.Foundations.Program
