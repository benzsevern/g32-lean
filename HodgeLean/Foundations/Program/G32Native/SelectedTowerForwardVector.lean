import HodgeLean.Foundations.Program.G32Native.CanonicalOrbitClasses
import HodgeLean.Foundations.Program.G32Native.SelectedTowerNormalOrbitBasis

/-! # The retained T13 vectors in the forward component convention -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
open HodgeLean.Adapters
open scoped BigOperators
namespace HodgeLean.Foundations.Program.G32Native

/-- T13's inverse pullbacks give T11's forward-component vector equation for
any normalized representatives of the same orbit. No coefficients are relabeled.
Source: Fulton, Intersection Theory, 19.2; Schoen (1988), printed p. 15. -/
theorem selected_tower_forward_vector
    {J : Over (Spec ↧ℂ)} [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom]
    (aut : g32p_G → (J ⟶ J)) (S : g32p_Supplier) (P : g32p_Part J aut S)
    {Q W W₀ N : Over (Spec ↧ℂ)} [IsIntegral Q.left]
    [LocallyOfFiniteType W.hom] [QuasiCompact W.hom] [IsSeparated W.hom]
    (eWr : N ≅ W) (d : N ⟶ N) (horder : End.of d ^ S.m = 1)
    (ι : Q ⟶ W) [IsClosedImmersion ι.left]
    (U : W.left.Opens) (hU : Set.range ι.left ⊆ U)
    (hsm : Smooth (U.ι ≫ W.hom))
    (hcodim : ∀ x ∈ (s2e_componentCycle ι ℚ).support, Order.coheight x = P.k)
    (cSeed : s2e_supportedClass W (s2e_componentCycle ι ℚ) P.k)
    (hcSeed : a3b4_IsCycleClass W.hom (s2e_componentCycle ι ℚ) P.k cSeed)
    (c : ∀ t : Fin S.m, s2e_supportedClass W
      (s2e_componentCycle (ι ≫ (End.of (eWr.inv ≫ d ≫ eWr.hom) ^ t.val).asHom) ℚ) P.k)
    (hc : ∀ t : Fin S.m, a3b4_IsCycleClass W.hom
      (s2e_componentCycle (ι ≫ (End.of (eWr.inv ≫ d ≫ eWr.hom) ^ t.val).asHom) ℚ) P.k (c t))
    (G : AlgebraicTopology.Singular.Cohomology ℚ (TopCat.of (ComplexPoint W)) (2 * P.k) →ₗ[ℚ]
      AlgebraicTopology.Singular.Cohomology ℚ (TopCat.of (ComplexPoint W₀)) (2 * P.k))
    (a : Fin (Nat.totient S.m) → Fin S.m → ℚ)
    (v : Fin (Nat.totient S.m) → AlgebraicTopology.Singular.Cohomology ℚ
      (TopCat.of (ComplexPoint W₀)) (2 * P.k))
    (hT13 : ∀ j, v j = G (∑ t : Fin S.m, a j t •
      s2e_pullback ℚ ((End.of (eWr.inv ≫ d ≫ eWr.hom) ^ (S.m - t.val)).asHom)
        (2 * P.k) (s2e_classToAbsolute W (s2e_componentCycle ι ℚ) P.k cSeed))) :
    ∀ j, G (∑ t : Fin S.m, a j t • s2e_classToAbsolute W
      (s2e_componentCycle (ι ≫ (End.of (eWr.inv ≫ d ≫ eWr.hom) ^ t.val).asHom) ℚ)
      P.k (c t)) = v j := by
  have hm : 0 < S.m := by have := S.three_le; omega
  have hperiod : End.of (eWr.inv ≫ d ≫ eWr.hom) ^ S.m = 1 := by
    have ho := congrArg eWr.conj horder
    rw [map_pow, map_one] at ho
    have he : eWr.conj (End.of d) = End.of (eWr.inv ≫ d ≫ eWr.hom) := by
      apply End.ext
      rw [Iso.conj_apply_asHom]
    rw [he] at ho
    exact ho
  have habs (t : Fin S.m) :
      s2e_classToAbsolute W
        (s2e_componentCycle (ι ≫ (End.of (eWr.inv ≫ d ≫ eWr.hom) ^ t.val).asHom) ℚ)
        P.k (c t) =
      s2e_pullback ℚ ((End.of (eWr.inv ≫ d ≫ eWr.hom) ^ (S.m - t.val)).asHom)
        (2 * P.k) (s2e_classToAbsolute W (s2e_componentCycle ι ℚ) P.k cSeed) := by
    letI := s2e_generator_power_isIso (eWr.inv ≫ d ≫ eWr.hom) hm.ne' hperiod t.val
    have he := s2e_componentCycle_absolute_deck_transport ι
      (End.of (eWr.inv ≫ d ≫ eWr.hom) ^ t.val).asHom P.k U hU hsm hcodim
      cSeed (c t) hcSeed (hc t)
    rw [endomorphism_inverse_power _ S.m hm hperiod t] at he
    exact he
  intro j
  rw [hT13 j]
  congr 1
  apply Finset.sum_congr rfl
  intro t _
  rw [habs t]

#print axioms selected_tower_forward_vector
end HodgeLean.Foundations.Program.G32Native
