import HodgeLean.Foundations.Program.G32Native.CollectedPrimeProjection
import HodgeLean.Foundations.Program.G32Native.SelectedTowerForwardVector
import HodgeLean.Foundations.Program.G32Native.TowerClassAdjointComparison

noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicTopology.Singular
open HodgeLean.Adapters HodgeLean.Foundations.Program
open HodgeLean.Foundations.QuotientDuality HodgeLean.Foundations.Analytic
open scoped BigOperators Classical
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program.G32Native

/-- The selected tower's T14 class field from intrinsic P3a normalization,
T12 projection, and the retained T13 inverse-orbit equation.
Source: Schoen, Compositio Mathematica 65 (1988), pp. 15–18;
Fulton, Intersection Theory, second edition, 1.4 and 19.1–19.2.
-/
theorem selected_tower_p3a_classes
    {J : Over (Spec ↧ℂ)} [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom]
    (aut : g32p_G → (J ⟶ J)) (S : g32p_Supplier) (P : g32p_Part J aut S)
    {Q W W₀ N : Over (Spec ↧ℂ)} [IsIntegral Q.left]
    [IsIntegral W.left] [IsIntegral W₀.left]
    [IsProjective W.hom] [IsProjective W₀.hom]
    (eWr : N ≅ W) (d : N ⟶ N) (f : N ⟶ W₀)
    [IsProper (eWr.inv ≫ f).left]
    (horder : End.of d ^ S.m = 1)
    (ι : Q ⟶ W) [IsClosedImmersion ι.left]
    (U : W.left.Opens) (hU : Set.range ι.left ⊆ U)
    (hsm : Smooth (U.ι ≫ W.hom))
    (hcodim : ∀ t : Fin S.m, ∀ x ∈ (s2e_componentCycle
      (ι ≫ (End.of (eWr.inv ≫ d ≫ eWr.hom) ^ t.val).asHom) ℚ).support,
      Order.coheight x = P.k)
    (hdegree : ∀ t : Fin S.m, 0 < a1p_degree (eWr.inv ≫ f).left
      ((ι ≫ (End.of (eWr.inv ≫ d ≫ eWr.hom) ^ t.val).asHom).left (genericPoint Q.left)))
    (hdim : TopologicalSpace.dim W.left = 2*P.k)
    (hdim₀ : TopologicalSpace.dim W₀.left = 2*P.k)
    (o : LocalRationalOrientation (a3b4_an W.hom) (2*(2*P.k)))
    (cW : Homology ℚ (a3b4_an W.hom) (2*(2*P.k)))
    (ho : ∀ x, localOrientation (a3b4_an W.hom) (2*(2*P.k)) cW x = o.generator x)
    (hchart : ∀ (E : OpenPartialHomeomorph (ComplexPoint W) (Fin (2*P.k) → ℂ)),
      (∀ j, (f4_analytification W).IsHolFun (fun u : E.source => E u j)) →
      ∀ x (hx : x ∈ E.source), localOrientation (a3b4_an W.hom) (2*(2*P.k)) cW x =
        localClassOfChart (2*P.k) E x hx)
    (hp : Function.Injective (properCyclePairing (a3b4_an W.hom) P.k cW))
    (o₀ : LocalRationalOrientation (a3b4_an W₀.hom) (2*(2*P.k)))
    (c₀ : Homology ℚ (a3b4_an W₀.hom) (2*(2*P.k)))
    (ho₀ : ∀ x, localOrientation (a3b4_an W₀.hom) (2*(2*P.k)) c₀ x = o₀.generator x)
    (hchart₀ : ∀ (E : OpenPartialHomeomorph (ComplexPoint W₀) (Fin (2*P.k) → ℂ)),
      (∀ j, (f4_analytification W₀).IsHolFun (fun u : E.source => E u j)) →
      ∀ x (hx : x ∈ E.source), localOrientation (a3b4_an W₀.hom) (2*(2*P.k)) c₀ x =
        localClassOfChart (2*P.k) E x hx)
    (hp₀ : Function.Bijective (properCyclePairing (a3b4_an W₀.hom) P.k c₀))
    (G : Cohomology ℚ (a3b4_an W.hom) (2*P.k) →ₗ[ℚ]
      Cohomology ℚ (a3b4_an W₀.hom) (2*P.k))
    (hadjoint : ∀ x u, properCyclePairing (a3b4_an W₀.hom) P.k c₀ (G x) u =
      properCyclePairing (a3b4_an W.hom) P.k cW x
        (s2e_pullback ℚ (eWr.inv ≫ f) (2*P.k) u))
    (cSeed : s2e_supportedClass W (s2e_componentCycle ι ℚ) P.k)
    (hcSeed : a3b4_IsCycleClass W.hom (s2e_componentCycle ι ℚ) P.k cSeed)
    (coeffs : Fin (Nat.totient S.m) → Fin S.m → ℚ)
    (v : Fin (Nat.totient S.m) → Cohomology ℚ (a3b4_an W₀.hom) (2*P.k))
    (hT13 : ∀ j, v j = G (∑ t : Fin S.m, coeffs j t •
      s2e_pullback ℚ ((End.of (eWr.inv ≫ d ≫ eWr.hom) ^ (S.m - t.val)).asHom)
        (2*P.k) (s2e_classToAbsolute W (s2e_componentCycle ι ℚ) P.k cSeed))) :
    ∀ j,
      let γ := s2e_rationalOrbitCycle ι (eWr.inv ≫ d ≫ eWr.hom) S.m (coeffs j)
      (∀ x ∈ γ.support, Order.coheight x = P.k) ∧
      (∀ x ∈ (a1p_pushforward (eWr.inv ≫ f).left γ).support, Order.coheight x = P.k) ∧
      ∃ cr, a3b4_IsCycleClass W.hom γ P.k cr ∧
      ∃ c₀, a3b4_IsCycleClass W₀.hom (a1p_pushforward (eWr.inv ≫ f).left γ) P.k c₀ ∧
        G (s2e_classToAbsolute W γ P.k cr) = v j ∧
        s2e_classToAbsolute W₀ (a1p_pushforward (eWr.inv ≫ f).left γ) P.k c₀ = v j := by
  let δ := eWr.inv ≫ d ≫ eWr.hom
  let φ := eWr.inv ≫ f
  let ξ : Fin S.m → W.left := fun t =>
    (ι ≫ (End.of δ ^ t.val).asHom).left (genericPoint Q.left)
  have hc : ∀ t, Order.coheight (ξ t) = P.k := by
    intro t
    apply hcodim t
    rw [s2e_componentCycle_support]
    exact Set.mem_singleton _
  obtain ⟨a, ha, hprojection⟩ := collected_prime_projection φ P.k hdim hdim₀
    o cW ho hchart hp o₀ c₀ ho₀ hchart₀ hp₀.1 ξ hc hdegree
  have hseed : ∀ x ∈ (s2e_componentCycle ι ℚ).support, Order.coheight x = P.k := by
    simpa only [pow_zero, End.one_asHom, Category.comp_id] using
      hcodim (⟨0, by have := S.three_le; omega⟩ : Fin S.m)
  have hvector := selected_tower_forward_vector aut S P eWr d horder ι U hU hsm
    hseed cSeed hcSeed a ha G coeffs v hT13
  intro j
  obtain ⟨cr, hcr, habs, c, hclass, hpair⟩ := hprojection (coeffs j)
  change s2e_classToAbsolute W (s2e_rationalOrbitCycle ι δ S.m (coeffs j)) P.k cr = _ at habs
  have hs : G (s2e_classToAbsolute W
      (s2e_rationalOrbitCycle ι δ S.m (coeffs j)) P.k cr) = v j := by
    rw [habs]
    exact hvector j
  have ht := tower_normalized_push_eq_adjoint φ P.k
    (orientationIntegral (a3b4_an W.hom) (2*(2*P.k)) cW)
    (orientationIntegral (a3b4_an W₀.hom) (2*(2*P.k)) c₀)
    hp₀ G hadjoint (s2e_rationalOrbitCycle ι δ S.m (coeffs j)) cr c hpair
  exact ⟨s2e_rationalOrbitCycle_coheight ι δ P.k S.m hcodim (coeffs j),
    tower_orbit_pushed_coheight ι δ φ P.k S.m
      (fun t => (retained_positive_degree_coheight φ (2*P.k) hdim hdim₀ (ξ t)
        (hdegree t)).trans (hc t)) (coeffs j),
    cr, hcr, c, hclass, hs, ht.trans hs⟩

#print axioms selected_tower_p3a_classes
end HodgeLean.Foundations.Program.G32Native
