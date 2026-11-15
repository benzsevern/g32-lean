import HodgeLean.Foundations.Program.SchoenCyclePrincipalDivisionColon
import HodgeLean.Foundations.Program.SchoenCycleQuotientSectionInvariance
import HodgeLean.Foundations.Program.SchoenCycleQuotientIdealJets
import HodgeLean.Foundations.Program.SchoenCycleInvariantPrincipalContraction
import HodgeLean.Foundations.Program.SchoenCycleLocalUnitApproximation

/-! # Principal divisibility in actual finite quotient stalks -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Principal divisibility of pulled-back sections at one tuple descends to the actual quotient stalk.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.4, printed p. 15;
Mumford–Fogarty–Kirwan, Geometric Invariant Theory, Chapter 1, §1. -/
theorem s2e_quotient_principal_stalk_divisibility
    (X Y : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsIntegral Y.left]
    (G : Type) [Group G] [Finite G]
    (a : G → (X ⟶ X)) (ha1 : a 1 = 𝟙 X)
    (hamul : ∀ u v, a (u * v) = a v ≫ a u)
    (q : X ⟶ Y) [IsFinite q.left] [Surjective q.left]
    (hinv : ∀ u, a u ≫ q = q)
    (hquot : ∀ (T : Over (Spec ↧ℂ)) (v : X ⟶ T),
      (∀ u, a u ≫ v = v) → ∃! w : Y ⟶ T, q ≫ w = v)
    (U : Y.left.affineOpens) (H : Subgroup G) (x : ComplexPoint X)
    (hxU : q.left x.underlying ∈ U.1)
    (hclosed : IsClosed ({x.underlying} : Set X.left))
    (hH : ∀ g, Point.map (a g) x = x ↔ g ∈ H)
    (c s : Γ(Y.left, U.1))
    (hreg : Function.Injective (fun z : Γ(X.left, q.left ⁻¹ᵁ U.1) =>
      (q.left.app U.1).hom c * z))
    (hd : q.left.stalkMap x.underlying
        (Y.left.presheaf.germ U.1 (q.left x.underlying) hxU c) ∣
      q.left.stalkMap x.underlying
        (Y.left.presheaf.germ U.1 (q.left x.underlying) hxU s)) :
    Y.left.presheaf.germ U.1 (q.left x.underlying) hxU c ∣
      Y.left.presheaf.germ U.1 (q.left x.underlying) hxU s := by
  let W := q.left ⁻¹ᵁ U.1
  let φ := (q.left.app U.1).hom
  let ψ := (X.left.presheaf.germ W x.underlying hxU).hom
  letI := s2e_step1_sectionAlgebra X W
  letI := s2e_step1_sectionAction X Y G a ha1 hamul q hinv U.1
  letI := s2e_step1_sectionAction_smulComm X Y G a ha1 hamul q hinv U.1
  let α := MulSemiringAction.toAlgAut G ℂ Γ(X.left, W)
  let K : Ideal Γ(X.left, W) := (Ideal.span {φ c}).colon ({φ s} : Set Γ(X.left, W))
  have hbase (g : G) (r : Γ(Y.left, U.1)) : α g (φ r) = φ r :=
    s2e_quotient_sectionAction_fixes_pullback X Y G a ha1 hamul q hinv U.1 g r
  have hK : ∀ g, ∀ z ∈ K, α g z ∈ K :=
    s2e_invariant_principal_division_colon_stable α (φ c) (φ s)
      (fun g => hbase g c) (fun g => hbase g s)
  letI : Algebra Γ(X.left, W) (X.left.presheaf.stalk x.underlying) := ψ.toAlgebra
  letI := (U.2.preimage q.left).isLocalization_stalk ⟨x.underlying, hxU⟩
  have hd' : ψ (φ c) ∣ ψ (φ s) := by
    simpa only [q.left.germ_stalkMap_apply U.1 x.underlying hxU] using hd
  have hKtop : K.map ψ = ⊤ :=
    s2e_localized_principal_division_colon_top
      ((U.2.preimage q.left).primeIdealOf ⟨x.underlying, hxU⟩).asIdeal.primeCompl
      (φ c) (φ s) hd'
  have hx : ⊤ ≤ x.left ⁻¹ᵁ W := s2e_step1_point_preimage X x W hxU
  obtain ⟨d, hdK, hjet⟩ := s2e_quotient_invariant_stalk_ideal_jet_descent X Y G a ha1 hamul
    q hinv hquot U.1 U.2 H x hx hclosed hH K hK 1 1
    (by rw [hKtop]; exact Submodule.mem_top)
    (by intro g hg; rw [map_one, sub_self]; exact Ideal.zero_mem _)
  have hdu : IsUnit (ψ (φ d)) := by
    apply s2e_isUnit_of_product_approximation
      (IsLocalRing.maximalIdeal (X.left.presheaf.stalk x.underlying)) 1 (ψ (φ d))
      (IsLocalRing.notMem_maximalIdeal.mpr isUnit_one)
    simpa only [one_mul, pow_one] using hjet
  have hdunit : IsUnit (Y.left.presheaf.germ U.1 (q.left x.underlying) hxU d) := by
    apply (isUnit_map_iff (q.left.stalkMap x.underlying).hom _).mp
    simpa only [q.left.germ_stalkMap_apply U.1 x.underlying hxU] using hdu
  have hdesc (z : Γ(X.left, W)) (hz : ∀ g, α g z = z) :
      ∃ r : Γ(Y.left, U.1), φ r = z := by
    have hi (g : G) : ((a g).left.appLE W W
        (s2e_step1_action_preimage X Y q (a g) (hinv g) U.1)).hom z = z := by
      have h := hz g⁻¹
      change ((a ((g⁻¹)⁻¹)).left.appLE W W _).hom z = z at h
      simpa only [inv_inv] using h
    obtain ⟨r, hr, _⟩ := s2e_step1_invariant_affine_descent X Y G a ha1 hamul q hinv hquot
      U.1 U.2 z hi
    exact ⟨r, hr⟩
  letI := IsSchemeTheoreticallyDominant.of_isDominant q.left
  have heq := s2e_invariant_regular_principal_contraction α φ
    (q.left.app_injective U.1) hbase hdesc c hreg
  have hds : d * s ∈ Ideal.span {c} := by
    rw [← heq]
    change φ (d * s) ∈ Ideal.span {φ c}
    rw [map_mul]
    exact Submodule.mem_colon_singleton.mp hdK
  have hg := Ideal.mem_map_of_mem
    (Y.left.presheaf.germ U.1 (q.left x.underlying) hxU).hom hds
  rw [Ideal.map_span, Set.image_singleton, map_mul] at hg
  exact Ideal.mem_span_singleton.mp
    ((Ideal.unit_mul_mem_iff_mem _ hdunit).mp hg)

end HodgeLean.Foundations.Program
