import HodgeLean.Foundations.Program.SchoenCycleComplexQuotientAdicStabilizerValues
import HodgeLean.Foundations.Program.SchoenCycleComplexAffineStalkInvariantValues
import HodgeLean.Foundations.Program.SchoenCycleAffineFormalPullback
import HodgeLean.Foundations.Program.SchoenCycleComplexQuotientAdicStabilizer
import HodgeLean.Foundations.Program.SchoenCycleComplexAffineStalkInvariants
import HodgeLean.Foundations.Program.SchoenCycleQuotientPointPrimeStabilizer

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
open scoped Pointwise
namespace HodgeLean.Foundations.Program

/-- Actual quotient formal point coordinates retain the geometric formal stalk pullback on every formal element.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Mumford–Fogarty–Kirwan, Geometric Invariant Theory, Chapter 1, §1. -/
theorem s2e_quotient_formal_point_values
    (X Y : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsIntegral Y.left]
    (G : Type) [Group G] [Fintype G]
    (a : G → (X ⟶ X)) (ha1 : a 1 = 𝟙 X)
    (hamul : ∀ u v, a (u * v) = a v ≫ a u)
    (q : X ⟶ Y) [IsFinite q.left] [Surjective q.left]
    (hinv : ∀ u, a u ≫ q = q)
    (hquot : ∀ (T : Over (Spec ↧ℂ)) (v : X ⟶ T),
      (∀ u, a u ≫ v = v) → ∃! w : Y ⟶ T, q ≫ w = v)
    (U : Y.left.Opens) (hU : IsAffineOpen U)
    (x : ComplexPoint X) (hx : x.underlying ∈ q.left ⁻¹ᵁ U)
    (hcx : IsClosed ({x.underlying} : Set X.left))
    (hcy : IsClosed ({q.left x.underlying} : Set Y.left)) :
    letI := s2e_step1_sectionAction X Y G a ha1 hamul q hinv U
    let I := ((hU.preimage q.left).primeIdealOf ⟨x.underlying, hx⟩).asIdeal
    let o : MulAction.orbit G I := ⟨I, MulAction.mem_orbit_self I⟩
    let H := MulAction.stabilizer G o
    ∃ hfix : ∀ g : H, (a g.val⁻¹).left x.underlying = x.underlying,
      let R := X.left.presheaf.stalk x.underlying
      let S := Y.left.presheaf.stalk (q.left x.underlying)
      letI : Algebra ℂ R := (HodgeLean.Foundations.Curves.stalkC x.underlying).toAlgebra
      letI : Algebra ℂ S := (HodgeLean.Foundations.Curves.stalkC (q.left x.underlying)).toAlgebra
      let β (g : H) : R →ₐ[ℂ] R :=
        { toRingHom := s2e_fixed_point_stalkPullback X.left (a g.val⁻¹).left x.underlying (hfix g)
          commutes' := s2e_fixed_point_stalkPullback_scalars X (a g.val⁻¹) x.underlying (hfix g) }
      let βhat g := s2e_adic_algebra_map _ _ (β g)
        (s2e_fixed_point_stalkPullback_power X.left (a g.val⁻¹).left x.underlying (hfix g))
      ∃ D : AdicCompletion (IsLocalRing.maximalIdeal S) S ≃ₐ[ℂ]
        (⨅ g, AlgHom.equalizer (βhat g) (AlgHom.id ℂ (AdicCompletion (IsLocalRing.maximalIdeal R) R)) :
          Subalgebra ℂ (AdicCompletion (IsLocalRing.maximalIdeal R) R)),
        ∀ z, (D z).val = s2e_formal_stalk_pullback X Y q x.underlying z := by
  let W := q.left ⁻¹ᵁ U
  have hW : IsAffineOpen W := hU.preimage q.left
  letI := s2e_step1_sectionAlgebra Y U
  letI := s2e_step1_sectionAlgebra X W
  letI : Algebra Γ(Y.left, U) Γ(X.left, W) := (q.left.app U).hom.toAlgebra
  letI := s2e_complex_section_app_tower X Y q U
  letI := s2e_step1_sectionAction X Y G a ha1 hamul q hinv U
  letI := s2e_quotient_sectionAction_base_smulComm X Y G a ha1 hamul q hinv U
  let I := (hW.primeIdealOf ⟨x.underlying, hx⟩).asIdeal
  let p := (hU.primeIdealOf ⟨q.left x.underlying, hx⟩).asIdeal
  letI : p.IsMaximal := hU.primeIdealOf_isMaximal_of_isClosed _ hcy
  have hI : I.LiesOver p := by
    constructor
    have he := congrArg PrimeSpectrum.asIdeal
      (IsAffineOpen.comap_primeIdealOf_appLE U hU W hW le_rfl hx (f := q.left))
    change I.comap (q.left.appLE U W le_rfl).hom = p at he
    rw [show q.left.appLE U W le_rfl = q.left.app U from Scheme.Hom.appLE_eq_app q.left] at he
    exact he.symm
  let o : MulAction.orbit G I := ⟨I, MulAction.mem_orbit_self I⟩
  let H := MulAction.stabilizer G o
  have hfix (g : H) : (a g.val⁻¹).left x.underlying = x.underlying := by
    have hi : g.val⁻¹ • I = I := congrArg Subtype.val (g⁻¹).property
    have he := (s2e_quotient_point_prime_stabilizer X Y G a ha1 hamul q hinv U hU x hx g.val⁻¹).mp hi
    exact congrArg Point.underlying he
  refine ⟨hfix, ?_⟩
  letI : Algebra ℂ (X.left.presheaf.stalk x.underlying) :=
    (HodgeLean.Foundations.Curves.stalkC x.underlying).toAlgebra
  letI : Algebra ℂ (Y.left.presheaf.stalk (q.left x.underlying)) :=
    (HodgeLean.Foundations.Curves.stalkC (q.left x.underlying)).toAlgebra
  obtain ⟨E, hE⟩ := s2e_complex_quotient_adic_stabilizer_values X Y G a ha1 hamul q hinv hquot U hU p I hI
  obtain ⟨hα, F, hF⟩ := s2e_complex_affine_stalk_invariant_values X H (fun g => a g.val⁻¹)
    x.underlying hfix W hW
    (fun g => s2e_step1_action_preimage X Y q (a g.val⁻¹) (hinv g.val⁻¹) U) hx hcx
  let EY := s2e_complex_affine_point_adic_equiv Y U hU (q.left x.underlying) hx hcy
  refine ⟨EY.symm.trans (E.trans F), ?_⟩
  intro z
  change (F (E (EY.symm z))).val = _
  rw [hF, hE]
  obtain ⟨hφ, hh⟩ := s2e_affine_formal_pullback X Y q U hU x.underlying hx hcx hcy
  have he := DFunLike.congr_fun hh (EY.symm z)
  change s2e_formal_stalk_pullback X Y q x.underlying (EY (EY.symm z)) = _ at he
  rw [EY.apply_symm_apply] at he
  exact he.symm

#print axioms s2e_quotient_formal_point_values
end HodgeLean.Foundations.Program
