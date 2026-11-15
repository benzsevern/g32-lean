import HodgeLean.Foundations.Program.SchoenCycleFormalStalkPullback
import HodgeLean.Foundations.Program.SchoenCycleComplexAffineAdicValues
import HodgeLean.Foundations.Program.SchoenCycleComplexSectionTower
import HodgeLean.Foundations.Program.SchoenCycleAdicBasePowers

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- The canonical affine formal germ comparisons intertwine actual section pullback and actual geometric formal stalk pullback.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Hartshorne, Algebraic Geometry, II.2; Atiyah–Macdonald, Chapter 10. -/
theorem s2e_affine_formal_pullback
    (X Y : Over (Spec ↧ℂ)) [IsIntegral X.left] [IsIntegral Y.left]
    (f : X ⟶ Y) [IsFinite f.left]
    (U : Y.left.Opens) (hU : IsAffineOpen U)
    (x : X.left) (hx : x ∈ f.left ⁻¹ᵁ U)
    (hcx : IsClosed ({x} : Set X.left)) (hcy : IsClosed ({f.left x} : Set Y.left)) :
    let W := f.left ⁻¹ᵁ U
    letI := s2e_step1_sectionAlgebra Y U
    letI := s2e_step1_sectionAlgebra X W
    letI : Algebra Γ(Y.left, U) Γ(X.left, W) := (f.left.app U).hom.toAlgebra
    letI := s2e_complex_section_app_tower X Y f U
    letI : Algebra ℂ (X.left.presheaf.stalk x) := (HodgeLean.Foundations.Curves.stalkC x).toAlgebra
    letI : Algebra ℂ (Y.left.presheaf.stalk (f.left x)) :=
      (HodgeLean.Foundations.Curves.stalkC (f.left x)).toAlgebra
    let p := (hU.primeIdealOf ⟨f.left x, hx⟩).asIdeal
    let I := ((hU.preimage f.left).primeIdealOf ⟨x, hx⟩).asIdeal
    let φ := (Algebra.ofId Γ(Y.left, U) Γ(X.left, W)).restrictScalars ℂ
    ∃ hφ : ∀ N a, a ∈ p ^ N → φ a ∈ I ^ N,
      (s2e_formal_stalk_pullback X Y f x).comp
        (s2e_complex_affine_point_adic_equiv Y U hU (f.left x) hx hcy).toAlgHom =
      (s2e_complex_affine_point_adic_equiv X W (hU.preimage f.left) x hx hcx).toAlgHom.comp
        (s2e_adic_algebra_map p I φ hφ) := by
  dsimp only
  let W := f.left ⁻¹ᵁ U
  letI := s2e_step1_sectionAlgebra Y U
  letI := s2e_step1_sectionAlgebra X W
  letI : Algebra Γ(Y.left, U) Γ(X.left, W) := (f.left.app U).hom.toAlgebra
  letI := s2e_complex_section_app_tower X Y f U
  letI : Algebra ℂ (X.left.presheaf.stalk x) := (HodgeLean.Foundations.Curves.stalkC x).toAlgebra
  letI : Algebra ℂ (Y.left.presheaf.stalk (f.left x)) :=
    (HodgeLean.Foundations.Curves.stalkC (f.left x)).toAlgebra
  let p := (hU.primeIdealOf ⟨f.left x, hx⟩).asIdeal
  let I := ((hU.preimage f.left).primeIdealOf ⟨x, hx⟩).asIdeal
  let φ := (Algebra.ofId Γ(Y.left, U) Γ(X.left, W)).restrictScalars ℂ
  have hbase : p ≤ I.comap (f.left.app U).hom := by
    have he := congrArg PrimeSpectrum.asIdeal
      (IsAffineOpen.comap_primeIdealOf_appLE U hU W (hU.preimage f.left) le_rfl hx (f := f.left))
    change I.comap (f.left.appLE U W le_rfl).hom = p at he
    rw [show f.left.appLE U W le_rfl = f.left.app U from Scheme.Hom.appLE_eq_app f.left] at he
    exact le_of_eq he.symm
  have hφ (N : ℕ) (a : Γ(Y.left, U)) (ha : a ∈ p ^ N) : φ a ∈ I ^ N := by
    exact (Ideal.pow_right_mono (Ideal.map_le_iff_le_comap.mpr hbase) N)
      (s2e_base_map_preserves_extended_ideal_powers p N a ha)
  refine ⟨hφ, ?_⟩
  apply AlgHom.ext
  intro z
  apply AdicCompletion.ext
  intro N
  change Ideal.quotientMapₐ (IsLocalRing.maximalIdeal (X.left.presheaf.stalk x) ^ N • ⊤ : Ideal _)
      (s2e_complex_stalk_pullback X Y f x) _
      (Ideal.quotientMapₐ (IsLocalRing.maximalIdeal (Y.left.presheaf.stalk (f.left x)) ^ N • ⊤ : Ideal _)
        (s2e_complex_section_germ Y U (f.left x) hx) _ (z.val N)) =
    Ideal.quotientMapₐ (IsLocalRing.maximalIdeal (X.left.presheaf.stalk x) ^ N • ⊤ : Ideal _)
      (s2e_complex_section_germ X W x hx) _
      (Ideal.quotientMapₐ (I ^ N • ⊤ : Ideal Γ(X.left, W)) φ _ (z.val N))
  refine Quotient.inductionOn' (z.val N) (fun a => ?_)
  apply congrArg (Ideal.Quotient.mk _)
  exact congrArg (fun k : Γ(Y.left, U) ⟶ X.left.presheaf.stalk x => k.hom a)
    (f.left.germ_stalkMap U x hx)

#print axioms s2e_affine_formal_pullback
end HodgeLean.Foundations.Program
