import HodgeLean.Foundations.AbelianQuotient.CharacterDescent
import HodgeLean.Foundations.AbelianQuotient.Injectivity

noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
open HodgeLean.RealDefs HodgeLean.Foundations HodgeLean.Adapters
open scoped CategoryTheory.MonObj
namespace HodgeLean.Foundations.AbelianQuotient

/-- A surjective homomorphism lifts a positive multiple of every target period additively. -/
theorem lattice_multiple_lift {P Q : Variety} (f : Hom P Q)
    (hs : Function.Surjective (Point.map f.hom))
    (A : (Fin (dim P.X.left) → ℂ) →ₗ[ℂ] (Fin (dim Q.X.left) → ℂ))
    (hA : ∀ v, Additive.toMul (complexExponential Q.X (dim Q.X.left) (A v)) =
      Point.map f.hom (Additive.toMul (complexExponential P.X (dim P.X.left) v))) :
    ∃ (N : ℕ) (ψ : abelianPeriodLattice Q.X →+ abelianPeriodLattice P.X),
      0 < N ∧ ∀ l, A (ψ l) = N • (l : Fin (dim Q.X.left) → ℂ) := by
  have hi := injective_pullback_of_surjective f hs
  let T := (homPullback f.hom 1).leftInverse
  have hT : ∀ x, T (homPullback f.hom 1 x) = x :=
    LinearMap.leftInverse_apply_of_inj (LinearMap.ker_eq_bot.mpr hi)
  obtain ⟨N, hN, ψ, hψ⟩ := period_transpose P Q T
  refine ⟨N, ψ, hN, fun l => ?_⟩
  have h := lattice_eq_of_period Q (a :=
    ⟨A (ψ l), homPullback_analyticRepresentation_mem_lattice f.hom A hA (ψ l)⟩)
    (b := N • l) ?_
  · exact congrArg Subtype.val h
  intro x
  rw [← abelianPeriod_homPullback_analyticRepresentation f.hom A hA x (ψ l),
    ← hψ, hT, map_smul, Pi.smul_apply]
  change (N : ℚ) * abelianPeriod Q.X x l = _
  obtain ⟨e, he⟩ := spec_abelianPeriod_equiv Q.X
  simp only [← he, map_nsmul, nsmul_eq_mul]

/-- Vanishing on the subvariety forces vanishing on projection-kernel periods. -/
theorem quotient_kernel_period_zero {A : Variety} {S : Subvariety A} (q : Projection S)
    (hk : {a : ComplexPoint A.X | Point.map q.map.hom a = 1} =
      Set.range (Point.map S.inclusion.hom))
    (I : (Fin (dim S.B.X.left) → ℂ) →ₗ[ℂ] (Fin (dim A.X.left) → ℂ))
    (Q : (Fin (dim A.X.left) → ℂ) →ₗ[ℂ] (Fin (dim q.Q.X.left) → ℂ))
    (hI : ∀ v, Additive.toMul (complexExponential A.X (dim A.X.left) (I v)) =
      Point.map S.inclusion.hom (Additive.toMul
        (complexExponential S.B.X (dim S.B.X.left) v)))
    (hQ : ∀ v, Additive.toMul (complexExponential q.Q.X (dim q.Q.X.left) (Q v)) =
      Point.map q.map.hom (Additive.toMul (complexExponential A.X (dim A.X.left) v)))
    (x : HQ A.X 1) (hx : homPullback S.inclusion.hom 1 x = 0)
    (l : abelianPeriodLattice A.X) (hl : Q l = 0) : abelianPeriod A.X x l = 0 := by
  obtain ⟨e, he⟩ := spec_abelianPeriod_equiv A.X
  obtain ⟨F, hF⟩ := exists_real_period_extension A (e x)
  have hFI := period_extension_comp_zero S.inclusion I hI x hx (e x) (he x) F hF
  obtain ⟨w, hw⟩ := quotient_tangent_kernel q hk I Q hI hQ hl
  have hz : F (l : Fin (dim A.X.left) → ℂ) = 0 := by
    rw [← hw]
    exact LinearMap.congr_fun hFI w
  rw [hF] at hz
  rw [← he]
  exact_mod_cast hz

end HodgeLean.Foundations.AbelianQuotient
