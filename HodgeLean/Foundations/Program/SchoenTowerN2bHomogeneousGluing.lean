import HodgeLean.Foundations.Program.SchoenTowerN2bHomogeneousEvaluation
import HodgeLean.Foundations.Program.SchoenTowerN2bProjectiveGluing

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial
open HodgeLean.Foundations
namespace HodgeLean.Foundations.Program
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Coordinate transition equations glue the actual homogeneous evaluations. -/
theorem n2b_glue_homogeneous_evaluations
    {X : Scheme.{0}} (𝒰 : X.OpenCover) {κ : Type}
    (q : ∀ i, ULift.{0} ℤ →+* Γ(𝒰.X i, ⊤))
    (a : ∀ i, κ → Γ(𝒰.X i, ⊤))
    (k : 𝒰.I₀ → κ) (hk : ∀ i, a i (k i) = 1)
    (hu : ∀ i j, ∃ u : Γ(pullback (𝒰.f i) (𝒰.f j), ⊤)ˣ,
      ∀ t, (pullback.snd (𝒰.f i) (𝒰.f j)).appTop.hom (a j t) =
        (u : Γ(pullback (𝒰.f i) (𝒰.f j), ⊤)) *
          (pullback.fst (𝒰.f i) (𝒰.f j)).appTop.hom (a i t)) :
    ∃ g : X ⟶ Proj (homogeneousSubmodule κ (ULift.{0} ℤ)), ∀ i,
      𝒰.f i ≫ g = Proj.fromOfGlobalSections (X := 𝒰.X i)
        (homogeneousSubmodule κ (ULift.{0} ℤ))
        (eval₂Hom (q i) (a i))
        (n2b_polynomial_evaluation_irrelevant (q i) (a i) (k i) (hk i)) := by
  apply n2b_glue_graded_chart_maps (homogeneousSubmodule κ (ULift.{0} ℤ)) 𝒰
    (fun i => eval₂Hom (q i) (a i))
    (fun i => n2b_polynomial_evaluation_irrelevant _ _ (k i) (hk i))
  intro i j
  obtain ⟨u, hu⟩ := hu i j
  refine ⟨u, fun d p hp => ?_⟩
  exact g3c_map_isHomogeneous_twist
    ((pullback.snd (𝒰.f i) (𝒰.f j)).appTop.hom.comp (eval₂Hom (q j) (a j)))
    ((pullback.fst (𝒰.f i) (𝒰.f j)).appTop.hom.comp (eval₂Hom (q i) (a i)))
    u (fun t => by simpa only [RingHom.comp_apply, eval₂Hom_X'] using hu t) hp

/-- An open cover detects equality of opens through its actual inclusions. -/
theorem n2b_opens_eq_of_cover_preimage {X : Scheme.{0}} (𝒰 : X.OpenCover)
    (U V : X.Opens) (h : ∀ i, 𝒰.f i ⁻¹ᵁ U = 𝒰.f i ⁻¹ᵁ V) : U = V := by
  ext x
  obtain ⟨y, hy⟩ := 𝒰.covers x
  have hi := congrArg (fun T : (𝒰.X (𝒰.idx x)).Opens => y ∈ T) (h (𝒰.idx x))
  change (𝒰.f (𝒰.idx x) y ∈ U) = (𝒰.f (𝒰.idx x) y ∈ V) at hi
  rw [hy] at hi
  exact iff_of_eq hi

end HodgeLean.Foundations.Program
