import HodgeLean.Foundations.Program.SchoenCycleStep1AffineAction

/-! # The finite group action on an invariant chart ring -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
namespace HodgeLean.Foundations.Program

/-- Pullback preserves a base inverse-image chart. -/
theorem s2e_step1_action_preimage (X Y : Over (Spec ↧ℂ))
    (q : X ⟶ Y) (u : X ⟶ X) (hu : u ≫ q = q) (U : Y.left.Opens) :
    q.left ⁻¹ᵁ U ≤ u.left ⁻¹ᵁ (q.left ⁻¹ᵁ U) := by
  change q.left ⁻¹ᵁ U ≤ (u.left ≫ q.left) ⁻¹ᵁ U
  have he : u.left ≫ q.left = q.left := congrArg Over.Hom.left hu
  rw [he]

/-- The action on sections uses pullback by the inverse group element.
Source: Mumford--Fogarty--Kirwan, Geometric Invariant Theory, Chapter 1, section 1. -/
@[instance_reducible] def s2e_step1_sectionAction (X Y : Over (Spec ↧ℂ))
    (G : Type) [Group G] (a : G → (X ⟶ X))
    (ha1 : a 1 = 𝟙 X) (hamul : ∀ u v, a (u * v) = a v ≫ a u)
    (q : X ⟶ Y) (hinv : ∀ u, a u ≫ q = q) (U : Y.left.Opens) :
    MulSemiringAction G Γ(X.left, q.left ⁻¹ᵁ U) := by
  let W := q.left ⁻¹ᵁ U
  let ρ := fun u => (a u⁻¹).left.appLE W W (s2e_step1_action_preimage X Y q (a u⁻¹) (hinv u⁻¹) U)
  have h1 : ρ 1 = 𝟙 Γ(X.left, W) := by
    have he : (a 1).left = 𝟙 X.left := congrArg Over.Hom.left ha1
    have hc : ρ 1 = (𝟙 X.left : X.left ⟶ X.left).appLE W W le_rfl := by
      dsimp only [ρ]
      congr 1
      simpa only [inv_one] using he
    rw [hc]
    change (𝟙 Γ(X.left, W)) ≫ X.left.presheaf.map (𝟙 (Opposite.op W)) = _
    rw [X.left.presheaf.map_id, Category.id_comp]
  have hm : ∀ u v, ρ v ≫ ρ u = ρ (u * v) := by
    intro u v
    dsimp only [ρ]
    rw [Scheme.Hom.appLE_comp_appLE]
    congr 1
    rw [mul_inv_rev]
    exact (congrArg Over.Hom.left (hamul v⁻¹ u⁻¹)).symm
  exact
    { smul := fun u b => (ρ u).hom b
      one_smul := fun b => congrArg (fun t : Γ(X.left, W) ⟶ Γ(X.left, W) => t.hom b) h1
      mul_smul := fun u v b =>
        (congrArg (fun t : Γ(X.left, W) ⟶ Γ(X.left, W) => t.hom b) (hm u v)).symm
      smul_zero := fun u => (ρ u).hom.map_zero
      smul_add := fun u b c => (ρ u).hom.map_add b c
      smul_one := fun u => (ρ u).hom.map_one
      smul_mul := fun u b c => (ρ u).hom.map_mul b c }

/-- The chart action fixes the scalar functions. -/
theorem s2e_step1_sectionAction_smulComm (X Y : Over (Spec ↧ℂ))
    (G : Type) [Group G] (a : G → (X ⟶ X))
    (ha1 : a 1 = 𝟙 X) (hamul : ∀ u v, a (u * v) = a v ≫ a u)
    (q : X ⟶ Y) (hinv : ∀ u, a u ≫ q = q) (U : Y.left.Opens) :
    letI := s2e_step1_sectionAlgebra X (q.left ⁻¹ᵁ U)
    letI := s2e_step1_sectionAction X Y G a ha1 hamul q hinv U
    SMulCommClass G ℂ Γ(X.left, q.left ⁻¹ᵁ U) := by
  letI := s2e_step1_sectionAlgebra X (q.left ⁻¹ᵁ U)
  letI := s2e_step1_sectionAction X Y G a ha1 hamul q hinv U
  let W := q.left ⁻¹ᵁ U
  refine ⟨fun u c b => ?_⟩
  let ρ := (a u⁻¹).left.appLE W W (s2e_step1_action_preimage X Y q (a u⁻¹) (hinv u⁻¹) U)
  have he : X.hom.appLE ⊤ W le_top ≫ ρ = X.hom.appLE ⊤ W le_top := by
    dsimp only [ρ]
    rw [Scheme.Hom.appLE_comp_appLE]
    congr 1
    exact Over.w (a u⁻¹)
  have hs : (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv ≫ X.hom.appLE ⊤ W le_top ≫ ρ =
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv ≫ X.hom.appLE ⊤ W le_top := by rw [he]
  change ρ.hom ((algebraMap ℂ Γ(X.left, W) c) * b) =
    (algebraMap ℂ Γ(X.left, W) c) * ρ.hom b
  rw [map_mul]
  congr 1
  exact congrArg (fun t : CommRingCat.of ℂ ⟶ Γ(X.left, W) => t.hom c) hs

end HodgeLean.Foundations.Program
