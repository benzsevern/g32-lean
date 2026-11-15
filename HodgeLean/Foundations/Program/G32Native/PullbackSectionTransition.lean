import HodgeLean.Foundations.Program.G32Native.AppLECongruence
import Mathlib.AlgebraicGeometry.Limits

/-! Transport of section transitions to overlaps of source charts. -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- A scalar relation on intersecting base opens pulls back to an overlap of charts over that base. -/
theorem g32l4_pullback_section_transition {X T A B : Scheme.{0}} {K : Type}
    (π : T ⟶ X) (f : A ⟶ T) (g : B ⟶ T) (V W : X.Opens)
    (hf : ⊤ ≤ (f ≫ π) ⁻¹ᵁ V) (hg : ⊤ ≤ (g ≫ π) ⁻¹ᵁ W)
    (s : K → Γ(X, V)) (t : K → Γ(X, W)) (c : Γ(X, V ⊓ W))
    (h : ∀ k, X.presheaf.map (homOfLE (inf_le_left : V ⊓ W ≤ V)).op (s k) =
      c * X.presheaf.map (homOfLE (inf_le_right : V ⊓ W ≤ W)).op (t k)) :
    ∃ c' : Γ(pullback f g, ⊤), ∀ k,
      (pullback.fst f g).appTop.hom ((f ≫ π).appLE V ⊤ hf (s k)) =
        c' * (pullback.snd f g).appTop.hom ((g ≫ π).appLE W ⊤ hg (t k)) := by
  let p := pullback.fst f g
  let q := pullback.snd f g
  let e := p ≫ (f ≫ π)
  have heq : e = q ≫ (g ≫ π) := pullback.condition_assoc π
  have heV : ⊤ ≤ e ⁻¹ᵁ V := by
    intro z _
    change (f ≫ π) (p z) ∈ V
    exact hf (by trivial)
  have heW : ⊤ ≤ e ⁻¹ᵁ W := by
    rw [heq]
    intro z _
    change (g ≫ π) (q z) ∈ W
    exact hg (by trivial)
  have heVW : ⊤ ≤ e ⁻¹ᵁ (V ⊓ W) := by
    intro z hz
    exact ⟨heV hz, heW hz⟩
  let ψ := e.appLE (V ⊓ W) ⊤ heVW
  have hpTop : p.appTop = p.appLE ⊤ ⊤ (by simp) := by simp [Scheme.Hom.appLE]
  have hqTop : q.appTop = q.appLE ⊤ ⊤ (by simp) := by simp [Scheme.Hom.appLE]
  have hl : X.presheaf.map (homOfLE (inf_le_left : V ⊓ W ≤ V)).op ≫ ψ =
      (f ≫ π).appLE V ⊤ hf ≫ p.appTop := by
    rw [Scheme.Hom.map_appLE]
    rw [hpTop, Scheme.Hom.appLE_comp_appLE]
  have hr : X.presheaf.map (homOfLE (inf_le_right : V ⊓ W ≤ W)).op ≫ ψ =
      (g ≫ π).appLE W ⊤ hg ≫ q.appTop := by
    rw [Scheme.Hom.map_appLE]
    rw [hqTop, Scheme.Hom.appLE_comp_appLE]
    exact g32l4_appLE_congr_morphism heq W ⊤ _ _
  refine ⟨ψ c, fun k => ?_⟩
  have hh := congrArg (fun z => ψ z) (h k)
  rw [map_mul] at hh
  change (X.presheaf.map (homOfLE inf_le_left).op ≫ ψ).hom (s k) =
    ψ c * (X.presheaf.map (homOfLE inf_le_right).op ≫ ψ).hom (t k) at hh
  rw [hl, hr] at hh
  exact hh

end HodgeLean.Foundations.Program
