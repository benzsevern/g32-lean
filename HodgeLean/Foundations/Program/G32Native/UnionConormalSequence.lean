import HodgeLean.Foundations.Program.SchoenTowerConormalDefs
import HodgeLean.Foundations.Program.G32Native.UnionConormalSteps

/-! # Conormal sequence for two components of a complete intersection

Local freeness of the two source conormals is stated directly. Together
with the dense complement of the second component, this is the input to
the equal-rank injectivity argument in Sublemma 2.7.
-/
noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Program

/-- The union/intersection conormal sequence on the first component.
The last sheaf is pushed from the intersection to that component.
Source: Schoen, Compositio Mathematica 65 (1988), Sublemma 2.7, pp. 16–17;
the local-freeness hypotheses isolate the equal-rank argument in its proof. -/
theorem union_conormal_sequence_aux
    (V T T₁ T₂ S : Over (Spec ↧ℂ))
    [IsIntegral T₁.left] [Smooth V.hom] [Smooth T₁.hom] [Smooth T₂.hom]
    (t : T ⟶ V) (t₁ : T₁ ⟶ V) (t₂ : T₂ ⟶ V)
    [IsClosedImmersion t.left] [IsClosedImmersion t₁.left] [IsClosedImmersion t₂.left]
    (a : T₁ ⟶ T) (s₁ : S ⟶ T₁) (s₂ : S ⟶ T₂)
    [IsClosedImmersion a.left] [IsClosedImmersion s₁.left] [IsClosedImmersion s₂.left]
    (ha : a ≫ t = t₁) (hs : s₁ ≫ t₁ = s₂ ≫ t₂)
    (hunion : t.left.ker = t₁.left.ker ⊓ t₂.left.ker)
    (hinter : (s₁ ≫ t₁).left.ker = t₁.left.ker ⊔ t₂.left.ker)
    (hnot : ¬ Set.range t₁.left ⊆ Set.range t₂.left)
    (p : ℕ)
    (hfree : ∀ x : T₁.left, ∃ U : T₁.left.Opens, x ∈ U ∧
      Nonempty (Scheme.Modules.restrict
        ((Scheme.Modules.pullback a.left).obj (s2c_conormal t.left)) U.ι ≅
        (SheafOfModules.free (R := U.toScheme.ringCatSheaf) (Fin p) : U.toScheme.Modules)) ∧
      Nonempty (Scheme.Modules.restrict (s2c_conormal t₁.left) U.ι ≅
        (SheafOfModules.free (R := U.toScheme.ringCatSheaf) (Fin p) : U.toScheme.Modules))) :
    ∃ (f : (Scheme.Modules.pullback a.left).obj (s2c_conormal t.left) ⟶
        s2c_conormal t₁.left)
      (g : s2c_conormal t₁.left ⟶
        (Scheme.Modules.pushforward s₁.left).obj (s2c_conormal s₂.left))
      (hfg : f ≫ g = 0), (ShortComplex.mk f g hfg).ShortExact := by
  let C := unionConormalComplex t.left t₁.left t₂.left a.left s₁.left s₂.left
    (congrArg Over.Hom.left ha) (congrArg Over.Hom.left hs) hunion
  obtain ⟨he, hg⟩ := union_conormal_right_exact_aux V T T₁ T₂ S t t₁ t₂ a s₁ s₂
    ha hs hunion hinter
  have hf := union_conormal_equal_rank_mono_aux V T T₁ T₂ S t t₁ t₂ a s₁ s₂
    ha hs hunion hinter hnot p hfree
  exact ⟨C.f, C.g, C.zero, ShortComplex.ShortExact.mk' he hf hg⟩

#print axioms union_conormal_sequence_aux

end HodgeLean.Foundations.Program.G32Native
