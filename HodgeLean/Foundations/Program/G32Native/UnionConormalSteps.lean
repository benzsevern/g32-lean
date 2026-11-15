import HodgeLean.Foundations.Program.G32Native.UnionConormalGlobalExact
import HodgeLean.Foundations.Program.G32Native.UnionConormalLocalFramesMono
import HodgeLean.Foundations.Program.SchoenTowerConormalDefs
import HodgeLean.Foundations.Program.G32Native.UnionConormalComplex

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

/-- Right exactness of the natural ideal-intersection conormal complex.
There is no rank or generic-injectivity assertion in this step.
Source: Fulton, Intersection Theory, Appendix B.7.4, conormal sequences;
Schoen, Compositio Mathematica 65 (1988), Sublemma 2.7, pp. 16–17. -/
theorem union_conormal_right_exact_aux
    (V T T₁ T₂ S : Over (Spec ↧ℂ))
    [IsIntegral T₁.left] [Smooth V.hom] [Smooth T₁.hom] [Smooth T₂.hom]
    (t : T ⟶ V) (t₁ : T₁ ⟶ V) (t₂ : T₂ ⟶ V)
    [IsClosedImmersion t.left] [IsClosedImmersion t₁.left] [IsClosedImmersion t₂.left]
    (a : T₁ ⟶ T) (s₁ : S ⟶ T₁) (s₂ : S ⟶ T₂)
    [IsClosedImmersion a.left] [IsClosedImmersion s₁.left] [IsClosedImmersion s₂.left]
    (ha : a ≫ t = t₁) (hs : s₁ ≫ t₁ = s₂ ≫ t₂)
    (hunion : t.left.ker = t₁.left.ker ⊓ t₂.left.ker)
    (hinter : (s₁ ≫ t₁).left.ker = t₁.left.ker ⊔ t₂.left.ker)
 :
    (unionConormalComplex t.left t₁.left t₂.left a.left s₁.left s₂.left
      (congrArg Over.Hom.left ha) (congrArg Over.Hom.left hs) hunion).Exact ∧
    Epi (unionConormalLast t₁.left t₂.left s₁.left s₂.left
      (congrArg Over.Hom.left hs)) := by
  haveI : IsLocallyNoetherian V.left := LocallyOfFiniteType.isLocallyNoetherian V.hom
  exact ⟨unionConormal_exact_of_locallyNoetherian t.left t₁.left t₂.left a.left s₁.left s₂.left
      (congrArg Over.Hom.left ha) (congrArg Over.Hom.left hs) hunion hinter,
    unionConormalLast_epi t₁.left t₂.left s₁.left s₂.left
      (congrArg Over.Hom.left hs) hinter⟩

/-- The natural first conormal map is monic when its two locally free
terms have the same rank on the integral first component and the other
component does not contain it. This is the generic-rank step only.
Source: Schoen, Compositio Mathematica 65 (1988), proof of Sublemma 2.7,
pp. 16–17, equal-rank local freeness and generic injectivity. -/
theorem union_conormal_equal_rank_mono_aux
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
    Mono (unionConormalFirst t.left t₁.left a.left (congrArg Over.Hom.left ha)) := by
  exact unionConormal_mono_of_local_frames t.left t₁.left t₂.left a.left
    (congrArg Over.Hom.left ha) hunion hnot p hfree

#print axioms union_conormal_right_exact_aux
#print axioms union_conormal_equal_rank_mono_aux
end HodgeLean.Foundations.Program.G32Native
