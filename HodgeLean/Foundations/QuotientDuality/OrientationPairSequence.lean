import HodgeLean.Foundations.QuotientDuality.OrientationInvariantSequence
import HodgeLean.Foundations.QuotientDuality.OrientationRelative

/-! Equivariant singular pair sequences and their actual comparison maps. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

variable (G : Type) [Group G]

abbrev pairSubspaceChainAction (P : TopPair.{0}) (ρ : G →* End P) :
    G →* End ((relativeChainShortComplex ℚ P).X₁) :=
  (((chainPairFunctor ℚ) ⋙ Arrow.leftFunc).mapEnd P).comp ρ

abbrev pairAmbientChainAction (P : TopPair.{0}) (ρ : G →* End P) :
    G →* End ((relativeChainShortComplex ℚ P).X₂) :=
  (((chainPairFunctor ℚ) ⋙ Arrow.rightFunc).mapEnd P).comp ρ

abbrev pairRelativeChainAction (P : TopPair.{0}) (ρ : G →* End P) :
    G →* End ((relativeChainShortComplex ℚ P).X₃) :=
  ((relativeChainFunctor ℚ).mapEnd P).comp ρ

def relativeChainSequenceMap {P Q : TopPair.{0}} (f : P ⟶ Q) :
    relativeChainShortComplex ℚ P ⟶ relativeChainShortComplex ℚ Q where
  τ₁ := ((chainPairFunctor ℚ).map f).left
  τ₂ := ((chainPairFunctor ℚ).map f).right
  τ₃ := (relativeChainFunctor ℚ).map f
  comm₁₂ := ((chainPairFunctor ℚ).map f).w
  comm₂₃ := (TopPair.Homotopy.relativeChainProjection_naturality (R := ℚ) f).symm

lemma relative_invariant_comparison_quasiIso [Fintype G]
    {P Q : TopPair.{0}} (ρ : G →* End P) (f : P ⟶ Q)
    (h₁ : ∀ i, Function.Bijective (fun z :
      (complexHomologyRepresentation G (relativeChainShortComplex ℚ P).X₁
        (pairSubspaceChainAction G P ρ) i).invariants =>
        (HomologicalComplex.homologyMap ((chainPairFunctor ℚ).map f).left i).hom z.1))
    (h₂ : ∀ i, Function.Bijective (fun z :
      (complexHomologyRepresentation G (relativeChainShortComplex ℚ P).X₂
        (pairAmbientChainAction G P ρ) i).invariants =>
        (HomologicalComplex.homologyMap ((chainPairFunctor ℚ).map f).right i).hom z.1)) :
    QuasiIso (invariantChainInclusion G (relativeChainShortComplex ℚ P).X₃
      (pairRelativeChainAction G P ρ) ≫ (relativeChainFunctor ℚ).map f) := by
  have hf : ∀ g, (pairSubspaceChainAction G P ρ g).asHom ≫
        (relativeChainShortComplex ℚ P).f =
      (relativeChainShortComplex ℚ P).f ≫ (pairAmbientChainAction G P ρ g).asHom :=
    fun g => ((chainPairFunctor ℚ).map (ρ g).asHom).w
  have hg : ∀ g, (pairAmbientChainAction G P ρ g).asHom ≫
        (relativeChainShortComplex ℚ P).g =
      (relativeChainShortComplex ℚ P).g ≫ (pairRelativeChainAction G P ρ g).asHom :=
    fun g => (TopPair.Homotopy.relativeChainProjection_naturality (R := ℚ) (ρ g).asHom).symm
  exact invariant_sequence_comparison_quasiIso G (relativeChainShortComplex ℚ P)
    (relativeChainShortComplex ℚ Q) (pairSubspaceChainAction G P ρ)
    (pairAmbientChainAction G P ρ) (pairRelativeChainAction G P ρ) hf hg
    (relativeChainSequenceMap f) (relativeChainShortComplex_shortExact ℚ P)
    (relativeChainShortComplex_shortExact ℚ Q) h₁ h₂

end HodgeLean.Foundations.QuotientDuality
