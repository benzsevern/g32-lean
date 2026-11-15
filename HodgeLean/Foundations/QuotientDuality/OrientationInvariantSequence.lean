import HodgeLean.Foundations.QuotientDuality.OrientationInvariantMaps
import Mathlib.Algebra.Homology.HomologySequenceLemmas

/-! Comparisons from fixed short exact chain sequences. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory
namespace HodgeLean.Foundations.QuotientDuality

variable (G : Type) [Group G]
    (S T : ShortComplex (ChainComplex (ModuleCat ℚ) ℕ))
    (ρ₁ : G →* End S.X₁) (ρ₂ : G →* End S.X₂) (ρ₃ : G →* End S.X₃)
    (hf : ∀ g, (ρ₁ g).asHom ≫ S.f = S.f ≫ (ρ₂ g).asHom)
    (hg : ∀ g, (ρ₂ g).asHom ≫ S.g = S.g ≫ (ρ₃ g).asHom)
    (φ : S ⟶ T)

def invariantShortComplexComparison :
    (equivariantShortComplex G S ρ₁ ρ₂ ρ₃ hf hg).map
      ((Rep.invariantsFunctor ℚ G).mapHomologicalComplex (.down ℕ)) ⟶ T where
  τ₁ := invariantChainInclusion G S.X₁ ρ₁ ≫ φ.τ₁
  τ₂ := invariantChainInclusion G S.X₂ ρ₂ ≫ φ.τ₂
  τ₃ := invariantChainInclusion G S.X₃ ρ₃ ≫ φ.τ₃
  comm₁₂ := by
    let I := (Rep.invariantsFunctor ℚ G).mapHomologicalComplex (.down ℕ)
    let f := equivariantChainMap G ρ₁ ρ₂ S.f hf
    have hi : I.map f ≫ invariantChainInclusion G S.X₂ ρ₂ =
        invariantChainInclusion G S.X₁ ρ₁ ≫ S.f :=
      (NatTrans.mapHomologicalComplex (invariantsInclusionNat G) (.down ℕ)).naturality f
    symm
    change I.map f ≫ (invariantChainInclusion G S.X₂ ρ₂ ≫ φ.τ₂) = _
    rw [← Category.assoc, hi, Category.assoc, ← φ.comm₁₂, ← Category.assoc]
  comm₂₃ := by
    let I := (Rep.invariantsFunctor ℚ G).mapHomologicalComplex (.down ℕ)
    let g := equivariantChainMap G ρ₂ ρ₃ S.g hg
    have hi : I.map g ≫ invariantChainInclusion G S.X₃ ρ₃ =
        invariantChainInclusion G S.X₂ ρ₂ ≫ S.g :=
      (NatTrans.mapHomologicalComplex (invariantsInclusionNat G) (.down ℕ)).naturality g
    symm
    change I.map g ≫ (invariantChainInclusion G S.X₃ ρ₃ ≫ φ.τ₃) = _
    rw [← Category.assoc, hi, Category.assoc, ← φ.comm₂₃, ← Category.assoc]

include hf hg in
lemma invariant_sequence_comparison_quasiIso [Fintype G]
    (hS : S.ShortExact) (hT : T.ShortExact)
    (h₁ : ∀ i, Function.Bijective (fun z :
      (complexHomologyRepresentation G S.X₁ ρ₁ i).invariants =>
        (HomologicalComplex.homologyMap φ.τ₁ i).hom z.1))
    (h₂ : ∀ i, Function.Bijective (fun z :
      (complexHomologyRepresentation G S.X₂ ρ₂ i).invariants =>
        (HomologicalComplex.homologyMap φ.τ₂ i).hom z.1)) :
    QuasiIso (invariantChainInclusion G S.X₃ ρ₃ ≫ φ.τ₃) := by
  let ψ := invariantShortComplexComparison G S T ρ₁ ρ₂ ρ₃ hf hg φ
  exact HomologicalComplex.HomologySequence.quasiIso_τ₃ ψ
    (invariantChainShortComplex_shortExact G _
      (equivariantShortComplex_shortExact G S ρ₁ ρ₂ ρ₃ hf hg hS)) hT
    (invariant_map_quasiIso G ρ₁ φ.τ₁ h₁) (invariant_map_quasiIso G ρ₂ φ.τ₂ h₂)

end HodgeLean.Foundations.QuotientDuality
