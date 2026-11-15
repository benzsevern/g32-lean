import HodgeLean.Foundations.BundleThom.LocalMatrixInterpolationHelpers

/-! # Actual product normal pairs and varying matrix maps

The base is retained in the source pair, and every map preserves the punctured normal support.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory TopologicalSpace AlgebraicTopology.Singular
namespace HodgeLean.Foundations.BundleThom

/-- The actual product normal complement pair over a supplied topological base.
Source: Bott–Tu, Differential Forms in Algebraic Topology, §6, trivial normal charts. -/
def i1_productNormalPair (B : Type) [TopologicalSpace B] (k : ℕ) : TopPair :=
  TopPair.ofSubset (X := TopCat.of (B × (Fin k → ℂ))) {p | p.2 ≠ 0}

/-- Projection from an actual product complement pair to its punctured complex normal model.
Source: Bott–Tu, Differential Forms in Algebraic Topology, §6, normal orientation. -/
def i1_productNormalProjection (B : Type) [TopologicalSpace B] (k : ℕ) :
    i1_productNormalPair B k ⟶ puncturedPair ℂ k :=
  TopPair.ofSubsetHom (TopCat.ofHom ⟨Prod.snd, continuous_snd⟩) (fun _ h => h)

/-- An actual continuous family of invertible complex matrices acts on the product normal pair.
Source: Bott–Tu, Differential Forms in Algebraic Topology, §6, complex frame changes. -/
def i1_productMatrixNormalMap {B : Type} [TopologicalSpace B] (k : ℕ)
    (A : B → Matrix (Fin k) (Fin k) ℂ) (hA : Continuous A) (hdet : ∀ b, (A b).det ≠ 0) :
    i1_productNormalPair B k ⟶ puncturedPair ℂ k :=
  TopPair.ofSubsetHom (TopCat.ofHom
    ⟨fun p => (A p.1).mulVec p.2, (hA.comp continuous_fst).matrix_mulVec continuous_snd⟩) (by
      intro p hp hz
      apply hp
      apply (A p.1).mulVec_injective_of_det_ne_zero (hdet p.1)
      simpa using hz)

/-- Constant matrix families factor through the actual normal projection and the fixed matrix map.
Source: Bott–Tu, Differential Forms in Algebraic Topology, §6, complex frame changes. -/
theorem i1_productMatrixNormalMap_constant (B : Type) [TopologicalSpace B] (k : ℕ)
    (A : Matrix (Fin k) (Fin k) ℂ) (hdet : A.det ≠ 0) :
    i1_productMatrixNormalMap k (fun _ : B => A) continuous_const (fun _ => hdet) =
      i1_productNormalProjection B k ≫ complexMatrixPuncturedPairMap k A hdet := by
  apply MorphismProperty.Arrow.Hom.ext
  · apply ConcreteCategory.hom_ext
    intro p
    rfl
  · apply ConcreteCategory.hom_ext
    intro p
    rfl

end HodgeLean.Foundations.BundleThom
