import HodgeLean.Foundations.Curves.Picard.LineBundles.TensorSections

/-! # Functoriality of the actual sheafified tensor maps

The pure tensor section characterization checks the module comparisons.
HC no distance; AV milestone no distance.
-/

set_option backward.isDefEq.respectTransparency false
noncomputable section
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Curves.Picard.LineBundles
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000

/-- Tensor maps preserve identity module morphisms. -/
theorem tensorMap_id {X : Scheme} (M N : X.Modules) :
    tensorMap (𝟙 M) (𝟙 N) = 𝟙 (tensor M N) := by
  apply tensor_hom_ext
  intro U s t
  rw [tensorMap_section]
  rfl

/-- Tensor maps preserve composition in both module arguments. -/
theorem tensorMap_comp {X : Scheme} {M₁ M₂ M₃ N₁ N₂ N₃ : X.Modules}
    (a : M₁ ⟶ M₂) (b : M₂ ⟶ M₃) (c : N₁ ⟶ N₂) (d : N₂ ⟶ N₃) :
    tensorMap a c ≫ tensorMap b d = tensorMap (a ≫ b) (c ≫ d) := by
  apply tensor_hom_ext
  intro U s t
  change (tensorMap b d).app U ((tensorMap a c).app U (tensorSection M₁ N₁ U s t)) =
    (tensorMap (a ≫ b) (c ≫ d)).app U (tensorSection M₁ N₁ U s t)
  rw [tensorMap_section, tensorMap_section, tensorMap_section]
  rfl

/-- The tensor comparison of isomorphisms has the expected underlying tensor map. -/
theorem tensorIso_hom {X : Scheme} {M N P Q : X.Modules}
    (e : M ≅ N) (f : P ≅ Q) : (tensorIso e f).hom = tensorMap e.hom f.hom := rfl

/-- Tensoring actual invertible module morphisms gives an invertible tensor map. -/
theorem tensorMap_isIso {X : Scheme} {M N P Q : X.Modules}
    (a : M ⟶ N) (b : P ⟶ Q) [IsIso a] [IsIso b] : IsIso (tensorMap a b) := by
  change IsIso (tensorIso (asIso a) (asIso b)).hom
  infer_instance

end HodgeLean.Foundations.Curves.Picard.LineBundles
