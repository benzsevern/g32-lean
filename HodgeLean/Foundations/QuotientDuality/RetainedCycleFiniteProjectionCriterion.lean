import HodgeLean.Foundations.QuotientDuality.RetainedCycleComplementDetection
import HodgeLean.Foundations.QuotientDuality.RetainedCycleIntrinsicNonvanishing

/-! Intrinsic image detection through an actual finite projective projection. -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicTopology.Singular TopologicalSpace
open HodgeLean.Adapters HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.QuotientDuality

/-- A positive proper projection away from a higher-codimension centre detects the actual intrinsic image. -/
lemma retained_intrinsic_image_ne_zero_of_projection
    (V W P : Over (Spec ↧ℂ))
    [IsIntegral V.left] [IsIntegral W.left]
    [IsProjective V.hom] [IsProjective W.hom] [IsProjective P.hom] [Smooth P.hom]
    (d : ℕ) (hdV : topologicalKrullDim V.left = (d : ℕ))
    (hdW : topologicalKrullDim W.left = (d : ℕ))
    (j : V ⟶ P) (B : Closeds P.left)
    (hB : ∀ p ∈ B, ((d+1 : ℕ) : ℕ∞) ≤ Order.coheight p)
    (havoid : ∀ v : ComplexPoint V, (Point.map j v).underlying ∉ B)
    (π : TopCat.of {p : ComplexPoint P | p.underlying ∉ B} ⟶ a3b4_an W.hom)
    (f : V ⟶ W) [IsProper f.left]
    (hg : f.left (genericPoint V.left) = genericPoint W.left)
    (hdeg : 0 < a1p_degree f.left (genericPoint V.left))
    (hsquare : ∀ v : ComplexPoint V, π ⟨Point.map j v, havoid v⟩ = Point.map f v) :
    homologyMap ℚ (2*d) (TopCat.ofHom (Point.continuousMap j))
      (properCycle_intrinsic_class V d hdV) ≠ 0 := by
  let S : Set (ComplexPoint P) := {p | p.underlying ∉ B}
  let i : a3b4_an V.hom ⟶ TopCat.of S :=
    TopCat.ofHom ⟨fun v => ⟨Point.map j v, havoid v⟩,
      (Point.continuousMap j).continuous.subtype_mk _⟩
  let incl : TopCat.of S ⟶ a3b4_an P.hom :=
    TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩
  have hi : i ≫ incl = TopCat.ofHom (Point.continuousMap j) := by
    ext v : 1
    rfl
  have hπ : i ≫ π = TopCat.ofHom (Point.continuousMap f) := by
    ext v : 1
    exact hsquare v
  have hinj : Function.Injective (homologyMap ℚ (2*d) incl) :=
    retained_complement_homology_injective_of_coheight P.hom B (d+1) (2*d) hB (by omega)
  have hnonzero := retained_intrinsic_proper_image_ne_zero V W f d hdV hdW hg hdeg
  intro hz
  rw [← hi, homologyMap_comp, LinearMap.comp_apply] at hz
  have hz' := hinj (hz.trans (map_zero _).symm)
  apply hnonzero
  rw [← hπ, homologyMap_comp, LinearMap.comp_apply, hz', map_zero]

end HodgeLean.Foundations.QuotientDuality
