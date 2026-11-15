import HodgeLean.Foundations.RationalHomologyManifold.AmbientSubdivisionSections
import HodgeLean.Foundations.RationalHomologyManifold.SubdivisionLocalEquality

/-! Actual subdivided relative-chain witnesses of local sheaf equality.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicTopology.Singular
namespace HodgeLean.Foundations.RationalHomologyManifold

/-- Equal ambient subdivision sections give equal actually subdivided relative chains on a neighborhood of each point.
Source: Bredon, Sheaf Theory, second edition, VI.12; local equality in supported subdivision limits.
HC no distance; AV milestone no distance.
-/
theorem subdivisionAmbientSection_eq_locally_subdivided (X : TopCat.{0}) (n m : ℕ)
    (U : Opens X) (z w : (SingularChainComplex ℚ X).X n)
    (hab : (subdivisionAmbientSectionMap X n U m).hom z =
      (subdivisionAmbientSectionMap X n U m).hom w) (x : X) (hx : x ∈ U) :
    ∃ (V : Opens X) (hV : V ≤ U) (r : ℕ), x ∈ V ∧
      (relativeChainProjection ℚ (TopPair.ofSubset (X := X) (V : Set X)ᶜ)).f n
        ((rationalSubdivisionIterate X r).f n z) =
      (relativeChainProjection ℚ (TopPair.ofSubset (X := X) (V : Set X)ᶜ)).f n
        ((rationalSubdivisionIterate X r).f n w) := by
  obtain ⟨V, hV, k, hk, hxV, hEq⟩ := subdivisionLimitSheaf_eq_locally_eventually X n m U
    ((relativeChainProjection ℚ (TopPair.ofSubset (X := X) (U : Set X)ᶜ)).f n z)
    ((relativeChainProjection ℚ (TopPair.ofSubset (X := X) (U : Set X)ᶜ)).f n w) hab x hx
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hk
  have hp := (ambientChainPresheafProjection X n).naturality (homOfLE hV).op
  simp only [CategoryTheory.Functor.const_obj_map, Category.id_comp] at hp
  have hz := ConcreteCategory.congr_hom hp z
  have hw := ConcreteCategory.congr_hom hp w
  simp only [ConcreteCategory.comp_apply] at hz hw
  change (relativeChainProjection ℚ (TopPair.ofSubset (X := X) (V : Set X)ᶜ)).f n z =
    ((singularChainPresheafComplex ℚ X).X n).map (homOfLE hV).op
      ((relativeChainProjection ℚ (TopPair.ofSubset (X := X) (U : Set X)ᶜ)).f n z) at hz
  change (relativeChainProjection ℚ (TopPair.ofSubset (X := X) (V : Set X)ᶜ)).f n w =
    ((singularChainPresheafComplex ℚ X).X n).map (homOfLE hV).op
      ((relativeChainProjection ℚ (TopPair.ofSubset (X := X) (U : Set X)ᶜ)).f n w) at hw
  rw [← hz, ← hw] at hEq
  have hiz := ConcreteCategory.congr_hom (supportedSubdivisionProjection_iterate X n V m r) z
  have hiw := ConcreteCategory.congr_hom (supportedSubdivisionProjection_iterate X n V m r) w
  simp only [ConcreteCategory.comp_apply] at hiz hiw
  refine ⟨V, hV, r, hxV, ?_⟩
  exact hiz.trans (hEq.trans hiw.symm)

#print axioms subdivisionAmbientSection_eq_locally_subdivided
/-- Equal actual supported relative chains remain equal after every ambient subdivision iterate.
Source: Bredon, Sheaf Theory, second edition, VI.12; subdivision on supported relative chains.
HC no distance; AV milestone no distance.
-/
theorem rationalSubdivision_preserves_supported_equality (X : TopCat.{0}) (n r : ℕ)
    (U : Opens X) (z w : (SingularChainComplex ℚ X).X n)
    (h : (relativeChainProjection ℚ (TopPair.ofSubset (X := X) (U : Set X)ᶜ)).f n z =
      (relativeChainProjection ℚ (TopPair.ofSubset (X := X) (U : Set X)ᶜ)).f n w) :
    (relativeChainProjection ℚ (TopPair.ofSubset (X := X) (U : Set X)ᶜ)).f n
        ((rationalSubdivisionIterate X r).f n z) =
      (relativeChainProjection ℚ (TopPair.ofSubset (X := X) (U : Set X)ᶜ)).f n
        ((rationalSubdivisionIterate X r).f n w) := by
  let T := (((presheafSubdivisionDiagram X).map (homOfLE (Nat.le_add_right 0 r))).f n).app
    (Opposite.op U)
  have hz := ConcreteCategory.congr_hom (supportedSubdivisionProjection_iterate X n U 0 r) z
  have hw := ConcreteCategory.congr_hom (supportedSubdivisionProjection_iterate X n U 0 r) w
  change (relativeChainProjection ℚ (TopPair.ofSubset (X := X) (U : Set X)ᶜ)).f n
      ((rationalSubdivisionIterate X r).f n z) =
    T ((relativeChainProjection ℚ (TopPair.ofSubset (X := X) (U : Set X)ᶜ)).f n z) at hz
  change (relativeChainProjection ℚ (TopPair.ofSubset (X := X) (U : Set X)ᶜ)).f n
      ((rationalSubdivisionIterate X r).f n w) =
    T ((relativeChainProjection ℚ (TopPair.ofSubset (X := X) (U : Set X)ᶜ)).f n w) at hw
  exact hz.trans ((congrArg T h).trans hw.symm)

#print axioms rationalSubdivision_preserves_supported_equality
end HodgeLean.Foundations.RationalHomologyManifold
