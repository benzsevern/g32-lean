import HodgeLean.Foundations.RationalHomologyManifold.LocalCapNeighborhood
import HodgeLean.Foundations.RationalHomologyManifold.AmbientSubdivisionSections

/-! Eventual germ vanishing of the actual subdivided fixed-chain cap sections.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicTopology.Singular AlgebraicTopology.Simplicial
namespace HodgeLean.Foundations.RationalHomologyManifold

/-- The actual subdivided cap section has zero germ eventually wherever its ambient cochain restricts to zero.
Source: Bredon, Sheaf Theory, second edition, VI.12; subordinate chains and the supported-chain germ.
HC no distance; AV milestone no distance.
-/
theorem subdivisionAmbientSection_cap_germ_eventually_zero (X : TopCat.{0}) [RegularSpace X]
    (x : X) (U : Opens X) (hx : x ∈ U) (p q : ℕ)
    (φ : Cochain ℚ (TopCat.toSSet.obj X) p)
    (hφ : cochainMap ℚ (TopCat.toSSet.map (TopPair.ofSubset (X := X) (U : Set X)).map) p φ = 0)
    (z : (SingularChainComplex ℚ X).X (p + q)) :
    ∃ m : ℕ, ∀ r : ℕ,
      ((subdivisionLimitSheafComplex X).X q).presheaf.germ U x hx
        (subdivisionAmbientSectionMap X q U 0
          (cap ℚ p q φ ((rationalSubdivisionIterate X (m + r)).f (p + q) z))) = 0 := by
  obtain ⟨V, hxV, hVU, m, hm⟩ := local_cap_subdivision_eventually_zero X x U hx p q φ hφ z
  refine ⟨m, fun r => ?_⟩
  let F := (subdivisionLimitSheafComplex X).X q
  let w := cap ℚ p q φ ((rationalSubdivisionIterate X (m + r)).f (p + q) z)
  have hres := ConcreteCategory.congr_hom
    (subdivisionAmbientSectionMap_restriction X q 0 U V hVU) w
  have hv : subdivisionAmbientSectionMap X q V 0 w = 0 := by
    change (toSheafify (Opens.grothendieckTopology X) ((subdivisionLimitPresheafComplex X).X q)).app (Opposite.op V)
      (((colimit.ι (presheafSubdivisionDiagram X) 0).f q).app (Opposite.op V)
        ((relativeChainProjection ℚ (TopPair.ofSubset (X := X) (V : Set X)ᶜ)).f q w)) = 0
    rw [hm r, map_zero, map_zero]
  have hh := congrArg (F.presheaf.germ V x hxV) hres
  simp only [ConcreteCategory.comp_apply] at hh
  have ht := (F.presheaf.germ_res_apply (i := homOfLE hVU) x hxV
    (subdivisionAmbientSectionMap X q U 0 w)).symm
  exact ht.trans (hh.trans (by rw [hv, map_zero]))

#print axioms subdivisionAmbientSection_cap_germ_eventually_zero
end HodgeLean.Foundations.RationalHomologyManifold
