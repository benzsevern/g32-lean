import HodgeLean.Adapters.CycleClassFlatPullbackDefs

/-! # The cycle of a scheme-theoretic intersection

The sum of ideal sheaves retains nilpotents and all generic lengths. This is
an ungraded fundamental cycle, not a refined intersection product. Expected
codimension and comparison with cup products are separate mathematical work.
HC no distance; AV milestone no distance.
-/

noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
namespace HodgeLean.Adapters

/-- Length in the actual local ring of the intersection subscheme.
Source: Fulton, Intersection Theory, second edition, §1.5 and §2.3;
Stacks Project, Tag 02QS, multiplicity of a component of a closed subscheme. -/
def ccm11_intersectionLength (X : Scheme) (I J : X.IdealSheafData)
    (y : (I ⊔ J).subscheme) : ℕ∞ :=
  Module.length ((I ⊔ J).subscheme.presheaf.stalk y)
    ((I ⊔ J).subscheme.presheaf.stalk y)

/-- Fundamental cycle of the scheme-theoretic intersection, with rational coefficients.
Every generic component contributes its own stalk length. No reduction is taken.
On a Noetherian ambient scheme the sum and component lengths are finite.
Source: Fulton, Intersection Theory, second edition, §1.5 and §2.3;
Stacks Project, Tag 02QS. -/
def ccm11_intersectionCycle (X : Scheme) [IsNoetherian X] (I J : X.IdealSheafData) :
    AlgebraicCycle X ℚ := by
  classical
  exact ∑ᶠ y : (I ⊔ J).subscheme,
    if closure ({y} : Set (I ⊔ J).subscheme) ∈
        irreducibleComponents (I ⊔ J).subscheme then
      Function.locallyFinsuppWithin.single ((I ⊔ J).subschemeι y)
        ((ccm11_intersectionLength X I J y).toNat : ℚ)
    else 0

/-- W0: two whole subschemes of the complex point, with a constructed stalk anchor.
Source: the zero ideal defines the whole scheme. -/
example : ℕ∞ := ccm11_intersectionLength (Spec ↧ℂ) ⊥ ⊥
  ⟨IsLocalRing.closedPoint ℂ, by
    change IsLocalRing.closedPoint ℂ ∈ ((⊥ ⊔ ⊥ : (Spec ↧ℂ).IdealSheafData).support : Set (Spec ↧ℂ))
    rw [sup_idem, Scheme.IdealSheafData.support_bot]
    exact Set.mem_univ _⟩

/-- W0b: an actual cycle in the existing carrier.
Source: the zero ideal defines the whole complex point. -/
example : AlgebraicCycle (Spec ↧ℂ) ℚ :=
  ccm11_intersectionCycle (Spec ↧ℂ) ⊥ ⊥

end HodgeLean.Adapters
