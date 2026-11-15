import HodgeLean.Adapters.CycleClassFlatPullbackDefs
import HodgeLean.Adapters.NormalConeB4Defs

/-! Finite-support reading of the specified cycle class sum. -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.Adapters HodgeLean.RealDefs
namespace HodgeLean.Foundations.Program

/-- On a pure rational cycle, the specified class sum is indexed by the
actual finite support, with every original coefficient retained. -/
theorem s4_q3_cycleClass_support_sum
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (γ : AlgebraicCycle X.left ℚ) (k : ℕ)
    (hγ : ∀ p ∈ γ.support, Order.coheight p = k) :
    letI : CompactSpace X.left := a3b4_compactSpace X.hom
    letI : Fintype {p : X.left // p ∈ γ.support} := (a3b2_support_finite γ).fintype
    ccm3_cycleClass X k γ = ∑ p : {p : X.left // p ∈ γ.support},
      γ p.1 • cycleComponentSheafClass X p.1 (hγ p.1 p.2) := by
  classical
  letI : CompactSpace X.left := a3b4_compactSpace X.hom
  let I := {p : X.left // p ∈ γ.support}
  letI : Fintype I := (a3b2_support_finite γ).fintype
  let J := {p : X.left // Order.coheight p = k}
  let e : I ≃ {p : J // γ p.1 ≠ 0} :=
    { toFun := fun p => ⟨⟨p.1, hγ p.1 p.2⟩, p.2⟩
      invFun := fun p => ⟨p.1.1, p.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  symm
  calc
    _ = ∑ᶠ p : I, γ p.1 • cycleComponentSheafClass X p.1 (hγ p.1 p.2) :=
      (finsum_eq_sum_of_fintype _).symm
    _ = ∑ᶠ p : {p : J // γ p.1 ≠ 0}, γ p.1.1 • cycleComponentSheafClass X p.1.1 p.1.2 :=
      finsum_comp_equiv e (f := fun p => γ p.1.1 • cycleComponentSheafClass X p.1.1 p.1.2)
    _ = ∑ᶠ p : J, ∑ᶠ _ : γ p.1 ≠ 0, γ p.1 • cycleComponentSheafClass X p.1 p.2 :=
      finsum_subtype_eq_finsum_cond (M := HQ X (2 * k))
        (f := fun p : J => γ p.1 • cycleComponentSheafClass X p.1 p.2)
        (fun p => γ p.1 ≠ 0)
    _ = ccm3_cycleClass X k γ := by
      apply finsum_congr
      intro p
      by_cases hp : γ p.1 ≠ 0
      · simp [hp]
      · simp [hp, not_ne_iff.mp hp]

end HodgeLean.Foundations.Program
