import HodgeLean.Adapters.KleimanProductProofs

/-! # Fundamental cycles of reduced and integral intersections -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
open HodgeLean.Adapters HodgeLean.RealDefs
namespace HodgeLean.Foundations.Program.G32Native

/-- Every generic stalk of a reduced intersection has length one. -/
theorem reduced_intersection_generic_length_one
    (X : Scheme) (I J : X.IdealSheafData) [IsReduced (I ⊔ J).subscheme]
    (w : (I ⊔ J).subscheme)
    (hw : closure {w} ∈ irreducibleComponents (I ⊔ J).subscheme) :
    ccm11_intersectionLength X I J w = 1 := by
  letI := (isField_stalk_of_closure_mem_irreducibleComponents (I ⊔ J).subscheme w hw).toField
  exact Module.length_eq_one _ _

#print axioms reduced_intersection_generic_length_one
/-- An integral intersection contributes its actual generic component with coefficient one. -/
theorem integral_intersection_cycle
    (X : Scheme) [IsNoetherian X] [DecidableEq X] (I J : X.IdealSheafData)
    [IsIntegral (I ⊔ J).subscheme] :
    ccm11_intersectionCycle X I J =
      Function.locallyFinsuppWithin.single
        ((I ⊔ J).subschemeι (genericPoint (I ⊔ J).subscheme)) (1 : ℚ) := by
  classical
  have hg (w : (I ⊔ J).subscheme)
      (hw : closure {w} ∈ irreducibleComponents (I ⊔ J).subscheme) :
      w = genericPoint (I ⊔ J).subscheme := by
    rw [irreducibleComponents_eq_singleton, Set.mem_singleton_iff] at hw
    exact (isGenericPoint_def.mpr hw).eq (genericPoint_spec _)
  unfold ccm11_intersectionCycle
  rw [finsum_eq_single _ (genericPoint (I ⊔ J).subscheme) (fun w hw => by
    by_cases hc : closure {w} ∈ irreducibleComponents (I ⊔ J).subscheme
    · exact (hw (hg w hc)).elim
    · simp only [if_neg hc])]
  have hgen : closure {genericPoint (I ⊔ J).subscheme} ∈
      irreducibleComponents (I ⊔ J).subscheme := by
    simp only [genericPoint_closure, irreducibleComponents_eq_singleton, Set.mem_singleton_iff]
  rw [if_pos hgen, reduced_intersection_generic_length_one X I J _ hgen]
  ext z
  simp [Function.locallyFinsuppWithin.single_apply]

#print axioms integral_intersection_cycle
/-- The actual class of a coefficient-weighted single prime is its weighted component class. -/
theorem prime_single_cycleClass (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] [DecidableEq X.left]
    (n : ℕ) (z : X.left) (hz : Order.coheight z = n) (a : ℚ) :
    ccm3_cycleClass X n (Function.locallyFinsuppWithin.single z a) =
      a • cycleComponentSheafClass X z hz := by
  unfold ccm3_cycleClass
  change (∑ᶠ w : {w : X.left // Order.coheight w = n},
    (Function.locallyFinsuppWithin.single z a : AlgebraicCycle X.left ℚ) w.1 •
      (cycleComponentSheafClass X w.1 w.2 : HQ X (2 * n))) = _
  rw [finsum_eq_single _ ⟨z, hz⟩ (fun w hw ↦ by
    rw [Function.locallyFinsuppWithin.single_apply, if_neg (fun h ↦ hw (Subtype.ext h)),
      zero_smul])]
  rw [Function.locallyFinsuppWithin.single_apply, if_pos rfl]


#print axioms prime_single_cycleClass
end HodgeLean.Foundations.Program.G32Native
