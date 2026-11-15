import HodgeLean.Foundations.Curves.CubicS13Defs
import HodgeLean.Adapters.AbelianMilestones
import HodgeLean.Adapters.TorusCohomologyChecks
import HodgeLean.Adapters.TorusSpine

set_option maxHeartbeats 400000

/-! # Proofs for the curves C5 spec

The proofs of the `_aux` theorems that `CubicS13.lean` (frozen) restates, all instantiations at
`E` with the named group object `cubicGrpObj`. S2 packages C2's instances with `cubicGrpObj`.
S3 and S3' rewrite `finrank_HQ_abelian` with `E_dim`; S8 reads off rank two. S4 is
`torusCohomology_cupProductOf`, `finiteBetti_abelian` and `vanishingAboveTop_abelian`. S5 uses
surjectivity of `cupWedgeMap 2` onto the line `HQ E 2`; S6 evaluates S5 on `ιMulti` through
`cupMulti_succ`. S7 computes `cupPow η 1 = η ∪ 1 = η` with `lefschetzPow_succ`, `lefschetzPow_zero`
and `cup_one`, after transporting `dim E.left` to `1`.
Relation to the goal: HC no distance; AV milestone no distance.
-/

noncomputable section

namespace HodgeLean.Foundations.Curves

open CategoryTheory AlgebraicGeometry TopologicalSpace
open HodgeLean.RealDefs HodgeLean.Adapters

/-- Spec S2: some complex scheme is an abelian curve. -/
theorem exists_complex_abelian_curve_aux :
    ∃ X : Over (Spec ↧ℂ), Nonempty (GrpObj X) ∧ IsIntegral X.left ∧ Smooth X.hom ∧
      IsProjective X.hom ∧ SmoothOfRelativeDimension 1 X.hom :=
  ⟨E, ⟨cubicGrpObj⟩, E_isIntegral, E_smooth, inferInstance, E_smoothOfRelativeDimension⟩

/-- Spec S3: the Betti numbers of `E` are those of the real two-torus. -/
theorem finrank_HQ_cubic_aux (n : ℕ) : Module.finrank ℚ (HQ E n) = Nat.choose 2 n := by
  rw [finrank_HQ_abelian, E_dim]

/-- Spec S3': the rational cohomology of `E` vanishes above degree two. -/
theorem finrank_HQ_cubic_of_two_lt_aux {n : ℕ} (hn : 2 < n) :
    Module.finrank ℚ (HQ E n) = 0 := by
  rw [finrank_HQ_cubic_aux, Nat.choose_eq_zero_of_lt hn]

/-- Spec S4: the S13 package holds on `E` for the constructed cup product. -/
theorem s13_inputs_cubic_aux :
    TorusCohomology (cupProductOf E) ∧ FiniteBetti E ∧ VanishingAboveTop E :=
  ⟨torusCohomology_cupProductOf E, finiteBetti_abelian E, vanishingAboveTop_abelian E⟩

/-- Spec S5: the constructed cup product's exterior-square map on `E` is nonzero. -/
theorem cupWedgeMap_two_cubic_ne_zero_aux : (cupProductOf E).cupWedgeMap 2 ≠ 0 := by
  intro h
  have : Nontrivial (HQ E 2) :=
    Module.nontrivial_of_finrank_pos (by rw [finrank_HQ_cubic_aux]; norm_num)
  obtain ⟨x, hx⟩ := exists_ne (0 : HQ E 2)
  obtain ⟨a, ha⟩ := (s13_inputs_cubic_aux.1.bijective 2).2 x
  rw [h, LinearMap.zero_apply] at ha
  exact hx ha.symm

/-- Spec S6: two degree-one classes of `E` have a nonzero cup product. -/
theorem exists_cup_ne_zero_cubic_aux :
    ∃ a b : HQ E 1, (cupProductOf E).cup (rfl : 1 + 1 = 2) a b ≠ 0 := by
  by_contra! h
  refine cupWedgeMap_two_cubic_ne_zero_aux (exteriorPower.linearMap_ext
    (AlternatingMap.ext fun v => ?_))
  rw [LinearMap.compAlternatingMap_apply, CupProduct.cupWedgeMap_ιMulti,
    CupProduct.cupMulti_succ _ 1 rfl]
  exact h _ _

/-- In complex dimension one the top cup power of `η` is `η` itself, transported along the
dimension equation. -/
theorem cupPow_one_eq_of_dim_eq_one {g : ℕ} (hg : g = 1) {η : HQ E 2} :
    cupPow E (cupProductOf E) η g ≠ 0 ↔ η ≠ 0 := by
  subst hg
  have : cupPow E (cupProductOf E) η 1 = η := by
    unfold cupPow
    erw [lefschetzPow_succ (cupProductOf E) η 0 _ (m' := 0) rfl rfl, lefschetzPow_zero]
    set_option maxRecDepth 20000 in
    exact (cupProductOf E).cup_one η
  rw [this]

/-- Spec S7: on `E`, the top cup power of a degree-two class is nonzero exactly when the class
is. -/
theorem cupPow_cubic_ne_zero_iff_aux (η : HQ E 2) :
    cupPow E (cupProductOf E) η (dim E.left) ≠ 0 ↔ η ≠ 0 := by
  rw [cupPow_one_eq_of_dim_eq_one E_dim]

/-- Spec S8: the first rational cohomology of `E` is nonzero. -/
theorem nontrivial_HQ_one_cubic_aux : Nontrivial (HQ E 1) :=
  Module.nontrivial_of_finrank_pos (by rw [finrank_HQ_cubic_aux]; norm_num)

end HodgeLean.Foundations.Curves
