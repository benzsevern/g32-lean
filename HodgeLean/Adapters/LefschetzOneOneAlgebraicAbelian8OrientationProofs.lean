import HodgeLean.Adapters.LefschetzOneOneAlgebraicAbelian8OrientationDefs

noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
open AlgebraicTopology.Singular HodgeLean.RealDefs HodgeLean.Foundations
open HodgeLean.Foundations.Singular
open Set Topology
open scoped CategoryTheory.MonObj
namespace HodgeLean.Adapters

private theorem bh8_loopPeriod_const_mul
    (X : Over (Spec ↧ℂ)) [GrpObj X] [IsCommMonObj X] [IsIntegral X.left]
    [Smooth X.hom] [IsProjective X.hom]
    (a : ComplexPoint X) (p : C(UnitAddCircle, ComplexPoint X)) :
    loopPeriod (⟨fun t ↦ a * p t, continuous_const.mul p.continuous⟩) = loopPeriod p := by
  let q : C(UnitAddCircle, ComplexPoint X) :=
    ⟨fun t ↦ a * p t, continuous_const.mul p.continuous⟩
  let ap : C(UnitAddCircle, Additive (ComplexPoint X)) :=
    ⟨fun t ↦ Additive.ofMul (q t), q.continuous⟩
  let ac : C(UnitAddCircle, Additive (ComplexPoint X)) :=
    ⟨fun _ ↦ Additive.ofMul a, continuous_const⟩
  let pp : C(UnitAddCircle, Additive (ComplexPoint X)) :=
    ⟨fun t ↦ Additive.ofMul (p t), p.continuous⟩
  haveI : PathConnectedSpace (Additive (ComplexPoint X)) := pathConnectedSpace_complexPoint X
  have hap : ap = ac + pp := rfl
  have hac : ac = ContinuousMap.const UnitAddCircle (Additive.ofMul a) := rfl
  change loopPeriod ap = loopPeriod pp
  rw [hap, spec_loopPeriod_add, hac, loopPeriod_const, zero_add]

private theorem bh8_periodTorus_h1
    (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] (l m : abelianPeriodLattice X) (z : Fin (dim X.left) → ℂ)
    (x : HQ X 1) :
    cohomologyMap ℚ 1 (TopCat.ofHom (bh8_periodTorus X l m z)) (cupComparison X 1 x) =
      abelianPeriod X x l • torusCoordinateClass 0 +
        abelianPeriod X x m • torusCoordinateClass 1 := by
  letI : IsCommMonObj X := isCommMonObj_of_complexSelfProductIntegral X
    (complexSelfProductIntegral_of_isIntegral X)
  obtain ⟨e, he⟩ := spec_torusPeriod_equiv 2
  apply e.injective
  apply AddMonoidHom.ext
  intro k
  change (e _).toIntLinearMap k = (e _).toIntLinearMap k
  apply LinearMap.congr_fun (x := k)
  apply (Pi.basisFun ℤ (Fin 2)).ext
  intro i
  simp only [Pi.basisFun_apply]
  change e _ (Pi.single i 1) = e _ (Pi.single i 1)
  let k : Fin 2 → ℤ := Pi.single i 1
  rw [he, he]
  change torusPeriod 2 _ k = torusPeriod 2
    (abelianPeriod X x l • torusCoordinateClass 0 +
      abelianPeriod X x m • torusCoordinateClass 1) k
  rw [map_add, map_smul, map_smul, Pi.add_apply, Pi.smul_apply, Pi.smul_apply,
    spec_torusPeriod_coordinate,
    spec_torusPeriod_coordinate]
  change loopPeriod (torusLoop k) (cohomologyMap ℚ 1
    (TopCat.ofHom (bh8_periodTorus X l m z)) (cupComparison X 1 x)) = _
  rw [← loopPeriod_comp]
  fin_cases i
  · have hloop : (bh8_periodTorus X l m z).comp (torusLoop k) =
        ⟨fun t ↦ abelianExp X z * abelianLatticeLoop X l t,
          continuous_const.mul (abelianLatticeLoop X l).continuous⟩ := by
      ext t
      simp [bh8_periodTorus, torusLoop, k, Pi.single_apply, abelianLatticeLoop,
        oneParameterSubgroup]
    rw [hloop, bh8_loopPeriod_const_mul]
    change abelianPeriod X x l = _
    simp [k, Pi.single_apply]
  · have hloop : (bh8_periodTorus X l m z).comp (torusLoop k) =
        ⟨fun t ↦ abelianExp X z * abelianLatticeLoop X m t,
          continuous_const.mul (abelianLatticeLoop X m).continuous⟩ := by
      ext t
      simp [bh8_periodTorus, torusLoop, k, Pi.single_apply, abelianLatticeLoop,
        oneParameterSubgroup]
    rw [hloop, bh8_loopPeriod_const_mul]
    change abelianPeriod X x m = _
    simp [k, Pi.single_apply]

private def bh8_topIndex : Set.powersetCard (Fin 2) 2 :=
  Set.powersetCard.ofCard (by simp : (Finset.univ : Finset (Fin 2)).card = 2)

set_option maxHeartbeats 400000 in
private theorem bh8_topMonomial_eq_cup : torusMonomialBasis 2 2 bh8_topIndex =
    cup (TopCat.of (UnitAddTorus (Fin 2))) rfl
      (torusCoordinateClass 0) (torusCoordinateClass 1) := by
  let I : Set.powersetCard (Fin 2) 2 := bh8_topIndex
  have hmono := (Set.powersetCard.ofFinEmbEquiv.symm I).strictMono
  have hI0 : Set.powersetCard.ofFinEmbEquiv.symm I 0 = 0 := by
    have h := hmono (by decide : (0 : Fin 2) < 1)
    omega
  have hI1 : Set.powersetCard.ofFinEmbEquiv.symm I 1 = 1 := by
    have h := hmono (by decide : (0 : Fin 2) < 1)
    omega
  change torusMonomialBasis 2 2 I = _
  rw [torusMonomialBasis_apply, cupMulti_succ _ 1 rfl, cupMulti_succ _ 0 rfl,
    cupMulti_zero, cup_one]
  rw [hI0]
  simp only [Fin.tail]
  rw [show (Fin.succ 0 : Fin 2) = 1 by rfl]
  rw [hI1]


private theorem bh8_coefficient_top :
    bh8_torusCoefficient (torusMonomialBasis 2 2 bh8_topIndex) = 1 := by
  simp only [bh8_torusCoefficient, bh8_topIndex, Module.Basis.coord_apply,
    Module.Basis.repr_self, Finsupp.single_eq_same]

private theorem bh8_coefficient_cup :
    bh8_torusCoefficient (cup (R := ℚ) (TopCat.of (UnitAddTorus (Fin 2))) (p := 1) (q := 1) (k := 2) rfl
      (torusCoordinateClass 0) (torusCoordinateClass 1)) = 1 := by
  exact (congrArg bh8_torusCoefficient bh8_topMonomial_eq_cup.symm).trans
    bh8_coefficient_top

private theorem bh8_coefficient_determinant (a b c d : ℚ) :
    bh8_torusCoefficient (cup (R := ℚ) (TopCat.of (UnitAddTorus (Fin 2))) (p := 1) (q := 1) (k := 2) rfl
      (a • torusCoordinateClass 0 + b • torusCoordinateClass 1)
      (c • torusCoordinateClass 0 + d • torusCoordinateClass 1)) = a * d - b * c := by
  simp only [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply]
  rw [torus_cup_self_eq_zero, torus_cup_self_eq_zero,
    torus_cup_comm_one 2 rfl (torusCoordinateClass 1) (torusCoordinateClass 0)]
  simp only [map_zero, map_neg, bh8_coefficient_cup, smul_eq_mul]
  rw [bh8_coefficient_cup]
  ring


private theorem bh8_pair_wedge
    (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] (l m : abelianPeriodLattice X) (v : Fin 2 → HQ X 1) :
    bh4_periodPair X l m ((torusCohomology_cupProductOf X).cupWedgeEquiv 2
      (exteriorPower.ιMulti ℚ 2 v)) =
      abelianPeriod X (v 0) l * abelianPeriod X (v 1) m -
        abelianPeriod X (v 1) l * abelianPeriod X (v 0) m := by
  simp only [bh4_periodPair, LinearMap.coe_mk, AddHom.coe_mk,
    LinearEquiv.symm_apply_apply, exteriorPower.map_apply_ιMulti,
    Symplectic.contract_ιMulti, Function.comp_apply,
    AddMonoidHom.sub_apply, AddMonoidHom.smul_apply, smul_eq_mul]
  simp only [LinearEquiv.coe_coe, abelianPeriodEquiv,
    Classical.choose_spec (spec_abelianPeriod_equiv X)]

/-- The increasing-coordinate coefficient of the period torus is the exterior period pairing.
Source: Birkenhake--Lange, second edition, section 1.3;
`abelianPeriod` and naturality of the cup-wedge comparison. -/
theorem bh8_period_coefficient_aux
    (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] (l m : abelianPeriodLattice X) (z : Fin (dim X.left) → ℂ)
    (c : HQ X 2) :
    bh4_periodPair X l m c = bh8_torusCoefficient
      (cohomologyMap ℚ 2 (TopCat.ofHom (bh8_periodTorus X l m z)) (cupComparison X 2 c)) := by
  let e := (torusCohomology_cupProductOf X).cupWedgeEquiv 2
  let f := cohomologyMap ℚ 2 (TopCat.ofHom (bh8_periodTorus X l m z))
  have h : (bh4_periodPair X l m).comp e.toLinearMap =
      bh8_torusCoefficient.comp (f.comp ((cupComparison X 2).toLinearMap.comp
        e.toLinearMap)) := by
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro v
    simp only [LinearMap.compAlternatingMap_apply, LinearMap.comp_apply,
      LinearEquiv.coe_coe]
    rw [bh8_pair_wedge]
    simp only [e, TorusCohomology.cupWedgeEquiv_apply,
      CupProduct.cupWedgeMap_ιMulti, cupComparison_cupMulti, f,
      cohomologyMap_cupMulti]
    rw [cupMulti_succ _ 1 rfl, cupMulti_succ _ 0 rfl, cupMulti_zero, cup_one]
    simp only [Fin.tail]
    rw [bh8_periodTorus_h1, bh8_periodTorus_h1, bh8_coefficient_determinant]
    change _ = abelianPeriod X (v 0) l * abelianPeriod X (v 1) m -
      abelianPeriod X (v 0) m * abelianPeriod X (v 1) l
    ring
  simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
    using LinearMap.congr_fun h (e.symm c)

end HodgeLean.Adapters
