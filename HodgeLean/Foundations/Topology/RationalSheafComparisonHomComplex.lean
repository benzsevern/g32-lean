import HodgeLean.Foundations.Topology.RationalSheafComparisonResolution

/-! Additive functors acting on the cocycles used by the rational comparison.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CochainComplex CochainComplex.HomComplex
namespace HodgeLean.Topology.RationalSheafComparison

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  (F : C ⥤ D) [F.Additive] {K L : CochainComplex C ℤ} {n : ℤ}

/-- Source: Bredon, Sheaf Theory, second edition, II.4. -/
def functorCocycle (z : Cocycle K L n) :
    Cocycle ((F.mapHomologicalComplex (.up ℤ)).obj K)
      ((F.mapHomologicalComplex (.up ℤ)).obj L) n :=
  Cocycle.mk (z.1.map F) (n + 1) rfl (by rw [δ_map, z.δ_eq_zero _, Cochain.map_zero])

/-- Source: Bredon, Sheaf Theory, second edition, II.4. -/
theorem functorCocycle_equivHomShift (z : Cocycle K L n) :
    Cocycle.equivHomShift.symm (functorCocycle F z) =
      (F.mapHomologicalComplex (.up ℤ)).map (Cocycle.equivHomShift.symm z) ≫
        ((F.mapHomologicalComplex (.up ℤ)).commShiftIso n).hom.app L := by
  apply HomologicalComplex.Hom.ext
  funext i
  simp [Cocycle.equivHomShift_symm_apply, Cocycle.homOf, Cocycle.rightShift,
    Cochain.rightShift, functorCocycle]

/-- Source: Bredon, Sheaf Theory, second edition, II.4. -/
theorem functorCocycle_derivedHom [HasDerivedCategory C] [HasDerivedCategory D]
    [CategoryTheory.Limits.PreservesFiniteLimits F]
    [CategoryTheory.Limits.PreservesFiniteColimits F] (z : Cocycle K L n) :
    ShiftedHom.map (Cocycle.equivHomShift.symm (functorCocycle F z)) DerivedCategory.Q =
      (ShiftedHom.mk₀ 0 rfl (F.mapDerivedCategoryFactors.inv.app K)).comp
        (((ShiftedHom.map (Cocycle.equivHomShift.symm z) DerivedCategory.Q).map
            F.mapDerivedCategory).comp
          (ShiftedHom.mk₀ 0 rfl (F.mapDerivedCategoryFactors.hom.app L)) (zero_add n))
        (add_zero n) := by
  rw [functorCocycle_equivHomShift]
  change ShiftedHom.map (ShiftedHom.map (Cocycle.equivHomShift.symm z)
    (F.mapHomologicalComplex (.up ℤ))) DerivedCategory.Q = _
  rw [← ShiftedHom.comp_map, ← ShiftedHom.comp_map]
  exact (ShiftedHom.map_naturality_1 (Cocycle.equivHomShift.symm z)
    F.mapDerivedCategoryFactors).symm

end HodgeLean.Topology.RationalSheafComparison
