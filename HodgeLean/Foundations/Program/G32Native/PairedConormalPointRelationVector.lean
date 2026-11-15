import HodgeLean.Foundations.Program.G32Native.PairedConormalPointCoordinateRows
import HodgeLean.Foundations.Program.G32Native.PairedConormalPresentationPointMap
import HodgeLean.Foundations.Program.G32Native.PairedConormalUnitMapDetection
import HodgeLean.Foundations.NormalPresentation.Defs

/-! # The actual relation vector in canonical point fibre coordinates -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native

/-- The supplied point frame and actual relation determine a literal vector
in the canonical unit-plus-free point coordinates. -/
def conormalPointRelationVector {X : Scheme.{0}} (k : ℕ) {I : X.Modules}
    (a : I ⟶ SheafOfModules.unit X.ringCatSheaf)
    (b : I ⟶ SheafOfModules.free (R := X.ringCatSheaf) (Fin k))
    (x : Spec (CommRingCat.of ℂ) ⟶ X)
    (u : SheafOfModules.unit (Spec ↧ℂ).ringCatSheaf ⟶ (Scheme.Modules.pullback x).obj I) :
    ℂ × (Fin k → ℂ) :=
  conormalUnitFreeFibreCoordinates x k
    ((moduleSpecΓFunctor (R := CommRingCat.of ℂ)).map
      (u ≫ (Scheme.Modules.pullback x).map
        (HodgeLean.Foundations.NormalPresentation.relation a b)) (1 : Γ(Spec ↧ℂ, ⊤)))

/-- An invertible actual point frame preserves nonvanishing of the actual relation vector. -/
theorem conormal_point_relation_vector_ne_zero {X : Scheme.{0}} (k : ℕ) {I : X.Modules}
    (a : I ⟶ SheafOfModules.unit X.ringCatSheaf)
    (b : I ⟶ SheafOfModules.free (R := X.ringCatSheaf) (Fin k))
    (x : Spec (CommRingCat.of ℂ) ⟶ X)
    (u : SheafOfModules.unit (Spec ↧ℂ).ringCatSheaf ⟶ (Scheme.Modules.pullback x).obj I)
    [IsIso u]
    (hrel : (Scheme.Modules.pullback x).map
      (HodgeLean.Foundations.NormalPresentation.relation a b) ≠ 0) :
    conormalPointRelationVector k a b x u ≠ 0 := by
  intro hv
  have hz : (moduleSpecΓFunctor (R := CommRingCat.of ℂ)).map
      (u ≫ (Scheme.Modules.pullback x).map
        (HodgeLean.Foundations.NormalPresentation.relation a b)) (1 : Γ(Spec ↧ℂ, ⊤)) = 0 := by
    apply (conormalUnitFreeFibreCoordinates x k).injective
    exact hv.trans (map_zero (conormalUnitFreeFibreCoordinates x k)).symm
  have ha := (conormal_point_unit_map_eq_zero_iff_value _).mpr hz
  apply hrel
  apply (cancel_epi u).mp
  simpa only [comp_zero] using ha

/-- The literal actual relation vector lies in the kernel of the supplied actual quotient. -/
theorem conormal_point_relation_vector_in_kernel {X : Scheme.{0}} (k : ℕ) {I M : X.Modules}
    (a : I ⟶ SheafOfModules.unit X.ringCatSheaf)
    (b : I ⟶ SheafOfModules.free (R := X.ringCatSheaf) (Fin k))
    (π : (SheafOfModules.unit X.ringCatSheaf ⊞
      SheafOfModules.free (R := X.ringCatSheaf) (Fin k)) ⟶ M)
    (hπ : HodgeLean.Foundations.NormalPresentation.relation a b ≫ π = 0)
    (x : Spec (CommRingCat.of ℂ) ⟶ X)
    (u : SheafOfModules.unit (Spec ↧ℂ).ringCatSheaf ⟶ (Scheme.Modules.pullback x).obj I) :
    conormalPresentationPointMap k π x (conormalPointRelationVector k a b x u) = 0 := by
  let F := Scheme.Modules.pullback x
  let G := moduleSpecΓFunctor (R := CommRingCat.of ℂ)
  letI : G.IsRightAdjoint := ⟨_, ⟨tilde.adjunction⟩⟩
  letI : F.Additive := conormal_scheme_pullback_additive x
  let r := HodgeLean.Foundations.NormalPresentation.relation a b
  change (G.map (F.map π))
    ((conormalUnitFreeFibreCoordinates x k).symm
      (conormalUnitFreeFibreCoordinates x k
        ((G.map (u ≫ F.map r)) (1 : Γ(Spec ↧ℂ, ⊤))))) = 0
  rw [LinearEquiv.symm_apply_apply]
  have hc : (u ≫ F.map r) ≫ F.map π = 0 := by
    rw [Category.assoc, ← CategoryTheory.Functor.map_comp, hπ,
      CategoryTheory.Functor.map_zero, comp_zero]
  have hz := congrArg (fun f : SheafOfModules.unit (Spec ↧ℂ).ringCatSheaf ⟶ F.obj M =>
    (G.map f) (1 : Γ(Spec ↧ℂ, ⊤))) hc
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_zero] at hz
  exact hz

end HodgeLean.Foundations.Program.G32Native
