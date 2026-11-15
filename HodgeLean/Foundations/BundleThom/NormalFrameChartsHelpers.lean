import HodgeLean.Foundations.BundleThom.FrameSectionsHelpers
import HodgeLean.Foundations.BundleThom.AnalyticNormalTopologyHelpers

/-! # Normal coordinates supplied by actual local conormal frames

The coordinate functions are evaluations against the frame's algebraic sections.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry TopologicalSpace Bundle
namespace HodgeLean.Foundations.BundleThom

variable {Q : Over (Spec ↧ℂ)} {V : Scheme} (j : Q.left ⟶ V) (k : ℕ)
private local instance : TopologicalSpace (TotalSpace (Fin k → ℂ) (i1_normalFibre j)) :=
  i1_normalTotalTopology j k

/-- Dual coordinates for the actual local conormal frame.
Source: Hartshorne, Algebraic Geometry, II.5 and II.8, normal bundle coordinates. -/
def i1_normalFrameCoordinates (U : Q.left.Opens)
    (E : (Scheme.Modules.pullback U.ι).obj (Conormal.sheaf j) ≅
      (SheafOfModules.free (R := U.toScheme.ringCatSheaf) (Fin k)))
    (z : {v : TotalSpace (Fin k → ℂ) (i1_normalFibre j) | v.proj ∈ Point.overOpen U}) :
    Fin k → ℂ :=
  (i1_conormalFrameBasis j k U E z.1.proj z.2).dualBasis.equivFun z.1.2

/-- The actual frame's dual coordinate map is continuous for the fixed total topology.
Source: Hartshorne, Algebraic Geometry, II.5, analytification of local frames. -/
theorem i1_normalFrameCoordinates_continuous (U : Q.left.Opens)
    (E : (Scheme.Modules.pullback U.ι).obj (Conormal.sheaf j) ≅
      (SheafOfModules.free (R := U.toScheme.ringCatSheaf) (Fin k))) :
    Continuous (i1_normalFrameCoordinates j k U E) := by
  apply continuous_pi
  intro i
  have heq : (fun z => i1_normalFrameCoordinates j k U E z i) =
      (fun z : {v : TotalSpace (Fin k → ℂ) (i1_normalFibre j) |
        v.proj ∈ Point.overOpen U} =>
        z.1.2 (i1_conormalSectionValue j U (i1_conormalFrameSection j k U E i)
          z.1.proj z.2)) := by
    funext z
    exact (Module.Basis.dualBasis_equivFun _ _ _).trans
      (congrArg z.1.2 (i1_conormalFrameBasis_apply j k U E z.1.proj z.2 i))
  rw [heq]
  exact i1_normalLocalEvaluation_continuous j k U (i1_conormalFrameSection j k U E i)

/-- The specified actual frame gives a fibrewise linear product equivalence over its open base.
Source: Hartshorne, Algebraic Geometry, II.5 and II.8, local normal coordinates. -/
def i1_normalFrameEquiv (U : Q.left.Opens)
    (E : (Scheme.Modules.pullback U.ι).obj (Conormal.sheaf j) ≅
      (SheafOfModules.free (R := U.toScheme.ringCatSheaf) (Fin k))) :
    {v : TotalSpace (Fin k → ℂ) (i1_normalFibre j) | v.proj ∈ Point.overOpen U} ≃
      ↥(Point.overOpen U : Set (ComplexPoint Q)) × (Fin k → ℂ) where
  toFun z := (⟨z.1.proj, z.2⟩, i1_normalFrameCoordinates j k U E z)
  invFun p := ⟨⟨p.1.1,
    (i1_conormalFrameBasis j k U E p.1.1 p.1.2).dualBasis.equivFun.symm p.2⟩, p.1.2⟩
  left_inv := by
    rintro ⟨⟨x, f⟩, hx⟩
    apply Subtype.ext
    exact congrArg (fun g : i1_normalFibre j x =>
      (⟨x, g⟩ : TotalSpace (Fin k → ℂ) (i1_normalFibre j)))
        ((i1_conormalFrameBasis j k U E x hx).dualBasis.equivFun.symm_apply_apply f)
  right_inv := by
    rintro ⟨⟨x, hx⟩, v⟩
    apply Prod.ext
    · rfl
    · exact (i1_conormalFrameBasis j k U E x hx).dualBasis.equivFun.apply_symm_apply v

/-- The local product equivalence is continuous in the direction of normal coordinates.
Source: Hartshorne, Algebraic Geometry, II.5, analytification of a local frame. -/
theorem i1_normalFrameEquiv_continuous (U : Q.left.Opens)
    (E : (Scheme.Modules.pullback U.ι).obj (Conormal.sheaf j) ≅
      (SheafOfModules.free (R := U.toScheme.ringCatSheaf) (Fin k))) :
    Continuous (i1_normalFrameEquiv j k U E) := by
  have hb : Continuous (fun z :
      {v : TotalSpace (Fin k → ℂ) (i1_normalFibre j) | v.proj ∈ Point.overOpen U} =>
      (⟨z.1.proj, z.2⟩ : ↥(Point.overOpen U : Set (ComplexPoint Q)))) :=
    ((i1_normalProjection_continuous j k).comp continuous_subtype_val).subtype_mk _
  exact hb.prodMk (i1_normalFrameCoordinates_continuous j k U E)

end HodgeLean.Foundations.BundleThom
