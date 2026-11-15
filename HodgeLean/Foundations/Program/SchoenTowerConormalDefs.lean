import HodgeLean.Foundations.Program.SchoenTowerGeometryDefs
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free

/-! # Conormal sheaves of the paired centres
The conormal is the pullback of the ideal sheaf, as a kernel of modules.
HC no distance; AV milestone no distance.
-/

noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- The ideal module of a scheme immersion, defined by the structure-sheaf map.
Source: Hartshorne, Algebraic Geometry, II.5, the ideal sheaf of a subscheme. -/
def s2c_idealModule {K B : Scheme} (k : K ⟶ B) : B.Modules :=
  kernel (show (SheafOfModules.unit B.ringCatSheaf : B.Modules) ⟶
      (Scheme.Modules.pushforward k).obj (SheafOfModules.unit K.ringCatSheaf) from
    SheafOfModules.unitToPushforwardObjUnit k.toRingCatSheafHom)

example {K B : Scheme} (k : K ⟶ B) : s2c_idealModule k =
    kernel (show (SheafOfModules.unit B.ringCatSheaf : B.Modules) ⟶
      (Scheme.Modules.pushforward k).obj (SheafOfModules.unit K.ringCatSheaf) from
      SheafOfModules.unitToPushforwardObjUnit k.toRingCatSheafHom) := rfl

/-- The conormal module I/I² on the centre itself.
Source: Hartshorne, Algebraic Geometry, II.8, conormal sheaf. -/
def s2c_conormal {K B : Scheme} (k : K ⟶ B) : K.Modules :=
  (Scheme.Modules.pullback k).obj (s2c_idealModule k)

example {K B : Scheme} (k : K ⟶ B) :
    s2c_conormal k = (Scheme.Modules.pullback k).obj (s2c_idealModule k) := rfl

/-- The actual exceptional scheme, by base change of the centre immersion.
Source: Schoen (1988), §2, pp. 14–18, Eᵢ over Kᵢ₋₁. -/
def s2c_exceptional {B' B : Over (Spec ↧ℂ)} (b : B' ⟶ B)
    (I : B.left.IdealSheafData) : Over (Spec ↧ℂ) :=
  pullback b (s2c_subschemeι B I)

example {B' B : Over (Spec ↧ℂ)} (b : B' ⟶ B) (I : B.left.IdealSheafData) :
    s2c_exceptional b I = pullback b (s2c_subschemeι B I) := rfl

end HodgeLean.Foundations.Program
