import HodgeLean.Foundations.Program.G32SelectedRealizationDefs
import HodgeLean.Foundations.Program.RiemannSurfaceQuotientDefs
import HodgeLean.Adapters.AbelianPower
import HodgeLean.Foundations.SegreProjective
import HodgeLean.Foundations.GeometricIntegralityC
import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-! # Schoen curve-power maps
Actual iterated fibre products and their coordinate maps.
HC no distance; AV milestone no distance.
-/

noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.Adapters HodgeLean.RealDefs
namespace HodgeLean.Foundations.Program

/-- Assemble a family of morphisms into the iterated scheme product.
Source: Mac Lane, Categories for the Working Mathematician, III.4. -/
def s2_lift {T Y : Over (Spec ↧ℂ)} :
    (h : ℕ) → (Fin h → (T ⟶ Y)) → (T ⟶ g3_power Y h)
  | 0, _ => CartesianMonoidalCategory.toUnit T
  | h + 1, f => CartesianMonoidalCategory.lift (f 0)
      (s2_lift h (fun i => f i.succ))

example {T Y : Over (Spec ↧ℂ)} (f : Fin 0 → (T ⟶ Y)) :
    s2_lift 0 f = CartesianMonoidalCategory.toUnit T := rfl

/-- Coordinate action: output coordinate i is a(v i) of input coordinate σ⁻¹ i.
The supplier equivalence retains the residual generator of the curve interface.
Source: Schoen (1988), §1, p. 5, and §2, p. 12. -/
def s2_action (S : g32p_Supplier) (Y : Over (Spec ↧ℂ))
    (a : (S.H ⧸ S.χ.ker) → (Y ⟶ Y))
    (e : (S.H ⧸ S.χ.ker) ≃* Multiplicative (ZMod S.m))
    (h : ℕ) (v : Fin h → ZMod S.m) (σ : Equiv.Perm (Fin h)) :
    g3_power Y h ⟶ g3_power Y h :=
  s2_lift h (fun i => g3_proj Y h (σ.symm i) ≫ a (e.symm (.ofAdd (v i))))

example (S : g32p_Supplier) (Y : Over (Spec ↧ℂ))
    (a : (S.H ⧸ S.χ.ker) → (Y ⟶ Y))
    (e : (S.H ⧸ S.χ.ker) ≃* Multiplicative (ZMod S.m))
    (v : Fin 0 → ZMod S.m) (σ : Equiv.Perm (Fin 0)) :
    s2_action S Y a e 0 v σ = CartesianMonoidalCategory.toUnit _ := rfl

/-- Permute the coordinates of an actual scheme power.
Source: Schoen (1988), §2, p. 12, the map to the symmetric power. -/
def s2_permute (Y : Over (Spec ↧ℂ)) (h : ℕ) (σ : Equiv.Perm (Fin h)) :
    g3_power Y h ⟶ g3_power Y h :=
  s2_lift h (fun i => g3_proj Y h (σ.symm i))

example (Y : Over (Spec ↧ℂ)) (σ : Equiv.Perm (Fin 0)) :
    s2_permute Y 0 σ = CartesianMonoidalCategory.toUnit _ := rfl

/-- Apply a curve morphism to each coordinate.
Source: Schoen (1988), §2, diagram on p. 12. -/
def s2_powerMap {Y X : Over (Spec ↧ℂ)} (p : Y ⟶ X) (h : ℕ) :
    g3_power Y h ⟶ g3_power X h :=
  s2_lift h (fun i => g3_proj Y h i ≫ p)

example {Y X : Over (Spec ↧ℂ)} (p : Y ⟶ X) :
    s2_powerMap p 0 = CartesianMonoidalCategory.toUnit _ := rfl

/-- A residual translation lifts to the first coordinate, requiring positive power.
Source: Schoen (1988), §1, p. 5, the map δ. -/
def s2_delta (S : g32p_Supplier) (h : ℕ) (hh : 0 < h) (t : ZMod S.m) :
    Fin h → ZMod S.m := fun i => if i = ⟨0, hh⟩ then t else 0

example (S : g32p_Supplier) (t : ZMod S.m) : s2_delta S 1 (by omega) t 0 = t :=
  ite_eq_left rfl

end HodgeLean.Foundations.Program
