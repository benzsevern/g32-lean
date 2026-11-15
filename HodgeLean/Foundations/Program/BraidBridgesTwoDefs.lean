import HodgeLean.Foundations.Program.BraidBridgesDefs
import HodgeLean.Foundations.Program.RigidStartingSystemRational
import HodgeLean.Foundations.Program.RigidStartingSystemPrintedGroup

/-! # Downstairs map and the inverse Hurwitz change of generators

Implication from regularity to a continuous map of punctured planes.
HC no distance; AV milestone no distance.
-/

noncomputable section
namespace HodgeLean.Foundations.Program

theorem b65x_phi_down_aux : ∀ z ∈ b65s_regular,
    b65r_phi z ≠ 0 ∧ b65r_phi z ≠ 5 ∧ b65r_phi z ≠ -7 := by
  intro z hz
  rcases hz with ⟨h0, h3, h1, h2, h5, h7⟩
  have hd : (z - 1)^3 * (z + 2)^3 ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (sub_ne_zero.mpr h1))
      (pow_ne_zero _ (by intro h; apply h2; linear_combination h))
  refine ⟨div_ne_zero (mul_ne_zero (pow_ne_zero _ h0)
    (pow_ne_zero _ (sub_ne_zero.mpr h3))) hd, ?_, ?_⟩
  · exact sub_ne_zero.mp (by rw [b65r_phi_sub 5 z h1 h2]; exact div_ne_zero h5 hd)
  · exact sub_ne_zero.mp (by rw [b65r_phi_sub (-7) z h1 h2]; exact div_ne_zero h7 hd)

theorem b65x_phi_continuousOn_aux : ContinuousOn b65r_phi b65s_regular := by
  intro z hz
  exact ((b65r_phi_hasDerivAt z hz.2.2.1 hz.2.2.2.1).continuousAt).continuousWithinAt

/-- The rational map on the regular punctured plane.
Source: G32 v0.16, §5.2, φ; `b65r_phi_sub` and `b65r_phi_hasDerivAt`. -/
def b65x_phiMap : C(b65s_regular, b65x_Down) where
  toFun z := ⟨b65r_phi z.val, b65x_phi_down_aux z.val z.property⟩
  continuous_toFun := (continuousOn_iff_continuous_domRestrict.mp b65x_phi_continuousOn_aux).subtype_mk _

example (z : b65s_regular) : (b65x_phiMap z).val = b65r_phi z.val := rfl

/-- Printed peripheral order obtained by undoing the cut-system Hurwitz move.
The last entry is the positive peripheral class at infinity.
Source: B65-BRAIDCERT REPORT §2, D₀ = r₂ x r₂⁻¹. -/
def b65x_peripheral (y : b65x_Down) (g : Fin 3 → Path y y) :
    Fin 4 → FundamentalGroup b65x_Down y :=
  let D := fun j ↦ FundamentalGroup.fromPath ⟦g j⟧
  ![D 0, D 1, (D 1)⁻¹ * D 2 * D 1, (D 0 * D 2 * D 1)⁻¹]

example (y : b65x_Down) (g : Fin 3 → Path y y) :
    b65x_peripheral y g 0 = FundamentalGroup.fromPath ⟦g 0⟧ := rfl

end HodgeLean.Foundations.Program
