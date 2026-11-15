import HodgeLean.Foundations.Program.ComponentTransportRelabel
import HodgeLean.Foundations.Program.HalfTwist

/-! # Normalized certificate path: the relabelled centre
The endpoint of the normalized certificate path in the chart. Reference label `τ j`, with
`τ = b65u_endpointPerm`, sits at the image of certified label `j` under the affine map
`w ↦ 1 - w / c₈`, where `c₈ = b65z_centre p 8`. This is a finite definition; no monodromy
statement is made here.
HC no distance; AV milestone no distance.
-/
noncomputable section
namespace HodgeLean.Foundations.Program

/-- The relabelled centre: moving coordinate `k` is `1 - a / c₈`, where `a` is the finite
branch point of the G32 centre at certified label `τ⁻¹ k` and `c₈ = b65z_centre p 8`. The last
entry of `![0, 1, 0]` is never read, since `τ⁻¹ k ≠ 12` for `k < 10`.
Source: `b65u_endpointPerm`, `b65z_centre`, `b6_branch`; G32 v0.16, §3.1 (normalization of
three branch points); spec-rle, stage S2. -/
def b65v_relabelCentre (p : Fin 12 → ℂ) : Fin 10 → ℂ := fun k ↦
  1 - (Fin.append (b65z_centre p) ![0, 1, 0] : Fin 13 → ℂ)
    (b65u_endpointPerm.symm (k.castAdd 3)) / b65z_centre p 8

/-- Reference label 0 sits at the image of certified label `τ⁻¹ 0 = 2`. -/
example (p : Fin 12 → ℂ) :
    b65v_relabelCentre p 0 = 1 - b65z_centre p 2 / b65z_centre p 8 := by
  have h : b65u_endpointPerm.symm ((0 : Fin 10).castAdd 3) = (2 : Fin 10).castAdd 3 := by
    decide +kernel
  simp only [b65v_relabelCentre, h, Fin.append_left]

/-- The labels sent to `0`, `1` and `∞` by the normalization. -/
example : b65u_endpointPerm.symm 10 = 8 ∧ b65u_endpointPerm.symm 11 = 10 ∧
    b65u_endpointPerm 12 = 12 := by
  decide +kernel

end HodgeLean.Foundations.Program
