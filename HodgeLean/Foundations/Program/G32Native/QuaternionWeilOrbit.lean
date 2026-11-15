import HodgeLean.Foundations.Program.G32Native.QuaternionEigenOrbit
import HodgeLean.Foundations.Program.G32Native.QuaternionOrbitScalarExtension
import HodgeLean.Foundations.Program.CompensationEightfold

noncomputable section
set_option maxHeartbeats 200000
set_option maxRecDepth 2048
open scoped Quaternion TensorProduct
open HodgeBlocks HodgeBlocks.WeilAction
namespace HodgeLean.Foundations.Program.QuaternionGraph
variable {V : Type*} [AddCommGroup V] [Module ℚ V] [Module.Finite ℚ V]
  {M : QHodgeStructure 1 V} {d a b : ℚ}

/-- Rational quaternion units generate a Weil exterior orbit of dimension twice the half-degree plus one. -/
theorem quaternion_weil_orbit_finrank (W : WeilAction M d)
    (hH : M.H (1,0) ⊔ M.H (0,1) = ⊤) (hWeil : W.IsWeilType) (hd : 0 < d)
    (ρ : ℍ[ℚ,a,0,b] →ₐ[ℚ] (Module.End ℚ V)ᵐᵒᵖ) (hb : b < 0)
    (hI : W.J = quaternionAction ρ (quaternionI a b)) :
    let k := Module.finrank ℂ ↥(W.Vs ⊓ M.H (1,0))
    Module.finrank ℚ (exteriorOrbit (fun q : ℍ[ℚ,a,0,b]ˣ => quaternionAction ρ q)
      (W.weilClasses hH hWeil)) = k+k+1 := by
  classical
  let k := Module.finrank ℂ ↥(W.Vs ⊓ M.H (1,0))
  have hiC : quaternionActionC ρ (quaternionI a b) = W.Jc := by
    exact congrArg (fun f : Module.End ℚ V => f.baseChange ℂ) hI.symm
  have hc : IsCompl (Module.End.eigenspace (quaternionActionC ρ (quaternionI a b)) (omegaC d))
      (Module.End.eigenspace (quaternionActionC ρ (quaternionI a b)) (-omegaC d)) := by
    rw [hiC]
    exact W.isCompl_Vs_Vsbar hd
  have he : Module.finrank ℂ
      (Module.End.eigenspace (quaternionActionC ρ (quaternionI a b)) (omegaC d)) = k+k := by
    rw [hiC]
    change Module.finrank ℂ W.Vs = k+k
    have h := hWeil
    change 2*k = Module.finrank ℂ W.Vs at h
    omega
  have hr := quaternion_eigen_orbit_finrank ρ hb (omegaC d) hc (k+k) he
  have hSpan : complexSpan (W.weilClasses hH hWeil) =
      LinearMap.range (exteriorPower.map (k+k) W.Vs.subtype) ⊔
      LinearMap.range (exteriorPower.map (k+k) W.Vsbar.subtype) :=
    HodgeLean.Foundations.Program.cq8_weilClasses_span W hH hWeil hd
  change Module.finrank ℚ (exteriorOrbit _ _) = k+k+1
  rw [← complexSpan_finrank, complexSpan_exteriorOrbit, hSpan]
  rw [hiC] at hr
  exact hr

#print axioms quaternion_weil_orbit_finrank
end HodgeLean.Foundations.Program.QuaternionGraph
