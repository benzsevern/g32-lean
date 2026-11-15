import HodgeLean.Foundations.Program.G32Native.QuaternionFramedOrbit
import HodgeLean.Foundations.Program.G32Native.QuaternionEigenSwap
import HodgeLean.Foundations.Program.G32Native.QuaternionPairedBasis
import HodgeLean.Foundations.Program.G32Native.QuaternionTopWedge
import HodgeLean.Foundations.Program.G32Native.QuaternionComplexAction
import HodgeLean.Foundations.Program.G32Native.QuaternionRationalSamples

noncomputable section
set_option maxHeartbeats 200000
open scoped Quaternion TensorProduct
namespace HodgeLean.Foundations.Program.QuaternionGraph
variable {V : Type*} [AddCommGroup V] [Module ℚ V] [Module.Finite ℚ V] {a b : ℚ}

/-- The rational quaternion unit orbit of two complementary top eigenlines has rank `n+1`. -/
theorem quaternion_eigen_orbit_finrank
    (ρ : ℍ[ℚ,a,0,b] →ₐ[ℚ] (Module.End ℚ V)ᵐᵒᵖ) (hb : b < 0) (w : ℂ)
    (hCompl : IsCompl (Module.End.eigenspace (quaternionActionC ρ (quaternionI a b)) w)
      (Module.End.eigenspace (quaternionActionC ρ (quaternionI a b)) (-w)))
    (n : ℕ) (hE : Module.finrank ℂ
      (Module.End.eigenspace (quaternionActionC ρ (quaternionI a b)) w) = n) :
    Module.finrank ℂ (exteriorOrbit
      (fun d : ℍ[ℚ,a,0,b]ˣ => quaternionActionC ρ d)
      (LinearMap.range (exteriorPower.map n
        (Module.End.eigenspace (quaternionActionC ρ (quaternionI a b)) w).subtype) ⊔
       LinearMap.range (exteriorPower.map n
        (Module.End.eigenspace (quaternionActionC ρ (quaternionI a b)) (-w)).subtype))) = n+1 := by
  classical
  let E := Module.End.eigenspace (quaternionActionC ρ (quaternionI a b)) w
  let F := Module.End.eigenspace (quaternionActionC ρ (quaternionI a b)) (-w)
  let e := eigenSwap (quaternionActionC ρ (quaternionI a b))
    (quaternionActionC ρ (quaternionJ a b)) (quaternionActionC_anticommute ρ)
    (b : ℂ) (by exact_mod_cast hb.ne) (quaternionActionC_j_sq ρ) w
  let bE : Module.Basis (Fin n) ℂ E := (Module.finBasis ℂ E).reindex (finCongr hE)
  let bF : Module.Basis (Fin n) ℂ F := bE.map e
  let B := pairedBasis E F hCompl bE e
  have hB₀ (i : Fin n) : B (i,0) = (bE i : ℂ ⊗[ℚ] V) := pairedBasis_zero _ _ _ _ _ _
  have hB₁ (i : Fin n) : B (i,1) = quaternionActionC ρ (quaternionJ a b) (bE i) :=
    pairedBasis_one _ _ _ _ _ _
  have hx (i : Fin n) : quaternionActionC ρ (quaternionI a b) (bE i) = w • (bE i : ℂ ⊗[ℚ] V) :=
    Module.End.mem_eigenspace_iff.mp (bE i).property
  have hLines : LinearMap.range (exteriorPower.map n E.subtype) ⊔
      LinearMap.range (exteriorPower.map n F.subtype) = frameLines B := by
    have hv₀ : exteriorPower.ιMulti ℂ n (fun i => E.subtype (bE i)) =
        exteriorPower.ιMulti ℂ n (fun i => B (i,0)) :=
      congrArg (exteriorPower.ιMulti ℂ n) (funext (fun i => (hB₀ i).symm))
    have hv₁ : exteriorPower.ιMulti ℂ n (fun i => F.subtype (bF i)) =
        exteriorPower.ιMulti ℂ n (fun i => B (i,1)) :=
      congrArg (exteriorPower.ιMulti ℂ n) (funext (fun i => (hB₁ i).symm))
    rw [range_topExterior_eq_span bE, range_topExterior_eq_span bF, hv₀, hv₁,
      frameLines, ← Submodule.span_union]
    simp only [Set.singleton_union]
  change Module.finrank ℂ (exteriorOrbit _ (_ ⊔ _)) = n+1
  rw [hLines]
  apply framed_orbit_finrank
  · intro d
    refine ⟨(d.val.re : ℂ) + (d.val.imI : ℂ)*w,
      (d.val.imJ : ℂ) + (d.val.imK : ℂ)*w,
      (b : ℂ)*((d.val.imJ : ℂ) - (d.val.imK : ℂ)*w),
      (d.val.re : ℂ) - (d.val.imI : ℂ)*w, ?_⟩
    intro i
    rw [hB₀, hB₁]
    exact ⟨quaternionActionC_eigenvector ρ d w (bE i) (hx i),
      quaternionActionC_paired ρ d w (bE i) (hx i)⟩
  · intro t
    refine ⟨graphQuaternionUnit a b (t.val : ℚ) hb, ?_⟩
    intro i
    rw [hB₀, hB₁]
    simpa only [graphQuaternionUnit_val, Rat.cast_one, Rat.cast_zero,
      Rat.cast_natCast, zero_mul, add_zero, one_smul] using
      quaternionActionC_eigenvector ρ (graphQuaternionUnit a b (t.val : ℚ) hb) w (bE i) (hx i)

#print axioms quaternion_eigen_orbit_finrank
end HodgeLean.Foundations.Program.QuaternionGraph
