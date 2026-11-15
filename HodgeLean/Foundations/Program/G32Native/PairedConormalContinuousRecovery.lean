import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-! # Continuous recovery from a family of injective linear maps -/

noncomputable section
set_option maxHeartbeats 200000
open Topology
namespace HodgeLean.Foundations.Program.G32Native

/-- A fixed left inverse at one point gives continuous recovery on an open
neighborhood, by inversion of the resulting square endomorphism. -/
theorem paired_linear_family_local_recovery
    {𝕜 B E F : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] [TopologicalSpace B]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 F]
    (A : B → E →L[𝕜] F) (hA : Continuous A) (b₀ : B)
    (hinj : Function.Injective (A b₀)) :
    ∃ U : Set B, IsOpen U ∧ b₀ ∈ U ∧
      ∃ L : U → F →L[𝕜] E, Continuous L ∧
        ∀ (b : U) (v : E), L b (A b.1 v) = v := by
  let l : F →L[𝕜] E := LinearMap.toContinuousLinearMap
    (A b₀).toLinearMap.leftInverse
  have hl (v : E) : l (A b₀ v) = v :=
    LinearMap.leftInverse_apply_of_inj (LinearMap.ker_eq_bot.mpr hinj) v
  let M : B → E →L[𝕜] E := fun b => l.comp (A b)
  have hM : Continuous M := hA.const_clm_comp l
  have hM₀ : M b₀ = 1 := by
    ext v
    exact hl v
  let U : Set B := {b | IsUnit (M b)}
  have hU : IsOpen U := (Units.isOpen (R := E →L[𝕜] E)).preimage hM
  have hb₀ : b₀ ∈ U := by
    change IsUnit (M b₀)
    rw [hM₀]
    exact isUnit_one
  let L : U → F →L[𝕜] E := fun b => (Ring.inverse (M b.1)).comp l
  have hInv : Continuous (fun b : U => Ring.inverse (M b.1)) := by
    apply continuous_iff_continuousAt.mpr
    intro b
    have h : ContinuousAt Ring.inverse (M b.1) := by
      obtain ⟨u, hu⟩ := b.2
      rw [← hu]
      exact NormedRing.inverse_continuousAt u
    exact h.comp (f := fun c : U => M c.1)
      (hM.comp continuous_subtype_val).continuousAt
  refine ⟨U, hU, hb₀, L, hInv.clm_comp_const l, ?_⟩
  intro b v
  have h := congrArg (fun T : E →L[𝕜] E => T v)
    (Ring.inverse_mul_cancel (M b.1) b.2)
  exact h

/-- Continuous base points and continuous observed vectors force continuity
of the recovered vectors for an injective continuous linear family. -/
theorem paired_linear_family_continuous_recovery
    {𝕜 B E F X : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
    [TopologicalSpace B] [TopologicalSpace X]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 F]
    (A : B → E →L[𝕜] F) (hA : Continuous A)
    (hinj : ∀ b, Function.Injective (A b))
    (b : X → B) (hb : Continuous b) (v : X → E)
    (hv : Continuous (fun x => A (b x) (v x))) : Continuous v := by
  apply continuous_iff_continuousAt.mpr
  intro x₀
  obtain ⟨U, hU, hx₀, L, hL, hrecover⟩ :=
    paired_linear_family_local_recovery A hA (b x₀) (hinj (b x₀))
  let V : Set X := b ⁻¹' U
  have hV : IsOpen V := hU.preimage hb
  have hbase : Continuous (fun x : V => (⟨b x.1, x.2⟩ : U)) :=
    (hb.comp continuous_subtype_val).subtype_mk _
  have hcoord : Continuous (fun x : V => L ⟨b x.1, x.2⟩ (A (b x.1) (v x.1))) :=
    (hL.comp hbase).clm_apply (hv.comp continuous_subtype_val)
  have hvV : ContinuousOn v V := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    exact hcoord.congr (fun x => hrecover ⟨b x.1, x.2⟩ (v x.1))
  exact hvV.continuousAt (hV.mem_nhds hx₀)

#print axioms paired_linear_family_local_recovery
#print axioms paired_linear_family_continuous_recovery
end HodgeLean.Foundations.Program.G32Native
