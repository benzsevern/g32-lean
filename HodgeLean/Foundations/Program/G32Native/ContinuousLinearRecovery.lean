import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.Analysis.Normed.Ring.Units

/-! # Recovering continuous coordinates from finite linear images -/
noncomputable section
set_option maxHeartbeats 200000
open Filter Topology
namespace HodgeLean.Foundations.Program.G32Native

/-- An injective finite-dimensional linear family detects continuity of a
vector from continuity of its image. No continuity of the vector is assumed. -/
theorem continuousAt_of_continuous_linear_image
    {E F T : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    [FiniteDimensional ℂ E] [FiniteDimensional ℂ F] [TopologicalSpace T]
    (A : T → E →L[ℂ] F) (v : T → E) (t : T)
    (hA : ContinuousAt A t) (hinj : Function.Injective (A t))
    (hv : ContinuousAt (fun s => A s (v s)) t) : ContinuousAt v t := by
  letI : CompleteSpace E := FiniteDimensional.complete ℂ E
  obtain ⟨l, hl⟩ := (A t).toLinearMap.exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr hinj)
  let L := l.toContinuousLinearMap
  let B : T → E →L[ℂ] E := fun s => L.comp (A s)
  have hBt : B t = 1 := by
    ext z
    exact DFunLike.congr_fun hl z
  have hB : ContinuousAt B t := continuousAt_const.clm_comp hA
  have hi : ContinuousAt (fun s => Ring.inverse (B s)) t := by
    have hh : ContinuousAt (Ring.inverse : (E →L[ℂ] E) → (E →L[ℂ] E)) (B t) := by
      rw [hBt]
      exact NormedRing.inverse_continuousAt (1 : (E →L[ℂ] E)ˣ)
    exact hh.comp hB
  have hu : ∀ᶠ s in 𝓝 t, IsUnit (B s) := by
    exact hB.eventually (Units.isOpen.mem_nhds
      (show IsUnit (B t) by rw [hBt]; exact isUnit_one))
  have heq : (fun s => Ring.inverse (B s) (L (A s (v s)))) =ᶠ[𝓝 t] v := by
    filter_upwards [hu] with s hs
    have h := congrArg (fun f : E →L[ℂ] E => f (v s)) (Ring.inverse_mul_cancel (B s) hs)
    exact h
  exact (hi.clm_apply (L.continuous.continuousAt.comp hv)).congr_of_eventuallyEq heq.symm

#print axioms continuousAt_of_continuous_linear_image

/-- Continuity of a surjective finite coordinate image controls every
continuous linear factor that vanishes on its kernel near the point. -/
theorem continuousAt_linear_factor_image
    {V E F T : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F]
    [FiniteDimensional ℂ V] [FiniteDimensional ℂ E] [FiniteDimensional ℂ F]
    [TopologicalSpace T] (A : T → V →L[ℂ] E) (D : T → V →L[ℂ] F)
    (v : T → V) (t : T) (hA : ContinuousAt A t) (hD : ContinuousAt D t)
    (hsurj : Function.Surjective (A t))
    (hker : ∀ᶠ s in 𝓝 t, LinearMap.ker (A s).toLinearMap ≤ LinearMap.ker (D s).toLinearMap)
    (hv : ContinuousAt (fun s => A s (v s)) t) :
    ContinuousAt (fun s => D s (v s)) t := by
  letI : CompleteSpace E := FiniteDimensional.complete ℂ E
  obtain ⟨r, hr⟩ := (A t).toLinearMap.exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr hsurj)
  let R := r.toContinuousLinearMap
  let B : T → E →L[ℂ] E := fun s => (A s).comp R
  have hBt : B t = 1 := by
    ext z
    exact DFunLike.congr_fun hr z
  have hB : ContinuousAt B t := hA.clm_comp continuousAt_const
  have hi : ContinuousAt (fun s => Ring.inverse (B s)) t := by
    have hh : ContinuousAt (Ring.inverse : (E →L[ℂ] E) → (E →L[ℂ] E)) (B t) := by
      rw [hBt]
      exact NormedRing.inverse_continuousAt (1 : (E →L[ℂ] E)ˣ)
    exact hh.comp hB
  have hu : ∀ᶠ s in 𝓝 t, IsUnit (B s) := by
    exact hB.eventually (Units.isOpen.mem_nhds
      (show IsUnit (B t) by rw [hBt]; exact isUnit_one))
  let w : T → V := fun s => R (Ring.inverse (B s) (A s (v s)))
  have hw : ContinuousAt w t := R.continuous.continuousAt.comp (hi.clm_apply hv)
  have heq : (fun s => D s (w s)) =ᶠ[𝓝 t] (fun s => D s (v s)) := by
    filter_upwards [hu, hker] with s hs hk
    have hAw : A s (w s) = A s (v s) := by
      exact congrArg (fun f : E →L[ℂ] E => f (A s (v s))) (Ring.mul_inverse_cancel (B s) hs)
    have hz : D s (v s - w s) = 0 := by
      apply hk
      change A s (v s - w s) = 0
      rw [map_sub, hAw, sub_self]
    exact (sub_eq_zero.mp (by simpa only [map_sub] using hz)).symm
  exact (hD.clm_apply hw).congr_of_eventuallyEq heq.symm

#print axioms continuousAt_linear_factor_image


/-- Surjectivity of a finite-dimensional linear family persists near a point
where the family is continuous and surjective. -/
theorem eventually_surjective_of_continuousAt
    {V E T : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ V] [FiniteDimensional ℂ E] [TopologicalSpace T]
    (A : T → V →L[ℂ] E) (t : T) (hA : ContinuousAt A t)
    (hsurj : Function.Surjective (A t)) :
    ∀ᶠ s in 𝓝 t, Function.Surjective (A s) := by
  letI : CompleteSpace E := FiniteDimensional.complete ℂ E
  obtain ⟨r, hr⟩ := (A t).toLinearMap.exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr hsurj)
  let R := r.toContinuousLinearMap
  let B : T → E →L[ℂ] E := fun s => (A s).comp R
  have hBt : B t = 1 := by ext z; exact DFunLike.congr_fun hr z
  have hB : ContinuousAt B t := hA.clm_comp continuousAt_const
  have hu : ∀ᶠ s in 𝓝 t, IsUnit (B s) := hB.eventually
    (Units.isOpen.mem_nhds (show IsUnit (B t) by rw [hBt]; exact isUnit_one))
  filter_upwards [hu] with s hs
  intro e
  refine ⟨R (Ring.inverse (B s) e), ?_⟩
  exact congrArg (fun f : E →L[ℂ] E => f e) (Ring.mul_inverse_cancel (B s) hs)

#print axioms eventually_surjective_of_continuousAt


/-- It suffices to check the kernel relation wherever the finite coordinate
map is surjective, since that condition persists near the reference point. -/
theorem continuousAt_linear_factor_of_surjective_kernel
    {V E F T : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F]
    [FiniteDimensional ℂ V] [FiniteDimensional ℂ E] [FiniteDimensional ℂ F]
    [TopologicalSpace T] (A : T → V →L[ℂ] E) (D : T → V →L[ℂ] F)
    (v : T → V) (t : T) (hA : ContinuousAt A t) (hD : ContinuousAt D t)
    (hsurj : Function.Surjective (A t))
    (hker : ∀ s, Function.Surjective (A s) →
      LinearMap.ker (A s).toLinearMap ≤ LinearMap.ker (D s).toLinearMap)
    (hv : ContinuousAt (fun s => A s (v s)) t) :
    ContinuousAt (fun s => D s (v s)) t := by
  apply continuousAt_linear_factor_image A D v t hA hD hsurj ?_ hv
  filter_upwards [eventually_surjective_of_continuousAt A t hA hsurj] with s hs
  exact hker s hs

#print axioms continuousAt_linear_factor_of_surjective_kernel

end HodgeLean.Foundations.Program.G32Native
