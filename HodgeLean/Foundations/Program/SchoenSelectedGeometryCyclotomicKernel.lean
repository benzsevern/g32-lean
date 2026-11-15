import HodgeLean.Foundations.Program.SchoenSelectedGeometryCyclotomicInverse
import HodgeLean.Foundations.Program.G32SelectedRealizationPrimitiveAction

noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- Inverse linear operators have equal primitive cyclotomic kernels. -/
theorem s0_cyclotomic_inverse_kernel {m : ℕ} [NeZero m]
    {V : Type*} [AddCommGroup V] [Module ℚ V]
    (T U : Module.End ℚ V) (hTU : T * U = 1) (hUT : U * T = 1) :
    LinearMap.ker (Polynomial.aeval T (Polynomial.cyclotomic m ℚ)) =
      LinearMap.ker (Polynomial.aeval U (Polynomial.cyclotomic m ℚ)) := by
  have step (T U : Module.End ℚ V) (hTU : T * U = 1) (hUT : U * T = 1) :
      LinearMap.ker (Polynomial.aeval T (Polynomial.cyclotomic m ℚ)) ≤
        LinearMap.ker (Polynomial.aeval U (Polynomial.cyclotomic m ℚ)) := by
    let p := Polynomial.cyclotomic m ℚ
    let W := LinearMap.ker (Polynomial.aeval T p)
    have stable (A : Module.End ℚ V) (hA : A ∘ₗ T = T ∘ₗ A) :
        ∀ v ∈ W, A v ∈ W := by
      intro v hv
      have hh := LinearMap.congr_fun (g32y_aeval_intertwine A T T hA p) v
      change A (Polynomial.aeval T p v) = Polynomial.aeval T p (A v) at hh
      change Polynomial.aeval T p v = 0 at hv
      change Polynomial.aeval T p (A v) = 0
      rw [hv, map_zero] at hh
      exact hh.symm
    have ht := stable T rfl
    have hu := stable U (show U * T = T * U by rw [hUT, hTU])
    have htu : T.restrict ht * U.restrict hu = 1 := by
      ext v
      exact congrArg (fun A : Module.End ℚ V ↦ A v) hTU
    have hp : Polynomial.aeval (T.restrict ht) p = 0 :=
      g32y_restrict_aeval_zero T W ht p (fun _ hv ↦ hv)
    have hq := s0_cyclotomic_inverse_relation (T.restrict ht) (U.restrict hu) htu hp
    have hh := g32y_aeval_intertwine W.subtype (U.restrict hu) U rfl p
    intro v hv
    have he := LinearMap.congr_fun hh (⟨v, hv⟩ : W)
    rw [hq] at he
    change Polynomial.aeval U p v = 0
    simpa only [LinearMap.comp_apply, LinearMap.zero_apply, map_zero, Submodule.subtype_apply] using he.symm
  exact le_antisymm (step T U hTU hUT) (step U T hUT hTU)

#print axioms s0_cyclotomic_inverse_kernel
end HodgeLean.Foundations.Program
