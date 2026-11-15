import HodgeLean.Foundations.Program.SchoenTowerL1bDivisorFractionCharacter
import HodgeLean.Foundations.Program.SchoenTowerL1bDivisorPullbackOrder

noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- Local pullback and a power rescaling give the base order of a rational character function. -/
theorem s2v_l1b_divisor_local_calculation
    {R T E K : Type*} [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]
    [CommRing T] [IsDomain T] [Field E] [Field K]
    [Algebra T E] [IsFractionRing T E]
    (φ : R →+* T) (hφ : Function.Injective φ)
    (ι : T →+* PowerSeries K) (hι : Function.Injective ι)
    (θ : T →+* T) (τ : E →+* E) (ξ : K)
    (hτ : ∀ a : T, τ (algebraMap T E a) = algebraMap T E (θ a))
    {m e q k : ℕ} (hm : m ≠ 0) (he : e ≠ 0) (hme : m = e * q)
    (hξ : IsPrimitiveRoot ξ m)
    (hθ : ∀ a : T, ι (θ a) = PowerSeries.rescale (ξ ^ q) (ι a))
    (c : T) (hc : ι c = PowerSeries.C (ξ ^ k))
    (u : E) (hu : u ≠ 0) (heigen : τ u = algebraMap T E c * u)
    (p : R) (hp : Prime p)
    (hlocal : ∀ v : R, ¬ p ∣ v → (ι (φ v)).constantCoeff ≠ 0)
    (heorder : (ι (φ p)).order.toNat = e)
    (A B : R) (hA : A ≠ 0) (hB : B ≠ 0)
    (hpow : u ^ m = algebraMap T E (φ A) / algebraMap T E (φ B)) :
    Int.ModEq (m : ℤ)
      (((emultiplicity p A).toNat : ℤ) - ((emultiplicity p B).toNat : ℤ)) (k : ℤ) := by
  obtain ⟨a, b, ha, hb, hab, hres⟩ :=
    s2v_l1b_divisor_fraction_power_character ι hι θ τ ξ hτ hθ hm hξ c hc u hu heigen
  have ho := s2v_l1b_divisor_pullback_fraction_order φ (algebraMap T E)
    (IsFractionRing.injective T E) ι hι p hp hlocal a b ha hb A B hA hB
    (fun h => hA (hφ (h.trans φ.map_zero.symm)))
    (fun h => hB (hφ (h.trans φ.map_zero.symm))) m (by rw [← hab]; exact hpow)
  rw [heorder] at ho
  have hmc : (m : ℤ) = (e : ℤ) * (q : ℤ) := by exact_mod_cast hme
  have hv : ((emultiplicity p A).toNat : ℤ) - ((emultiplicity p B).toNat : ℤ) =
      (q : ℤ) * (((ι a).order.toNat : ℤ) - ((ι b).order.toNat : ℤ)) := by
    apply mul_left_cancel₀ (by exact_mod_cast he : (e : ℤ) ≠ 0)
    rw [← mul_assoc, ← hmc]
    exact ho.symm
  rw [hv]
  exact hres

end HodgeLean.Foundations.Program
