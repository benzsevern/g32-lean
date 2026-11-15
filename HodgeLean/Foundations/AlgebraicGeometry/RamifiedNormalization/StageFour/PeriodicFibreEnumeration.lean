import Mathlib.Dynamics.PeriodicPts.Defs
import Mathlib.Data.Fintype.Card

noncomputable section
set_option Elab.async false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace AlgebraicGeometry.RamifiedNormalization.StageFour

/-- A fibre that is one periodic orbit is enumerated exactly by its positive return divisor. -/
theorem periodic_fibre_enumeration
    {X B : Type*} (d : X → X) (p : X → B) (x : X) (N : ℕ) (hN : 0 < N)
    (hp : ∀ y, p (d y) = p y)
    (horbit : ∀ y, p y = p x → ∃ k : ℕ, d^[k] x = y)
    (hreturn : ∀ k : ℕ, d^[k] x = x ↔ N ∣ k) :
    ∃ e : Fin N ≃ {y : X // p y = p x}, ∀ i, (e i).val = d^[i.val] x := by
  have hper : Function.IsPeriodicPt d N x := (hreturn N).mpr (dvd_refl N)
  have hmin : Function.minimalPeriod d x = N := by
    apply Nat.dvd_antisymm hper.minimalPeriod_dvd
    exact (hreturn _).mp (Function.isPeriodicPt_minimalPeriod d x)
  have hpiterate (k : ℕ) : p (d^[k] x) = p x := by
    induction k with
    | zero => rfl
    | succ k ih => rw [Function.iterate_succ_apply', hp, ih]
  let f : Fin N → {y : X // p y = p x} := fun i => ⟨d^[i.val] x, hpiterate i.val⟩
  have hinj : Function.Injective f := by
    intro i j hij
    apply Fin.ext
    apply Function.iterate_injOn_Iio_minimalPeriod (f := d) (x := x)
    · change i.val < Function.minimalPeriod d x
      rw [hmin]
      exact i.isLt
    · change j.val < Function.minimalPeriod d x
      rw [hmin]
      exact j.isLt
    · exact congrArg Subtype.val hij
  have hsurj : Function.Surjective f := by
    intro y
    obtain ⟨k, hk⟩ := horbit y.val y.property
    refine ⟨⟨k % N, Nat.mod_lt _ hN⟩, Subtype.ext ?_⟩
    change d^[k % N] x = y.val
    rw [← hmin, Function.iterate_mod_minimalPeriod_eq, hk]
  exact ⟨Equiv.ofBijective f ⟨hinj, hsurj⟩, fun _ => rfl⟩

end AlgebraicGeometry.RamifiedNormalization.StageFour
