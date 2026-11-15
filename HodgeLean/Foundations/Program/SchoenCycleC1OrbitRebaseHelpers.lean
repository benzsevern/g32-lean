import Mathlib.Data.Fintype.EquivFin
import Mathlib.Logic.Function.Iterate

/-! # Changing the base point of a finite free orbit -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- An injective fibre-preserving map with one exhaustive free finite orbit
has an exhaustive free orbit from every point of that fibre. -/
theorem s2e_c1_orbit_rebase {A B : Type*} (f : A → A) (p : A → B)
    (hf : Function.Injective f) (hp : ∀ a, p (f a) = p a)
    (m : ℕ) (z : A)
    (hinj : Function.Injective (fun t : Fin m => f^[t.val] z))
    (hex : ∀ a, p a = p z → ∃ t : Fin m, f^[t.val] z = a)
    (w : A) (hw : p w = p z) :
    Function.Injective (fun t : Fin m => f^[t.val] w) ∧
      (∀ a, p a = p z → ∃ t : Fin m, f^[t.val] w = a) := by
  classical
  have hiter (n : ℕ) (a : A) : p (f^[n] a) = p a := by
    induction n with
    | zero => rfl
    | succ n ih => rw [Function.iterate_succ_apply', hp, ih]
  obtain ⟨k, hk⟩ := hex w hw
  have hcomm (i : ℕ) : f^[i] w = f^[k.val] (f^[i] z) := by
    rw [← hk, ← Function.iterate_add_apply, Nat.add_comm, Function.iterate_add_apply]
  have hi : Function.Injective (fun t : Fin m => f^[t.val] w) := by
    intro t u htu
    change f^[t.val] w = f^[u.val] w at htu
    rw [hcomm, hcomm] at htu
    exact hinj ((hf.iterate k.val) htu)
  let F := {a : A // p a = p z}
  let φ : Fin m → F := fun t => ⟨f^[t.val] z, hiter t.val z⟩
  have hφ : Function.Bijective φ := by
    constructor
    · intro t u htu
      exact hinj (congrArg Subtype.val htu)
    · intro a
      obtain ⟨t, ht⟩ := hex a.val a.property
      exact ⟨t, Subtype.ext ht⟩
  let e : Fin m ≃ F := Equiv.ofBijective φ hφ
  letI : Fintype F := Fintype.ofEquiv (Fin m) e
  let ψ : Fin m → F := fun t => ⟨f^[t.val] w, (hiter t.val w).trans hw⟩
  have hψinj : Function.Injective ψ := by
    intro t u htu
    exact hi (congrArg Subtype.val htu)
  have hψ : Function.Surjective ψ :=
    ((Fintype.bijective_iff_injective_and_card ψ).mpr
      ⟨hψinj, Fintype.card_congr e⟩).2
  refine ⟨hi, ?_⟩
  intro a ha
  obtain ⟨t, ht⟩ := hψ ⟨a, ha⟩
  exact ⟨t, congrArg Subtype.val ht⟩

end HodgeLean.Foundations.Program
