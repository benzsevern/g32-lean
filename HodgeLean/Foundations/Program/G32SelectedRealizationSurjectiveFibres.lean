import HodgeLean.Foundations.Program.G32SelectedRealizationProjector

noncomputable section
namespace HodgeLean.Foundations.Program

def g32y_equiv_of_surjective_fibres {A B C : Type*} (p : A → B) (q : A → C)
    (hp : Function.Surjective p) (hq : Function.Surjective q)
    (h : ∀ a b, p a = p b ↔ q a = q b) : B ≃ C := by
  classical
  let f : B → C := fun b ↦ q (Function.surjInv hp b)
  apply Equiv.ofBijective f
  constructor
  · intro b b' he
    have hh := (h (Function.surjInv hp b) (Function.surjInv hp b')).mpr he
    simpa only [Function.surjInv_eq hp] using hh
  · intro c
    obtain ⟨a, rfl⟩ := hq c
    refine ⟨p a, ?_⟩
    exact (h (Function.surjInv hp (p a)) a).mp (Function.surjInv_eq hp (p a))

theorem g32y_equiv_of_surjective_fibres_apply {A B C : Type*} (p : A → B) (q : A → C)
    (hp : Function.Surjective p) (hq : Function.Surjective q)
    (h : ∀ a b, p a = p b ↔ q a = q b) (a : A) :
    g32y_equiv_of_surjective_fibres p q hp hq h (p a) = q a := by
  change q (Function.surjInv hp (p a)) = q a
  exact (h (Function.surjInv hp (p a)) a).mp (Function.surjInv_eq hp (p a))

end HodgeLean.Foundations.Program
