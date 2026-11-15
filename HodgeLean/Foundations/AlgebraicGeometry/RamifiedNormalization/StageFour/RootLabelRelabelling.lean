import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.ComponentLabels

noncomputable section
set_option Elab.async false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace AlgebraicGeometry.RamifiedNormalization.StageFour

/-- Any two primitive-root enumerations of the same nonzero selector roots differ by a unique permutation of labels. -/
theorem binomial_root_relabelling
    (g : ℕ) (hg : 0 < g) (κ ζ κ' ζ' : ℂ)
    (hκ : κ ≠ 0) (hκ' : κ' ≠ 0)
    (hζ : IsPrimitiveRoot ζ g) (hζ' : IsPrimitiveRoot ζ' g)
    (hpower : κ ^ g = κ' ^ g) :
    ∃! e : ZMod g ≃ ZMod g, ∀ l, κ' * ζ' ^ (e l).val = κ * ζ ^ l.val := by
  let b : ZMod g → ℂ := fun l => κ * ζ ^ l.val
  let b' : ZMod g → ℂ := fun l => κ' * ζ' ^ l.val
  have hp (l : ZMod g) : b l ^ g = κ ^ g := by
    dsimp only [b]
    rw [mul_pow, ← pow_mul, Nat.mul_comm l.val g, pow_mul, hζ.pow_eq_one,
      one_pow, mul_one]
  have hp' (l : ZMod g) : b' l ^ g = κ' ^ g := by
    dsimp only [b']
    rw [mul_pow, ← pow_mul, Nat.mul_comm l.val g, pow_mul, hζ'.pow_eq_one,
      one_pow, mul_one]
  have hb : Function.Injective b := by
    intro i j h
    obtain ⟨k, _, hk⟩ := binomial_root_label g hg κ ζ (b i) hκ hζ (hp i)
    exact (hk i rfl).trans (hk j h).symm
  have hb' : Function.Injective b' := by
    intro i j h
    obtain ⟨k, _, hk⟩ := binomial_root_label g hg κ' ζ' (b' i) hκ' hζ' (hp' i)
    exact (hk i rfl).trans (hk j h).symm
  have hex (i : ZMod g) : ∃ j, b' j = b i := by
    obtain ⟨j, hj, _⟩ := binomial_root_label g hg κ' ζ' (b i) hκ' hζ'
      ((hp i).trans hpower)
    exact ⟨j, hj.symm⟩
  let f : ZMod g → ZMod g := fun i => Classical.choose (hex i)
  have hf (i) : b' (f i) = b i := Classical.choose_spec (hex i)
  have hbij : Function.Bijective f := by
    constructor
    · intro i j h
      exact hb ((hf i).symm.trans ((congrArg b' h).trans (hf j)))
    · intro j
      obtain ⟨i, hi, _⟩ := binomial_root_label g hg κ ζ (b' j) hκ hζ
        ((hp' j).trans hpower.symm)
      exact ⟨i, hb' ((hf i).trans hi.symm)⟩
  refine ⟨Equiv.ofBijective f hbij, hf, ?_⟩
  intro e he
  ext i
  exact hb' ((he i).trans (hf i).symm)

end AlgebraicGeometry.RamifiedNormalization.StageFour
