import HodgeLean.Foundations.Program.G32Native.TypeIIISkewProjection

noncomputable section
namespace HodgeLean.Foundations.Program.G32Native

/-- Splitting off a vector with nonzero diagonal value over a division ring.
The second factor is its orthogonal coefficient kernel. -/
def typeIIISkewSplit {D V : Type*} [DivisionRing D]
    [AddCommGroup V] [Module D V] (H : V → V → D)
    (hadd : ∀ v w x, H (v + w) x = H v x + H w x)
    (hsmul : ∀ (q : D) v x, H (q • v) x = q * H v x)
    (x : V) (hx : H x x ≠ 0) :
    (D × LinearMap.ker (typeIIISkewCoefficient H hadd hsmul x)) ≃ₗ[D] V := by
  let p := typeIIISkewCoefficient H hadd hsmul x
  have hp : p x = 1 := typeIIISkewCoefficient_self H hadd hsmul x hx
  let f : (D × LinearMap.ker p) →ₗ[D] V :=
    { toFun := fun v => v.1 • x + v.2
      map_add' := by
        rintro ⟨a, u⟩ ⟨b, v⟩
        simp only [Prod.fst_add, Prod.snd_add, Submodule.coe_add, add_smul]
        abel
      map_smul' := by
        intro a v
        change (a * v.1) • x + a • (v.2 : V) = a • (v.1 • x + (v.2 : V))
        rw [smul_add, mul_smul] }
  apply LinearEquiv.ofBijective f
  constructor
  · rintro ⟨a, u⟩ ⟨b, v⟩ huv
    have hab : a = b := by
      have h := congrArg p huv
      change p (a • x + (u : V)) = p (b • x + (v : V)) at h
      simpa only [map_add, map_smul, hp, smul_eq_mul, mul_one,
        LinearMap.mem_ker.mp u.property, LinearMap.mem_ker.mp v.property, add_zero] using h
    subst b
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      change a • x + (u : V) = a • x + (v : V) at huv
      exact add_left_cancel huv
  · intro v
    refine ⟨(p v, ⟨v - p v • x, ?_⟩), ?_⟩
    · change p (v - p v • x) = 0
      simp only [map_sub, map_smul, hp, smul_eq_mul, mul_one, sub_self]
    · change p v • x + (v - p v • x) = v
      abel

end HodgeLean.Foundations.Program.G32Native

#print axioms HodgeLean.Foundations.Program.G32Native.typeIIISkewSplit
