import HodgeLean.Foundations.Program.G32Native.SplitKernelPairing

/-! # Exactness from a split tangent map and a nondegenerate normal pairing -/
noncomputable section
set_option maxHeartbeats 200000
namespace HodgeLean.Foundations.Program.G32Native

/-- A split tangent map fills the kernel when the pairing is injective on
the complementary normal subspace. -/
theorem ker_eq_range_of_split_pairing
    {K E T N : Type*} [Field K]
    [AddCommGroup E] [Module K E] [AddCommGroup T] [Module K T]
    [AddCommGroup N] [Module K N]
    (A : E →ₗ[K] N) (t : T →ₗ[K] E) (p : E →ₗ[K] T)
    (hpt : p.comp t = LinearMap.id) (hat : A.comp t = 0)
    (hi : Function.Injective (A.comp p.ker.subtype)) :
    LinearMap.ker A = LinearMap.range t := by
  apply le_antisymm
  · intro w hw
    have hpw : p (w - t (p w)) = 0 := by
      rw [map_sub, show p (t (p w)) = p w from DFunLike.congr_fun hpt (p w), sub_self]
    let v : p.ker := ⟨w - t (p w), hpw⟩
    have hv : v = 0 := by
      apply hi
      change A (w - t (p w)) = A 0
      rw [map_sub, show A (t (p w)) = 0 from DFunLike.congr_fun hat (p w),
        show A w = 0 from hw, sub_zero, map_zero]
    have hv' : w - t (p w) = 0 := congrArg Subtype.val hv
    exact ⟨p w, (sub_eq_zero.mp hv').symm⟩
  · rintro w ⟨v, rfl⟩
    exact DFunLike.congr_fun hat v

#print axioms ker_eq_range_of_split_pairing
end HodgeLean.Foundations.Program.G32Native
