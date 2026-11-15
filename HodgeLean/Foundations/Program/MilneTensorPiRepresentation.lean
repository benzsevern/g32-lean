import HodgeLean.Foundations.Program.MilneTensorDefs

noncomputable section
namespace HodgeLean.Foundations.Program
variable {ι : Type*} {R M : ι → Type*}
    [∀ i, Ring (R i)] [∀ i, Algebra ℂ (R i)]
    [∀ i, AddCommGroup (M i)] [∀ i, Module ℂ (M i)]

def m1b_piRepresentation (ρ : (i : ι) → R i →ₐ[ℂ] Module.End ℂ (M i)) :
    ((i : ι) → R i) →ₐ[ℂ] Module.End ℂ ((i : ι) → M i) where
  toFun X := LinearMap.piMap (fun i => ρ i (X i))
  map_one' := by
    apply LinearMap.ext
    intro v
    funext i
    change ρ i 1 (v i) = v i
    rw [map_one, Module.End.one_apply]
  map_mul' X Y := by
    apply LinearMap.ext
    intro v
    funext i
    change ρ i (X i * Y i) (v i) = ρ i (X i) (ρ i (Y i) (v i))
    rw [map_mul, Module.End.mul_apply]
  map_zero' := by
    apply LinearMap.ext
    intro v
    funext i
    change ρ i 0 (v i) = 0
    rw [map_zero, LinearMap.zero_apply]
  map_add' X Y := by
    apply LinearMap.ext
    intro v
    funext i
    change ρ i (X i + Y i) (v i) = ρ i (X i) (v i) + ρ i (Y i) (v i)
    rw [map_add, LinearMap.add_apply]
  commutes' z := by
    apply LinearMap.ext
    intro v
    funext i
    change ρ i (algebraMap ℂ (R i) z) (v i) = z • v i
    rw [AlgHom.commutes]
    rfl

end HodgeLean.Foundations.Program
