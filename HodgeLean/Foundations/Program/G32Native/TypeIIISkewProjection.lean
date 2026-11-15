import HodgeLean.Foundations.Program.G32Native.TypeIIISkewDiagonalVector

noncomputable section
namespace HodgeLean.Foundations.Program.G32Native

/-- Coefficient along a vector with nonzero diagonal value, retaining the
order of the quaternion division. -/
def typeIIISkewCoefficient {D V : Type*} [DivisionRing D]
    [AddCommGroup V] [Module D V] (H : V → V → D)
    (hadd : ∀ v w x, H (v + w) x = H v x + H w x)
    (hsmul : ∀ (q : D) v x, H (q • v) x = q * H v x) (x : V) : V →ₗ[D] D where
  toFun v := H v x * (H x x)⁻¹
  map_add' v w := by rw [hadd, add_mul]
  map_smul' q v := by
    change H (q • v) x * (H x x)⁻¹ = q * (H v x * (H x x)⁻¹)
    rw [hsmul, mul_assoc]

/-- The chosen diagonal vector has coefficient one. -/
theorem typeIIISkewCoefficient_self {D V : Type*} [DivisionRing D]
    [AddCommGroup V] [Module D V] (H : V → V → D)
    (hadd : ∀ v w x, H (v + w) x = H v x + H w x)
    (hsmul : ∀ (q : D) v x, H (q • v) x = q * H v x)
    (x : V) (hx : H x x ≠ 0) : typeIIISkewCoefficient H hadd hsmul x x = 1 :=
  mul_inv_cancel₀ hx

/-- The coefficient kernel is the left orthogonal complement of the chosen
nonisotropic vector. -/
theorem typeIIISkewCoefficient_ker {D V : Type*} [DivisionRing D]
    [AddCommGroup V] [Module D V] (H : V → V → D)
    (hadd : ∀ v w x, H (v + w) x = H v x + H w x)
    (hsmul : ∀ (q : D) v x, H (q • v) x = q * H v x)
    (x v : V) (hx : H x x ≠ 0) :
    v ∈ LinearMap.ker (typeIIISkewCoefficient H hadd hsmul x) ↔ H v x = 0 := by
  change H v x * (H x x)⁻¹ = 0 ↔ H v x = 0
  exact mul_eq_zero_iff_right (inv_ne_zero hx)

end HodgeLean.Foundations.Program.G32Native

#print axioms HodgeLean.Foundations.Program.G32Native.typeIIISkewCoefficient_self
#print axioms HodgeLean.Foundations.Program.G32Native.typeIIISkewCoefficient_ker
