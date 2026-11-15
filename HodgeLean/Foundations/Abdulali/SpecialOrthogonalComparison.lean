import HodgeLean.Foundations.Abdulali.SpecialOrthogonalGeneration
import HodgeLean.Foundations.Abdulali.SpecialOrthogonalExteriorTangent
import HodgeLean.Foundations.Abdulali.SpecialOrthogonalExteriorFixed

noncomputable section
open scoped TensorProduct
open HodgeLean.Foundations HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.Abdulali

/-- For the standard representation with trivial multiplicities, the alternating
images of SO-fixed tensors are precisely the vectors killed by its orthogonal
Lie algebra. The comparison includes the empty tensor degree.
Source: Borel, Linear Algebraic Groups, II.7; Humphreys, Linear Algebraic
Groups, §7.5 and §13.2; characteristic-zero alternating tensor splitting. -/
theorem special_orthogonal_exterior_comparison_aux
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (B : LinearMap.BilinForm ℂ V) (hB : B.Nondegenerate) (hs : B.IsSymm)
    (r n : ℕ) (v : ⋀[ℂ]^n (Fin r → V)) :
    (∀ X : Module.End ℂ V, (∀ x y, B (X x) y + B x (X y) = 0) →
      InvariantsExterior.exteriorDer n (m1b_copies r X) v = 0) ↔
    v ∈ (m1b_fixed (m1b_copies r ''
      {u ∈ m1b_isometries B | LinearMap.det u = 1}) n).map
        (InvariantsExterior.wedgeQuotient n) := by
  constructor
  · intro hv
    apply (exterior_fixed_iff_mem_fixed_tensor_image _ n v).mp
    rintro _ ⟨u, ⟨hu, hd⟩, rfl⟩
    exact special_orthogonal_exterior_fixed_of_killed B hB hs r n v hv u hu hd
  · exact special_orthogonal_tensor_image_killed B hB r n v

end HodgeLean.Foundations.Abdulali
