import HodgeLean.Foundations.Program.SchoenCycleAdicAlgebraMap

/-! # Identity on the canonical adic algebra -/
noncomputable section
namespace HodgeLean.Foundations.Program

/-- The canonical adic map of the identity algebra homomorphism is the
identity on every formal element. -/
theorem s2e_c1_adic_algebra_map_id
    {k R : Type*} [CommRing k] [CommRing R] [Algebra k R] (I : Ideal R)
    (h : ∀ n a, a ∈ I ^ n → (AlgHom.id k R) a ∈ I ^ n) :
    s2e_adic_algebra_map I I (AlgHom.id k R) h = AlgHom.id k (AdicCompletion I R) := by
  apply AlgHom.ext
  intro z
  apply AdicCompletion.ext
  intro n
  change Ideal.quotientMapₐ (I ^ n • ⊤ : Ideal R) (AlgHom.id k R) _ (z.val n) = z.val n
  exact Quotient.inductionOn' (z.val n) (fun _ => rfl)

end HodgeLean.Foundations.Program
