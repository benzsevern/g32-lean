import HodgeLean.Foundations.Program.SchoenCycleInverseIndexedInvariants

/-! # Ambient values under inverse indexing of invariants -/
noncomputable section
namespace HodgeLean.Foundations.Program

/-- Reindexing fixed elements by inverses retains their ambient values. -/
theorem s2e_c1_inverse_indexed_invariant_val
    {k R G : Type*} [CommRing k] [CommRing R] [Algebra k R] [Group G]
    (α : G → (R →ₐ[k] R))
    (z : (⨅ g, AlgHom.equalizer (α g) (AlgHom.id k R) : Subalgebra k R)) :
    (s2e_inverse_indexed_invariant_equiv α z).val = z.val := by
  rfl

end HodgeLean.Foundations.Program
