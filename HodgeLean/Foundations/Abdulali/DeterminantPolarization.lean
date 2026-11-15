import HodgeLean.Foundations.InvariantsExterior
import HodgeLean.Foundations.RationalPolarization

noncomputable section
open HodgeLean.Foundations InvariantsExterior
namespace HodgeLean.Foundations.Abdulali

/-- Mixed alternating volume blocks are spanned by diagonal blocks with rational
multiplicity coordinates. Both the alternating sign and the permutation of the
standard factor are retained on the left.
Source: Weyl, The Classical Groups, Chapter II, §9 (polarization);
van Geemen–Verra, Quaternionic Pryms and Hodge Classes, §4.6. -/
theorem alternating_volume_mem_span_rational_diagonals
    {V M : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup M] [Module ℂ M]
    {n m : ℕ} (j : V →ₗ[ℂ] (Fin m → ℂ) →ₗ[ℂ] M)
    (v : Fin n → V) (a : Fin n → (Fin m → ℂ)) :
    (∑ σ : Equiv.Perm (Fin n), Equiv.Perm.sign σ •
      exteriorPower.ιMulti ℂ n (fun i => j (v (σ i)) (a i))) ∈
    Submodule.span ℂ (Set.range (fun b : Fin m → ℚ =>
      exteriorPower.ιMulti ℂ n (fun i => j (v i) (fun k => (b k : ℂ))))) := by
  rw [antisymmetrized_multiplicities_eq_mixedDeterminant]
  apply (Submodule.span_le.mpr ?_)
    (mixedDeterminant_mem_span_diagonal j v a)
  rintro _ ⟨b, rfl⟩
  exact multilinear_diagonal_mem_span_rat (multiplicityWedge j v) b

/-- The same reduction after a linear comparison, for example the complexified
cup-wedge isomorphism. No injectivity of that comparison is needed.
Source: Weyl, The Classical Groups, Chapter II, §9 (polarization and functoriality). -/
theorem alternating_volume_map_mem_span_rational_diagonals
    {V M N : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup M] [Module ℂ M]
    [AddCommGroup N] [Module ℂ N] {n m : ℕ}
    (j : V →ₗ[ℂ] (Fin m → ℂ) →ₗ[ℂ] M) (v : Fin n → V)
    (a : Fin n → (Fin m → ℂ)) (f : (⋀[ℂ]^n M) →ₗ[ℂ] N) :
    f (∑ σ : Equiv.Perm (Fin n), Equiv.Perm.sign σ •
      exteriorPower.ιMulti ℂ n (fun i => j (v (σ i)) (a i))) ∈
    Submodule.span ℂ (Set.range (fun b : Fin m → ℚ =>
      f (exteriorPower.ιMulti ℂ n (fun i => j (v i) (fun k => (b k : ℂ)))))) := by
  have h := Submodule.mem_map_of_mem (f := f)
    (alternating_volume_mem_span_rational_diagonals j v a)
  rw [Submodule.map_span] at h
  apply (Submodule.span_mono ?_) h
  rintro _ ⟨_, ⟨b, rfl⟩, rfl⟩
  exact ⟨b, rfl⟩

/-- Exterior projection of a labelled alternating tensor is the exact signed
volume block used by polarization. This keeps the tensor-to-exterior
normalization visible to tensor invariant-generation consumers.
Source: Weyl, The Classical Groups, Chapter II, §9; functoriality of the
universal alternating map. -/
theorem wedge_labelled_antisymTensor
    {V B M : Type*} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup B] [Module ℂ B] [AddCommGroup M] [Module ℂ M]
    {n : ℕ} (j : V →ₗ[ℂ] B →ₗ[ℂ] M) (v : Fin n → V) (labels : Fin n → B) :
    wedgeQuotient n
      (PiTensorProduct.map (fun i => j.flip (labels i))
        (SchurWeyl.antisymTensor ℂ V (Fin n) v)) =
      ∑ σ : Equiv.Perm (Fin n), Equiv.Perm.sign σ •
        exteriorPower.ιMulti ℂ n (fun i => j (v (σ i)) (labels i)) := by
  simp only [SchurWeyl.antisymTensor_apply, map_sum, map_zsmul,
    PiTensorProduct.map_tprod, wedgeQuotient_tprod, LinearMap.flip_apply, Units.smul_def]

end HodgeLean.Foundations.Abdulali
