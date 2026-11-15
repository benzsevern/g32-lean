import HodgeLean.Blocks.Weil.ExteriorRestriction

/-! # Exterior quotients and the scalar derivation -/

noncomputable section

namespace HodgeBlocks.ExteriorRestriction

variable {K V : Type*} [Field K] [Algebra ℚ K] [AddCommGroup V]
  [Module K V] [Module ℚ V] [IsScalarTower ℚ K V]

/-- Multiplication by a field element, read as a rational endomorphism. -/
def scalarEnd (a : K) : V →ₗ[ℚ] V where
  toFun x := a • x
  map_add' := smul_add a
  map_smul' r x := smul_comm a r x

/-- On K-wedges the Leibniz derivation of a scalar acts by degree times that scalar. -/
theorem quotient_derivationExt (a : K) (n : ℕ) (x : ⋀[ℚ]^n V) :
    quotient (K := K) n (derivationExt (scalarEnd (V := V) a) n x) =
      ((n : K) * a) • quotient (K := K) n x := by
  classical
  let f : (⋀[ℚ]^n V) →ₗ[ℚ] (⋀[K]^n V) :=
    (quotient (K := K) n).comp (derivationExt (scalarEnd (V := V) a) n)
  let g : (⋀[ℚ]^n V) →ₗ[ℚ] (⋀[K]^n V) :=
    { toFun := fun y => ((n : K) * a) • quotient (K := K) n y
      map_add' := by intro y z; rw [map_add, smul_add]
      map_smul' := by intro r y; rw [map_smul, smul_comm, RingHom.id_apply] }
  have hfg : f = g := by
    apply LinearMap.ext_on (exteriorPower.ιMulti_span ℚ n V)
    rintro _ ⟨v, rfl⟩
    change quotient (K := K) n (derivationExt (scalarEnd (V := V) a) n
      (exteriorPower.ιMulti ℚ n v)) = _
    change quotient (K := K) n (derivationExt (scalarEnd (V := V) a) n
      (exteriorPower.ιMulti ℚ n v)) = ((n : K) * a) •
        quotient (K := K) n (exteriorPower.ιMulti ℚ n v)
    rw [derivationExt_ιMulti, map_sum, quotient_ιMulti]
    change (∑ i : Fin n, quotient (K := K) n
      (exteriorPower.ιMulti ℚ n (Function.update v i (a • v i)))) = _
    simp only [quotient_ιMulti, (exteriorPower.ιMulti K n).map_update_smul,
      Function.update_eq_self, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    change n • (a • exteriorPower.ιMulti K n v) =
      ((n : K) * a) • exteriorPower.ιMulti K n v
    rw [← smul_assoc, nsmul_eq_mul]
  exact DFunLike.congr_fun hfg x

#print axioms scalarEnd
#print axioms quotient_derivationExt

end HodgeBlocks.ExteriorRestriction
