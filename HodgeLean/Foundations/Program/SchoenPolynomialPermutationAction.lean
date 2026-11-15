import HodgeLean.Foundations.Program.SchoenSegreCoordinateRenames

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial
namespace HodgeLean.Foundations.Program

/-- The actual polynomial ring action obtained by inverse permutation of tuple factors. -/
def s2_polynomialPermutationAction (R : Type) [CommRing R] (d n : ℕ)
    {G : Type} [Group G] (σ : G →* Equiv.Perm (Fin n)) :
    MulSemiringAction G (MvPolynomial (Fin n → Fin (d + 1)) R) where
  smul g p := MvPolynomial.rename (fun b i => b ((σ g).symm i)) p
  one_smul p := by
    change MvPolynomial.rename (fun b i => b ((σ 1).symm i)) p = p
    simp only [map_one, Equiv.Perm.one_symm, Equiv.Perm.one_apply]
    exact MvPolynomial.rename_id_apply p
  mul_smul g h p := by
    change MvPolynomial.rename (fun b i => b ((σ (g * h)).symm i)) p =
      MvPolynomial.rename (fun b i => b ((σ g).symm i))
        (MvPolynomial.rename (fun b i => b ((σ h).symm i)) p)
    simp only [map_mul, MvPolynomial.rename_rename, Function.comp_def]
    rfl
  smul_zero g := by
    change MvPolynomial.rename (fun b i => b ((σ g).symm i)) (0 : MvPolynomial (Fin n → Fin (d + 1)) R) = 0
    exact map_zero _
  smul_add g p q := by
    change MvPolynomial.rename (fun b i => b ((σ g).symm i)) (p + q) = _ + _
    exact map_add _ _ _
  smul_one g := by
    change MvPolynomial.rename (fun b i => b ((σ g).symm i)) (1 : MvPolynomial (Fin n → Fin (d + 1)) R) = 1
    exact map_one _
  smul_mul g p q := by
    change MvPolynomial.rename (fun b i => b ((σ g).symm i)) (p * q) = _ * _
    exact map_mul _ _ _

end HodgeLean.Foundations.Program
