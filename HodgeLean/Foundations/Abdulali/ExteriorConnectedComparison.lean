import HodgeLean.Foundations.Abdulali.ExteriorMatrixStabilizer
import HodgeLean.Foundations.Abdulali.ExteriorExponential
import HodgeLean.Foundations.MatrixAlgGroupLie

noncomputable section
set_option maxHeartbeats 200000
open HodgeLean.Foundations HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.Abdulali
variable {V : Type*} [AddCommGroup V] [Module ℂ V] {d : ℕ}

/-- An exterior vector killed by a matrix velocity has that velocity in the
tangent space of its algebraic stabilizer, using the actual exponential curve. -/
theorem killed_mem_exterior_stabilizer_tangent (b : Module.Basis (Fin d) ℂ V)
    (r n : ℕ) (v : ⋀[ℂ]^n (Fin r → V)) (X : Matrix (Fin d) (Fin d) ℂ)
    (hv : InvariantsExterior.exteriorDer n (m1b_copies r (Matrix.toLin b b X)) v = 0) :
    X ∈ g1_lieAlgebra (exteriorMatrixStabilizer b r n v) := by
  apply g1_mem_lieOfSet_iff.mpr
  intro f hf
  have hγ : ∀ i j, HasDerivAt (fun s : ℂ => NormedSpace.exp (s • X) i j) (X i j) 0 := by
    intro i j
    simpa using g2k_hasDerivAt_exp_mul X 1 0 i j
  have hd := g2k_hasDerivAt_differential (fun s => NormedSpace.exp (s • X)) X 0
    (by simp only [zero_smul, NormedSpace.exp_zero]) hγ f
  have hz : (fun s : ℂ => MvPolynomial.eval
      (fun ij => NormedSpace.exp (s • X) ij.1 ij.2) f) = fun _ => 0 := by
    funext s
    have hs : g2k_expGL X s ∈ (exteriorMatrixStabilizer b r n v).carrier := by
      rw [mem_exteriorMatrixStabilizer, g2k_coe_expGL]
      exact exterior_exp_fixed_of_killed b r n X v hv s
    have hh := g1_mem_vanishingIdealSet_iff.mp hf _ hs
    change MvPolynomial.eval
      (fun ij => (g2k_expGL X s : Matrix (Fin d) (Fin d) ℂ) ij.1 ij.2) f = 0 at hh
    rw [g2k_coe_expGL] at hh
    exact hh
  rw [hz] at hd
  exact hd.unique (hasDerivAt_const 0 0)

/-- For a connected matrix algebraic group, annihilation by its tangent space
implies fixedness on every exterior power of repeated standard copies. -/
theorem exterior_fixed_of_connected_tangent_killed (b : Module.Basis (Fin d) ℂ V)
    (G : MatrixAlgGroup ℂ d) (hG : g1_IsConnected G) (r n : ℕ)
    (v : ⋀[ℂ]^n (Fin r → V))
    (hv : ∀ X ∈ g1_lieAlgebra G,
      InvariantsExterior.exteriorDer n (m1b_copies r (Matrix.toLin b b X)) v = 0)
    (g : Matrix.GeneralLinearGroup (Fin d) ℂ) (hg : g ∈ G.carrier) :
    exteriorPower.map n (m1b_copies r (Matrix.toLin b b ↑g)) v = v := by
  let H := exteriorMatrixStabilizer b r n v
  let I := g1_inter G H
  have hle : g1_lieAlgebra G ≤ g1_lieAlgebra H := by
    intro X hX
    exact killed_mem_exterior_stabilizer_tangent b r n v X (hv X hX)
  have hlie : g1_lieAlgebra I = g1_lieAlgebra G := by
    rw [g1_lie_inf G H I rfl, inf_eq_left.mpr hle]
  have hsub := g1_le_of_lie_eq_of_dim G I hG inf_le_left hlie
    (g1_finrank_lie_eq_krullDim G) (g1_finrank_lie_eq_krullDim I)
  exact (mem_exteriorMatrixStabilizer b r n v g).mp (hsub hg).2

end HodgeLean.Foundations.Abdulali
