import HodgeLean.Foundations.Program.GriffithsTransversality
import HodgeLean.Foundations.Program.PeriodDerivative

/-! Primitive multiplication and its residue array. HC no distance; AV milestone no distance. -/
noncomputable section
open Set Filter Topology Manifold
open scoped TensorProduct
namespace HodgeLean.Foundations.Program
attribute [local instance] Classical.propDecidable
attribute [local instance] rf8_SharedFamily.topC rf8_SharedFamily.chartC
  rf8_SharedFamily.manC rf8_SharedFamily.t2C rf8_SharedFamily.compactC
  rf8_SharedFamily.connectedC rf8_SharedFamily.actionC rf8_SharedFamily.totalChart
  rf8_SharedFamily.totalMan rf8_SharedFamily.fibreChart rf8_SharedFamily.fibreMan
  rf8_SharedFamily.fibreT2 rf8_SharedFamily.fibreCompact rf8_SharedFamily.fibreConnected
  rf8_SharedFamily.fibreFaithful

/-- Averaged products of primitive forms, as raw quadratic coefficients.
Source: Forster, Lectures on Riemann Surfaces, §9; Serre, §2.2. -/
def b66m_multiply (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (q r : b66g_primitiveForms R t) : b66g_Coeff R :=
  b66g_average R t (b66g_product R q.val r.val)
example (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (q r : b66g_primitiveForms R t) :
    b66m_multiply R t q r = b66g_average R t (b66g_product R q.val r.val) := rfl

/-- Residue multiplication array on three selected forms in each eigen-direction.
The pole data are supplied separately for each of the ten standard branch velocities.
Source: Griffiths, Periods II, §1; Forster, §17. -/
def b66m_multiplicationMatrix (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (q r : Fin 3 → b66g_primitiveForms R t)
    (S : Fin 10 → Finset R.C) (v : Fin 10 → b66k_Index R → ℂ → ℂ) :
    Matrix (Fin 9) (Fin 10) ℂ := fun i j =>
  b66g_residueSum R t (S j) (v j)
    (b66m_multiply R t (q ((finProdFinEquiv : Fin 3 × Fin 3 ≃ Fin 9).symm i).1) (r ((finProdFinEquiv : Fin 3 × Fin 3 ≃ Fin 9).symm i).2))
example (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (q r : Fin 3 → b66g_primitiveForms R t)
    (S : Fin 10 → Finset R.C) (v : Fin 10 → b66k_Index R → ℂ → ℂ)
    (i : Fin 9) (j : Fin 10) :
    b66m_multiplicationMatrix R t q r S v i j =
      b66g_residueSum R t (S j) (v j)
        (b66m_multiply R t (q ((finProdFinEquiv : Fin 3 × Fin 3 ≃ Fin 9).symm i).1)
          (r ((finProdFinEquiv : Fin 3 × Fin 3 ≃ Fin 9).symm i).2)) := rfl

/-- Tangent evaluations reconstructed using the retained chart centred at the point.
Source: Forster, Lectures on Riemann Surfaces, §9, coordinate expression of a differential. -/
def b66m_chartForm (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (q : b66g_Coeff R) : TangentBundle 𝓘(ℂ, ℂ) (rf8_fibre R.C t) → ℂ :=
  fun p => q (t, p.1.val.2) p.1.val.2 *
    (show ℂ from mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ)
      (fun y : rf8_fibre R.C t => (R.atlas.A (t, p.1.val.2) y.val).2) p.1 p.2)
example (R : rf8_SharedFamily) (t : b6t_polydisc mr_base) :
    b66m_chartForm R t 0 = 0 := by
  funext p
  exact zero_mul _

/-- Output change of coordinates: pair each negative tail variation with the positive
holomorphic frame, using the original model polarization; rows index products qᵢ rⱼ.
Source: Griffiths, Periods II, §1; van Geemen, LNM 1594, §5.10. -/
def b66m_leftMatrix (z : Fin 9 → ℂ) (κ : ℂ) : Matrix (Fin 9) (Fin 9) ℂ :=
  fun a b =>
    let ij := (finProdFinEquiv : Fin 3 × Fin 3 ≃ Fin 9).symm a
    let kl := (finProdFinEquiv : Fin 3 × Fin 3 ≃ Fin 9).symm b
    if ij.1 = kl.2 then κ * b60_E.baseChange ℂ
      (b60c_eigenBasis (0, Fin.natAdd 3 kl.1)) (b60_frame z (1, ij.2)) else 0
example (z : Fin 9 → ℂ) : b66m_leftMatrix z 0 = 0 := by
  funext a b
  simp only [b66m_leftMatrix, zero_mul, ite_self, Matrix.zero_apply]

/-- Multiplication jet along a parameter path, extended by zero outside the retained domain.
No certificate is part of this definition.
Source: G32, Lemma 5.1; g32r_PeriodMap.codiff. -/
def b66m_jet (R : rf8_SharedFamily)
    (q r : (t : b6t_polydisc mr_base) → Fin 3 → b66g_primitiveForms R t)
    (S : (t : b6t_polydisc mr_base) → Fin 10 → Finset R.C)
    (v : (t : b6t_polydisc mr_base) → Fin 10 → b66k_Index R → ℂ → ℂ)
    (curve : ℂ → Fin 10 → ℂ) (θ : ℂ) : Matrix (Fin 9) (Fin 10) ℂ :=
  if ht : curve θ ∈ b6t_polydisc mr_base then
    b66m_multiplicationMatrix R ⟨curve θ, ht⟩ (q ⟨curve θ, ht⟩) (r ⟨curve θ, ht⟩) (S ⟨curve θ, ht⟩) (v ⟨curve θ, ht⟩) else 0
example (R : rf8_SharedFamily)
    (q r : (t : b6t_polydisc mr_base) → Fin 3 → b66g_primitiveForms R t)
    (S : (t : b6t_polydisc mr_base) → Fin 10 → Finset R.C)
    (v : (t : b6t_polydisc mr_base) → Fin 10 → b66k_Index R → ℂ → ℂ)
    (curve : ℂ → Fin 10 → ℂ) (θ : ℂ) (ht : curve θ ∈ b6t_polydisc mr_base) :
    b66m_jet R q r S v curve θ =
      b66m_multiplicationMatrix R ⟨curve θ, ht⟩ (q ⟨curve θ, ht⟩) (r ⟨curve θ, ht⟩) (S ⟨curve θ, ht⟩) (v ⟨curve θ, ht⟩) := by
  exact dite_eq_left ht

end HodgeLean.Foundations.Program
