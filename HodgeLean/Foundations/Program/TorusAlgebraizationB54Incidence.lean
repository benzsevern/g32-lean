import HodgeLean.Foundations.Program.TorusAlgebraizationB54Cone
import HodgeLean.Foundations.AnalyticDivisorAlgebraic2

noncomputable section
namespace HodgeLean.Foundations.Program

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {ι : Type} [Fintype ι]

def b54_vectorIncidence (f : E → ι → ℂ) : Set (E × (ι → ℂ)) :=
  {p | ∀ i j, f p.1 i * p.2 j - f p.1 j * p.2 i = 0}

theorem b54_vectorIncidence_iff (f : E → ι → ℂ) (z : E) (v : ι → ℂ)
    (hf : f z ≠ 0) : (z, v) ∈ b54_vectorIncidence f ↔ ∃ c : ℂ, v = c • f z := by
  classical
  obtain ⟨i, hi⟩ : ∃ i, f z i ≠ 0 := by
    by_contra h
    apply hf
    funext i
    simpa using not_exists.mp h i
  constructor
  · intro h
    refine ⟨v i / f z i, ?_⟩
    funext j
    have hj := sub_eq_zero.mp (h i j)
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [div_mul_eq_mul_div, eq_div_iff hi]
    simpa only [mul_comm] using hj
  · rintro ⟨c, rfl⟩ i j
    simp only [Pi.smul_apply, smul_eq_mul]
    ring

theorem b54_vectorIncidence_isClosedAnalytic [FiniteDimensional ℂ E] (f : E → ι → ℂ)
    (hf : ∀ i, Differentiable ℂ (fun z => f z i)) :
    IsClosedAnalytic (E × (ι → ℂ)) (b54_vectorIncidence f) := by
  have h (ij : ι × ι) : IsClosedAnalytic (E × (ι → ℂ))
      {p : E × (ι → ℂ) | f p.1 ij.1 * p.2 ij.2 - f p.1 ij.2 * p.2 ij.1 = 0} := by
    apply AnalyticDivisorAlgebraic2.spec_isClosedAnalytic_zeroSet_of_differentiable
    have hfst (i : ι) : Differentiable ℂ (fun p : E × (ι → ℂ) => f p.1 i) :=
      (hf i).comp differentiable_fst
    have hsnd (i : ι) : Differentiable ℂ (fun p : E × (ι → ℂ) => p.2 i) := by
      fun_prop
    exact ((hfst ij.1).mul (hsnd ij.2)).sub ((hfst ij.2).mul (hsnd ij.1))
  convert IsClosedAnalytic.biInter_finset (Finset.univ : Finset (ι × ι))
    (fun ij _ => h ij) using 1
  ext p
  simp [b54_vectorIncidence]

end HodgeLean.Foundations.Program
