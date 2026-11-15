import HodgeLean.Foundations.Program.SchoenTowerHardtCad5SectionMembership
import HodgeLean.Foundations.Program.SchoenTowerHardtCad5GenericSections
import HodgeLean.Foundations.Program.SchoenTowerHardtCad5BlockLimits
import HodgeLean.Foundations.Program.SchoenTowerHardtCad5CoefficientField
import HodgeLean.Foundations.Program.SchoenTowerHardtCad5CoefficientTransport

/-! Generic ambient limit membership for carriers covered by actual root tuples. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

theorem s2v_hardt_cad5_root_tuple_limit_mem {n q r : ℕ}
    (C : s2v_t11b_Formula n) (ψ : Fin r → C.realize → ℝ)
    (hψ : ∀ i, Continuous (ψ i))
    (g : Fin r → s2v_t11b_Formula (n + 1))
    (hg : ∀ j y, y ∈ (g j).realize ↔ ∃ a : C.realize,
      (∀ v, y v.succ = a.val v) ∧ y 0 = ψ j a)
    (S : s2v_t11b_Formula (q + n))
    (hCover : ∀ (t : EuclideanSpace ℝ (Fin q)) (a : C.realize),
      WithLp.toLp 2 (Fin.append (fun i => t i) (fun i => a.val i)) ∈ S.realize →
        ∀ i, ∃ j, t i = ψ j a) :
    ∃ K : Subfield ℝ, Countable K ∧
      ∀ L : Subfield ℝ, K ≤ L →
      ∀ a : EuclideanSpace ℝ (Fin n), a ∈ C.realize →
        AlgebraicIndependent L (fun i => a i) → ∀ t : EuclideanSpace ℝ (Fin q),
        WithLp.toLp 2 (Fin.append (fun i => t i) (fun i => a i)) ∈ closure S.realize →
        WithLp.toLp 2 (Fin.append (fun i => t i) (fun i => a i)) ∈ S.realize := by
  classical
  choose M hM using fun f : Fin q → Fin r =>
    s2v_hardt_cad5_section_tuple_membership_formula C ψ g hg S f
  let F : Option (Fin q → Fin r) → s2v_t11b_Formula n := fun o => o.elim C M
  obtain ⟨K, hK, hcoeff⟩ := s2v_hardt_cad5_formula_coefficient_field_fintype n F
  refine ⟨K, hK, ?_⟩
  intro L hKL a ha hgen t hcl
  let χ : (Fin q → Fin r) → C.realize → EuclideanSpace ℝ (Fin q) :=
    fun f b => WithLp.toLp 2 (fun i => ψ (f i) b)
  have hχ : ∀ f, Continuous (χ f) := fun f =>
    (PiLp.continuous_toLp 2 _).comp (continuous_pi (fun i => hψ (f i)))
  have hCcoeff := s2v_hardt_cad5_atom_lifts_mono K L hKL C (hcoeff none)
  have hMcoeff := fun f => s2v_hardt_cad5_atom_lifts_mono K L hKL (M f) (hcoeff (some f))
  let T : Set (EuclideanSpace ℝ (Fin q) × EuclideanSpace ℝ (Fin n)) :=
    {p | WithLp.toLp 2 (Fin.append (fun i => p.1 i) (fun i => p.2 i)) ∈ S.realize}
  have hTcover : ∀ y (b : C.realize), (y, b.val) ∈ T → ∃ f, y = χ f b := by
    intro y b hy
    choose f hf using hCover y b hy
    refine ⟨f, ?_⟩
    ext i
    exact hf i
  exact s2v_hardt_cad5_generic_finite_sections_mem L C M hCcoeff hMcoeff χ hχ T
    hTcover hM a ha hgen t (s2v_hardt_cad5_block_closure_split S.realize t a hcl)

end HodgeLean.Foundations.Program
