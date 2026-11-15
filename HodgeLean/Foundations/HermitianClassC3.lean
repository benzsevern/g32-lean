import HodgeLean.Foundations.MeyerRationalS9
import Mathlib.LinearAlgebra.QuadraticForm.Prod

noncomputable section
namespace HodgeLean.Foundations.HermitianClass

set_option maxHeartbeats 400000 in

/-- A regular indefinite rational quadratic form of rank at least four represents every
nonzero rational number.
Source: Serre, *A Course in Arithmetic*, Chapter IV, p. 43, Corollary 2. -/
theorem quadratic_represents_nonzero (V : Type*) [AddCommGroup V] [Module ℚ V]
    [FiniteDimensional ℚ V] (q : QuadraticForm ℚ V)
    (hq : q.associated.SeparatingLeft) (hrank : 4 ≤ Module.finrank ℚ V)
    (hp : ∃ x, 0 < q x) (hn : ∃ x, q x < 0) (a : ℚ) (ha : a ≠ 0) :
    ∃ x, q x = a := by
  let qa : QuadraticForm ℚ ℚ := (-a) • QuadraticMap.sq (R := ℚ) (A := ℚ)
  let Q : QuadraticForm ℚ (V × ℚ) := q.prod qa
  have hqa : qa.associated.SeparatingLeft := by
    intro z hz
    specialize hz 1
    simp [qa, QuadraticMap.sq, QuadraticMap.linMulLin_apply] at hz
    exact hz.resolve_left ha
  have hQ : Q.associated.SeparatingLeft := by
    intro z hz
    apply Prod.ext
    · apply hq z.1
      intro y
      have := hz (y, 0)
      simpa [Q] using this
    · apply hqa z.2
      intro y
      have := hz (0, y)
      simpa [Q] using this
  have hdim : 5 ≤ Module.finrank ℚ (V × ℚ) := by
    rw [Module.finrank_prod, Module.finrank_self]
    omega
  have hQp : ∃ z, 0 < Q z := by
    obtain ⟨x, hx⟩ := hp
    exact ⟨(x, 0), by simpa [Q, qa] using hx⟩
  have hQn : ∃ z, Q z < 0 := by
    obtain ⟨x, hx⟩ := hn
    exact ⟨(x, 0), by simpa [Q, qa] using hx⟩
  obtain ⟨z, hz, hzero⟩ := meyer_isotropic (V × ℚ) Q hQ hdim hQp hQn
  by_cases hz2 : z.2 = 0
  · have hz1 : z.1 ≠ 0 := by
      intro hz1
      apply hz
      exact Prod.ext hz1 hz2
    have hqz : q z.1 = 0 := by simpa [Q, qa, hz2] using hzero
    obtain ⟨y, hxy⟩ := not_forall.mp (fun hall => hz1 (hq z.1 hall))
    let B := q.associated
    let y' := y - (q y / (2 * B z.1 y)) • z.1
    have hB : B z.1 y ≠ 0 := hxy
    have hxy' : B z.1 y' = B z.1 y := by
      simp only [y', map_sub, map_smul, B, hqz, smul_zero, sub_zero]
      rw [QuadraticMap.associated_eq_self_apply, hqz]
      simp
    have hqy' : q y' = 0 := by
      rw [show y' = y + -((q y / (2 * B z.1 y)) • z.1) by
        exact sub_eq_add_neg _ _]
      rw [QuadraticMap.map_add q, QuadraticMap.map_neg, QuadraticMap.map_smul, hqz,
        smul_zero, add_zero]
      rw [show QuadraticMap.polar (⇑q) y (-((q y / (2 * B z.1 y)) • z.1)) =
          2 * B y (-((q y / (2 * B z.1 y)) • z.1)) by
        change q.polarBilin y (-((q y / (2 * B z.1 y)) • z.1)) = _
        rw [← QuadraticMap.two_nsmul_associated ℚ]
        rfl]
      simp only [map_neg, map_smul, smul_eq_mul]
      have hsym : B y z.1 = B z.1 y := (QuadraticForm.associated_isSymm ℚ q).eq y z.1
      rw [hsym]
      simp only [B]
      field_simp
      ring
    refine ⟨z.1 + (a / (2 * B z.1 y)) • y', ?_⟩
    rw [QuadraticMap.map_add q, hqz, QuadraticMap.map_smul, hqy', smul_zero, add_zero]
    rw [show QuadraticMap.polar (⇑q) z.1 ((a / (2 * B z.1 y)) • y') =
        2 * B z.1 ((a / (2 * B z.1 y)) • y') by
      change q.polarBilin z.1 ((a / (2 * B z.1 y)) • y') = _
      rw [← QuadraticMap.two_nsmul_associated ℚ]
      rfl]
    simp only [map_smul, smul_eq_mul, hxy']
    field_simp
    ring
  · refine ⟨z.2⁻¹ • z.1, ?_⟩
    have heq : q z.1 = a * z.2 ^ 2 := by
      have hzero' : q z.1 - a * (z.2 * z.2) = 0 := by
        simpa [Q, qa, QuadraticMap.sq, QuadraticMap.linMulLin_apply, sub_eq_add_neg] using hzero
      simpa [pow_two] using sub_eq_zero.mp hzero'
    rw [QuadraticMap.map_smul, heq]
    simp only [smul_eq_mul]
    field_simp

#print axioms quadratic_represents_nonzero

end HodgeLean.Foundations.HermitianClass
