import HodgeLean.Foundations.Program.G32Native.EulerModel.GlobalNormalKernel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! # Homogeneous projection defining the global normal-model section -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
open scoped BigOperators ComplexConjugate
namespace HodgeLean.Foundations.Program.G32Native.EulerModel

/-- Squared Hermitian length of the full homogeneous vector. -/
def normalLengthSq (k : ℕ) (v : ℂ × (Fin k → ℂ)) : ℝ :=
  Complex.normSq v.1 + ∑ i, Complex.normSq (v.2 i)

/-- A nonzero homogeneous representative has strictly positive squared length. -/
theorem normalLengthSq_pos (k : ℕ) (v : ℂ × (Fin k → ℂ)) (hv : v ≠ 0) :
    0 < normalLengthSq k v := by
  classical
  unfold normalLengthSq
  by_cases h0 : v.1 = 0
  · have ht : v.2 ≠ 0 := by
      intro ht
      exact hv (Prod.ext h0 ht)
    obtain ⟨i, hi⟩ := Function.ne_iff.mp ht
    apply add_pos_of_nonneg_of_pos (Complex.normSq_nonneg _)
    exact Finset.sum_pos' (fun j _ => Complex.normSq_nonneg (v.2 j))
      ⟨i, Finset.mem_univ i, Complex.normSq_pos.mpr hi⟩
  · exact add_pos_of_pos_of_nonneg (Complex.normSq_pos.mpr h0)
      (Finset.sum_nonneg fun i _ => Complex.normSq_nonneg (v.2 i))

#print axioms normalLengthSq_pos
/-- Hermitian length scales by the squared norm of the homogeneous scalar. -/
theorem normalLengthSq_smul (k : ℕ) (v : ℂ × (Fin k → ℂ)) (a : ℂ) :
    normalLengthSq k (a • v) = Complex.normSq a * normalLengthSq k v := by
  simp [normalLengthSq, smul_eq_mul, Complex.normSq_mul, mul_add, Finset.mul_sum]

#print axioms normalLengthSq_smul
/-- Project the first coordinate covector to the homogeneous evaluation kernel. -/
def homogeneousNormalSection (k : ℕ) (v : ℂ × (Fin k → ℂ)) : ℂ × (Fin k → ℂ) :=
  (1, 0) - (v.1 / (normalLengthSq k v : ℂ)) •
    (conj v.1, fun i => conj (v.2 i))

/-- The projected covector belongs to the actual evaluation kernel. -/
theorem homogeneousNormalSection_mem (k : ℕ) (v : ℂ × (Fin k → ℂ)) (hv : v ≠ 0) :
    homogeneousNormalSection k v ∈ LinearMap.ker (homogeneousNormalEvaluation k v) := by
  rw [LinearMap.mem_ker]
  have hN : (normalLengthSq k v : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (normalLengthSq_pos k v hv))
  have hpair : homogeneousNormalEvaluation k v (conj v.1, fun i => conj (v.2 i)) =
      (normalLengthSq k v : ℂ) := by
    simp [homogeneousNormalEvaluation_apply, normalLengthSq, Complex.mul_conj]
  have he0 : homogeneousNormalEvaluation k v (1, 0) = v.1 := by
    simp [homogeneousNormalEvaluation_apply]
  unfold homogeneousNormalSection
  rw [map_sub, map_smul, hpair, he0]
  simp only [smul_eq_mul, div_mul_cancel₀ _ hN, sub_self]

#print axioms homogeneousNormalSection_mem
/-- The projected covector is unchanged by every nonzero homogeneous scaling. -/
theorem homogeneousNormalSection_smul (k : ℕ) (v : ℂ × (Fin k → ℂ)) (hv : v ≠ 0)
    (a : ℂ) (ha : a ≠ 0) :
    homogeneousNormalSection k (a • v) = homogeneousNormalSection k v := by
  have hN : (normalLengthSq k v : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (normalLengthSq_pos k v hv))
  have hca : conj a ≠ 0 := by simpa using ha
  have hC : (conj (a • v).1, fun i => conj ((a • v).2 i)) =
      conj a • (conj v.1, fun i => conj (v.2 i)) := by
    apply Prod.ext
    · simp [smul_eq_mul]
    · funext i
      simp [smul_eq_mul]
  have hcoef : (a * v.1) / ((Complex.normSq a : ℂ) * (normalLengthSq k v : ℂ)) * conj a =
      v.1 / (normalLengthSq k v : ℂ) := by
    rw [← Complex.mul_conj a]
    field_simp [ha, hca, hN]
  unfold homogeneousNormalSection
  rw [hC, normalLengthSq_smul, Complex.ofReal_mul]
  change (1, 0) - ((a * v.1) / ((Complex.normSq a : ℂ) * (normalLengthSq k v : ℂ))) •
      (conj a • (conj v.1, fun i => conj (v.2 i))) = _
  rw [smul_smul, hcoef]

#print axioms homogeneousNormalSection_smul
/-- The projected covector as a global function of the projective line. -/
def projectiveNormalSectionVector (k : ℕ)
    (p : Projectivization ℂ (ℂ × (Fin k → ℂ))) : ℂ × (Fin k → ℂ) :=
  Projectivization.lift (fun v => homogeneousNormalSection k v.1)
    (by
      intro v w a ha
      have ha0 : a ≠ 0 := by
        intro hzero
        apply v.2
        rw [ha, hzero, zero_smul]
      rw [ha]
      exact homogeneousNormalSection_smul k w.1 w.2 a ha0) p

/-- The global projected vector is the original projection on every homogeneous representative. -/
theorem projectiveNormalSectionVector_mk (k : ℕ) (v : ℂ × (Fin k → ℂ)) (hv : v ≠ 0) :
    projectiveNormalSectionVector k (Projectivization.mk ℂ v hv) = homogeneousNormalSection k v := by
  rfl

#print axioms projectiveNormalSectionVector_mk
/-- The descended projected vector lies in the kernel attached to that same projective line. -/
theorem projectiveNormalSectionVector_mem (k : ℕ)
    (p : Projectivization ℂ (ℂ × (Fin k → ℂ))) :
    projectiveNormalSectionVector k p ∈ projectiveNormalKernel k p := by
  induction p using Projectivization.ind with
  | h v hv =>
    rw [projectiveNormalSectionVector_mk, projectiveNormalKernel_mk]
    exact homogeneousNormalSection_mem k v hv

/-- The global section with its actual varying evaluation-kernel fibre retained. -/
def projectiveNormalSection (k : ℕ) (p : Projectivization ℂ (ℂ × (Fin k → ℂ))) :
    projectiveNormalKernel k p :=
  ⟨projectiveNormalSectionVector k p, projectiveNormalSectionVector_mem k p⟩

#print axioms projectiveNormalSectionVector_mem
/-- The homogeneous projection vanishes exactly on the first coordinate axis. -/
theorem homogeneousNormalSection_zero_iff (k : ℕ) (v : ℂ × (Fin k → ℂ)) (hv : v ≠ 0) :
    homogeneousNormalSection k v = 0 ↔ v.2 = 0 := by
  have hN : (normalLengthSq k v : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (normalLengthSq_pos k v hv))
  constructor
  · intro hz
    have hh := congrArg (fun w : ℂ × (Fin k → ℂ) => w.1) hz
    have hv0 : v.1 ≠ 0 := by
      intro hzero
      simpa [homogeneousNormalSection, hzero] using hh
    have hcoef : v.1 / (normalLengthSq k v : ℂ) ≠ 0 := div_ne_zero hv0 hN
    funext i
    have hi := congrArg (fun w : ℂ × (Fin k → ℂ) => w.2 i) hz
    have hi' : -(v.1 / (normalLengthSq k v : ℂ) * conj (v.2 i)) = 0 := by
      simpa [homogeneousNormalSection, smul_eq_mul] using hi
    have hc := (mul_eq_zero.mp (neg_eq_zero.mp hi')).resolve_left hcoef
    simpa using hc
  · intro ht
    have hv0 : v.1 ≠ 0 := by
      intro hzero
      exact hv (Prod.ext hzero ht)
    have hc0 : conj v.1 ≠ 0 := by simpa using hv0
    have hNval : (normalLengthSq k v : ℂ) = v.1 * conj v.1 := by
      simp [normalLengthSq, ht, Complex.mul_conj]
    apply Prod.ext
    · change 1 - v.1 / (normalLengthSq k v : ℂ) * conj v.1 = 0
      rw [hNval]
      field_simp [hv0, hc0]
      simp
    · funext i
      simp [homogeneousNormalSection, ht]

#print axioms homogeneousNormalSection_zero_iff
/-- The first coordinate line in the projective normal model. -/
def normalProjectiveBase (k : ℕ) : Projectivization ℂ (ℂ × (Fin k → ℂ)) :=
  Projectivization.mk ℂ (1, 0) (by
    intro h
    exact one_ne_zero (congrArg (fun w : ℂ × (Fin k → ℂ) => w.1) h))

/-- The descended global section has exactly the first coordinate line as its zero. -/
theorem projectiveNormalSectionVector_zero_iff (k : ℕ)
    (p : Projectivization ℂ (ℂ × (Fin k → ℂ))) :
    projectiveNormalSectionVector k p = 0 ↔ p = normalProjectiveBase k := by
  constructor
  · intro hz
    induction p using Projectivization.ind with
    | h v hv =>
      have ht : v.2 = 0 := (homogeneousNormalSection_zero_iff k v hv).mp
        (by simpa only [projectiveNormalSectionVector_mk] using hz)
      unfold normalProjectiveBase
      rw [Projectivization.mk_eq_mk_iff']
      refine ⟨v.1, ?_⟩
      apply Prod.ext <;> simp [ht, smul_eq_mul]
  · rintro rfl
    unfold normalProjectiveBase
    rw [projectiveNormalSectionVector_mk]
    exact (homogeneousNormalSection_zero_iff k _ (by
      intro h
      exact one_ne_zero (congrArg (fun w : ℂ × (Fin k → ℂ) => w.1) h))).mpr rfl

#print axioms projectiveNormalSectionVector_zero_iff
end HodgeLean.Foundations.Program.G32Native.EulerModel
