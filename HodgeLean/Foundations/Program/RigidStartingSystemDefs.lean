import HodgeLean.Foundations.Program.FuchsianSystemDefs
import HodgeLean.Foundations.Program.PrymFamilyExistsDefs

/-! # Explicit starting residues and numerical rigidity data

The four-point system precedes the degree-six pullback. HC no distance; AV milestone no distance.
-/

noncomputable section
open Set Matrix
namespace HodgeLean.Foundations.Program

/-- Matrix action on column vectors, with its finite-dimensional topology.
Source: G32 v0.16, Appendix A, column-vector convention. -/
def b65r_operator {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    (Fin n → ℂ) →L[ℂ] (Fin n → ℂ) := A.mulVecLin.toContinuousLinearMap

example : b65r_operator (1 : Matrix (Fin 4) (Fin 4) ℂ) = 1 := by
  ext v i
  simp [b65r_operator]

/-- The residue at zero of the four-point system.
Source: G32 v0.16, §5.2 and Appendix A, the displayed B₀. -/
def b65r_B0 : Matrix (Fin 4) (Fin 4) ℂ :=
  diagonal ![-3/4, -1/2, -1/2, 3/4]

example : b65r_B0 0 0 = -3/4 := rfl

/-- The rank-one residue at five, with the rational outer-product factors printed in the source.
Source: G32 v0.16, Appendix A, u₁ and v₁. -/
def b65r_B5 : Matrix (Fin 4) (Fin 4) ℂ :=
  fun i j ↦ (![1, 1, 0, 1] : Fin 4 → ℂ) i *
    (![119/648, 28/135, -41472/289, -187/3240] : Fin 4 → ℂ) j

example : b65r_B5 0 2 = -41472/289 := by norm_num [b65r_B5]

/-- The rank-one residue at minus seven.
Source: G32 v0.16, Appendix A, u₂ and v₂. -/
def b65r_Bneg7 : Matrix (Fin 4) (Fin 4) ℂ :=
  fun i j ↦ (![-5598720/14161, 0, 1, 5598720/22253] : Fin 4 → ℂ) i *
    (![-2648107/3627970560, -1090397/755827200, 56/135,
      -2648107/18139852800] : Fin 4 → ℂ) j

example : b65r_Bneg7 2 2 = 56/135 := by norm_num [b65r_Bneg7]

/-- The residue in the coordinate w = 1/z at infinity.
Source: G32 v0.16, §5.2, B∞ = −(B₀ + B₅ + B₋₇). -/
def b65r_Binf : Matrix (Fin 4) (Fin 4) ℂ := -(b65r_B0 + b65r_B5 + b65r_Bneg7)

example : b65r_B0 + b65r_B5 + b65r_Bneg7 + b65r_Binf = 0 := by
  simp [b65r_Binf]

/-- The residue tuple in the order of the printed four-point monodromy tuple.
Source: G32 v0.16, §5.2, puncture order 5, −7, 0, ∞. -/
def b65r_residues : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ :=
  ![b65r_B5, b65r_Bneg7, b65r_B0, b65r_Binf]

example : b65r_residues 3 = b65r_Binf := rfl

/-- The concrete rational coefficient on the z-plane.
Source: G32 v0.16, §5.2, the displayed differential system. -/
def b65r_A (z : ℂ) : (Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ) :=
  z⁻¹ • b65r_operator b65r_B0 + (z-5)⁻¹ • b65r_operator b65r_B5 +
    (z+7)⁻¹ • b65r_operator b65r_Bneg7

example : b65r_A 1 = b65r_operator b65r_B0 +
    (-4 : ℂ)⁻¹ • b65r_operator b65r_B5 + (8 : ℂ)⁻¹ • b65r_operator b65r_Bneg7 := by
  norm_num [b65r_A]

/-- The degree-six rational map used before normalization of the branch points.
Source: G32 v0.16, §5.2, φ(s). -/
def b65r_phi (s : ℂ) : ℂ := s^2 * (s-3)^4 / ((s-1)^3 * (s+2)^3)

example : b65r_phi 0 = 0 := by norm_num [b65r_phi]

/-- The polynomial cutting out the fibre over ε.
Source: G32 v0.16, §5.2, P₅ and P₋₇. -/
def b65r_P (ε s : ℂ) : ℂ := s^2 * (s-3)^4 - ε * (s-1)^3 * (s+2)^3

example : b65r_P 5 0 = 40 := by norm_num [b65r_P]

/-- The pulled-back rational coefficient, including the apparent poles.
Source: G32 v0.16, §5.4, residues at 0, 3, 1, −2 and the reflection poles. -/
def b65r_pullback (s : ℂ) : (Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ) :=
  (2/s + 4/(s-3)) • b65r_operator b65r_B0 +
  (deriv (b65r_P 5) s / b65r_P 5 s) • b65r_operator b65r_B5 +
  (deriv (b65r_P (-7)) s / b65r_P (-7) s) • b65r_operator b65r_Bneg7 +
  (3/(s-1) + 3/(s+2)) • b65r_operator b65r_Binf

example (s : ℂ) : b65r_pullback s =
    (2/s + 4/(s-3)) • b65r_operator b65r_B0 +
    (deriv (b65r_P 5) s / b65r_P 5 s) • b65r_operator b65r_B5 +
    (deriv (b65r_P (-7)) s / b65r_P (-7) s) • b65r_operator b65r_Bneg7 +
    (3/(s-1) + 3/(s+2)) • b65r_operator b65r_Binf := rfl

/-- Local monodromy targets on the unnormalized pullback sphere.
Source: G32 v0.16, §5.2, local ramification indices 2, 4, 3, 3. -/
def b65r_localTarget (a : ℂ) : b4b_Group :=
  if a = 0 then (b4b_generators 2)^2
  else if a = 3 then (b4b_generators 2)^4
  else if a = 1 ∨ a = -2 then (b4b_generators 3)^3
  else if b65r_P 5 a = 0 then b4b_generators 0
  else b4b_generators 1

example : b65r_localTarget 0 = b4b_root 12 := by
  simp [b65r_localTarget, b4b_root]

/-- Linear centralizer of a matrix, used to measure local conjugacy classes.
Source: Katz, Rigid Local Systems, §1.1, centralizer dimension formula. -/
def b65r_centralizer {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    Submodule ℂ (Matrix (Fin n) (Fin n) ℂ) where
  carrier := {X | A * X = X * A}
  zero_mem' := by simp
  add_mem' := by intro X Y hX hY; simp only [mem_ofPred_eq] at *; rw [mul_add, add_mul, hX, hY]
  smul_mem' := by intro c X hX; simp only [mem_ofPred_eq] at *; simpa only [mul_smul_comm, smul_mul_assoc] using congrArg (c • ·) hX

example : (1 : Matrix (Fin 4) (Fin 4) ℂ) ∈ b65r_centralizer b65r_B0 := by
  change b65r_B0 * 1 = 1 * b65r_B0
  simp

/-- Euler-characteristic rigidity index, evaluated in integers to retain negative values.
Source: Katz, Rigid Local Systems, §1.1, rig(T) = (2−r)n² + Σ dim Z(Tᵢ). -/
def b65r_index {n r : ℕ} (T : Fin r → Matrix (Fin n) (Fin n) ℂ) : ℤ :=
  (2 - (r : ℤ)) * (n : ℤ)^2 + ∑ i, (Module.finrank ℂ (b65r_centralizer (T i)) : ℤ)

example : (2 - (4 : ℤ)) * 4^2 + (10 + 10 + 6 + 8) = 2 := by norm_num
example : (2 - (13 : ℤ)) * 4^2 + (12 * 10 + 8) = -48 := by norm_num

/-- The twelve finite marked poles in B6-2 coordinates.
Source: b6_branch, mr_marks and b6t_punctured. -/
def b65r_marks : Finset ℂ := Finset.univ.image mr_marks

example : (0 : ℂ) ∈ b65r_marks := by
  exact Finset.mem_image.mpr ⟨10, Finset.mem_univ _, rfl⟩

/-- Plane traces of the thirteen marked peripheral curves.
Source: mr_curve, mr_lasso and mr_outer. -/
def b65r_curve (i : Fin 13) (s : ℝ) : ℂ :=
  if h : i.val < 12 then mr_lasso (mr_marks ⟨i.val, h⟩) s else mr_outer s

example (s : ℝ) : b65r_curve 12 s = mr_outer s := by simp [b65r_curve]

example : 0 < Module.finrank ℂ (Fin 4 → ℂ) := by simp
example : b65r_B5 ≠ 0 := by
  intro h
  have := congrFun (congrFun h 0) 0
  norm_num [b65r_B5] at this
example : Matrix.trace b65r_B5 = 1/3 := by
  norm_num [Matrix.trace, Fin.sum_univ_succ, b65r_B5]
example : Matrix.trace b65r_Bneg7 = 2/3 := by
  norm_num [Matrix.trace, Fin.sum_univ_succ, b65r_Bneg7]

/-- A positive-rank, nonidentity input for the index-two criterion.
Source: Katz, Rigid Local Systems, §1.1, rank-one two-puncture case. -/
example :
    let T : Fin 2 → (Matrix (Fin 1) (Fin 1) ℂ)ˣ := fun _ ↦ -1
    (List.ofFn T).prod = 1 ∧ T 0 ≠ 1 ∧
    b65r_index (fun i ↦ (T i).val) = 2 ∧
    (∀ W : Submodule ℂ (Fin 1 → ℂ),
      (∀ i v, v ∈ W → (T i).val.mulVec v ∈ W) → W = ⊥ ∨ W = ⊤) := by
  dsimp only
  have hc : b65r_centralizer (-1 : Matrix (Fin 1) (Fin 1) ℂ) = ⊤ := by
    ext X
    simp [b65r_centralizer]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [List.ofFn_succ]
  · intro h
    have hv := congrArg (fun u : (Matrix (Fin 1) (Fin 1) ℂ)ˣ ↦ u.val 0 0) h
    norm_num at hv
  · have hf : Module.finrank ℂ (b65r_centralizer (-1 : Matrix (Fin 1) (Fin 1) ℂ)) = 1 := by
      rw [hc, finrank_top]
      change Module.finrank ℂ (Fin 1 → Fin 1 → ℂ) = 1
      rw [Module.finrank_pi_fintype]
      simp
    change (2 - (2 : ℤ)) * (1 : ℤ)^2 +
      ∑ _i : Fin 2, (Module.finrank ℂ (b65r_centralizer (-1 : Matrix (Fin 1) (Fin 1) ℂ)) : ℤ) = 2
    simp [hf]
  · intro W _
    let : IsSimpleOrder (Submodule ℂ (Fin 1 → ℂ)) :=
      is_simple_module_of_finrank_eq_one (K := ℂ) (by simp)
    exact eq_bot_or_eq_top W

end HodgeLean.Foundations.Program
