import HodgeLean.Foundations.AnalyticDivisorAlgebraic6
import HodgeLean.Foundations.AnalyticSubset

/-! # Concrete inputs for analytic dimension

Coordinate germs and polynomial analytic-set witnesses.
HC no distance; AV milestone no distance.
-/

noncomputable section
open Set Filter Topology Polynomial
open HodgeLean.Foundations.AnalyticDivisorAlgebraic6
namespace HodgeLean.Foundations

/-- The last coordinate at the origin.
Source: Gunning--Rossi, II.B, coordinate germs. -/
def adim_coordinate (n : ℕ) : AnalyticGerm (n + 1) :=
  ⟨Germ.ofFun (fun z ↦ z (Fin.last n)), fun z ↦ z (Fin.last n),
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin (n + 1) ↦ ℂ)
      (Fin.last n)).analyticAt 0, rfl⟩

example : analyticGermValue 1 (adim_coordinate 0) = 0 := rfl

/-- The coordinate is regular along its own axis.
Source: Gunning--Rossi, II.B, definition of regularity in the last variable. -/
theorem adim_coordinate_regular (n : ℕ) : IsRegularInLast (adim_coordinate n) := by
  refine ⟨fun z ↦ z (Fin.last n), ?_, rfl, ?_⟩
  · exact (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin (n + 1) ↦ ℂ)
      (Fin.last n)).analyticAt 0
  · simp only [Pi.single_eq_same]
    change analyticOrderAt (id : ℂ → ℂ) 0 ≠ ⊤
    rw [analyticOrderAt_id]
    exact ENat.one_ne_top

/-- The coordinate vanishes at the origin and is not a unit.
Source: Gunning--Rossi, II.B, units of the analytic local ring. -/
theorem adim_coordinate_nonunit (n : ℕ) : ¬ IsUnit (adim_coordinate n) := by
  rw [analyticGerm_isUnit_iff]
  change ¬ ((adim_coordinate n).1.value ≠ 0)
  change ¬ ((Germ.ofFun (fun z : Fin (n + 1) → ℂ ↦ z (Fin.last n))).value ≠ 0)
  simp only [Germ.value_ofFun, Pi.zero_apply, ne_eq, not_not]

/-- Global finite holomorphic equations give a closed analytic set in affine space.
Source: Schnell, *Complex Manifolds*, Definition 3.2. -/
theorem adim_equations_analytic (n m : ℕ) (f : Fin m → (Fin n → ℂ) → ℂ)
    (hf : ∀ i, AnalyticOnNhd ℂ (f i) univ) :
    IsClosedAnalytic (Fin n → ℂ) {z : Fin n → ℂ | ∀ i, f i z = 0} := by
  refine ⟨?_, fun x _ ↦ ⟨univ, isOpen_univ, mem_univ _, by simp,
    m, f, hf, ?_⟩⟩
  · have he : {z : Fin n → ℂ | ∀ i, f i z = 0} = ⋂ i, {z | f i z = 0} := by ext; simp
    rw [he]
    exact isClosed_iInter fun i ↦ isClosed_eq
      (continuousOn_univ.mp (hf i).continuousOn) continuous_const
  · intro z _
    simp

/-- The point, line, cusp, and mixed-dimensional union all have explicit polynomial equations.
Source: Chirka, *Complex Analytic Sets*, §§2–3, elementary analytic-set examples. -/
example : IsClosedAnalytic (Fin 1 → ℂ) {z : Fin 1 → ℂ | z 0 = 0} := by
  simpa using adim_equations_analytic 1 1 (fun _ z ↦ z 0)
    (fun _ ↦ (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 1 ↦ ℂ) 0).analyticOnNhd _)

example : IsClosedAnalytic (Fin 2 → ℂ) {z : Fin 2 → ℂ | z 1 = 0} := by
  simpa using adim_equations_analytic 2 1 (fun _ z ↦ z 1)
    (fun _ ↦ (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 2 ↦ ℂ) 1).analyticOnNhd _)

example : IsClosedAnalytic (Fin 2 → ℂ) {z : Fin 2 → ℂ | z 1 ^ 2 = z 0 ^ 3} := by
  have h0 := (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 2 ↦ ℂ) 0).analyticOnNhd univ
  have h1 := (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 2 ↦ ℂ) 1).analyticOnNhd univ
  have hh := adim_equations_analytic 2 1
    (fun _ z ↦ z 1 ^ 2 - z 0 ^ 3) (fun _ ↦ (h1.pow 2).sub (h0.pow 3))
  convert hh using 1
  ext z
  simp only [Set.mem_ofPred_eq, Fin.forall_fin_one, sub_eq_zero]

example : IsClosedAnalytic (Fin 3 → ℂ) {z : Fin 3 → ℂ | z 2 = 0 ∨ (z 0 = 0 ∧ z 1 = 0)} := by
  have h (i : Fin 3) : IsClosedAnalytic (Fin 3 → ℂ) {z : Fin 3 → ℂ | z i = 0} := by
    simpa using adim_equations_analytic 3 1 (fun _ z ↦ z i)
      (fun _ ↦ (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 3 ↦ ℂ) i).analyticOnNhd _)
  exact (h 2).union ((h 0).inter (h 1))

example : IsClosedAnalytic (Fin 2 → ℂ) (∅ : Set (Fin 2 → ℂ)) := isClosedAnalytic_empty

end HodgeLean.Foundations
