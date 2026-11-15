import HodgeLean.Foundations.Program.FuchsianSystem

noncomputable section
open Set Filter
open scoped Topology
namespace HodgeLean.Foundations.Program

theorem b65r_transport_constant (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E] (A : ℂ → E →L[ℂ] E) (a : ℂ) :
    b65f_transport E A (fun _ ↦ a) = 1 := by
  have hp : b65f_polygon E A (fun _ ↦ a) = fun _ ↦ 1 := by
    funext N
    simp [b65f_polygon,b65f_segment_initial]
  unfold b65f_transport
  rw [hp]
  exact tendsto_const_nhds.limUnder_eq

theorem b65r_transport_eqOn (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E] (A : ℂ → E →L[ℂ] E) (γ δ : ℝ → ℂ)
    (h : EqOn γ δ (Icc (0 : ℝ) 1)) :
    b65f_transport E A γ = b65f_transport E A δ := by
  have hp : b65f_polygon E A γ = b65f_polygon E A δ := by
    funext N
    have hi (i : Fin (2^N)) :
        ((i.val : ℝ)/(2 : ℝ)^N) ∈ Icc (0 : ℝ) 1 ∧
        (((i.val : ℝ)+1)/(2 : ℝ)^N) ∈ Icc (0 : ℝ) 1 := by
      have hh : (i.val : ℝ)+1 ≤ (2 : ℝ)^N := by exact_mod_cast i.isLt
      constructor <;> constructor
      · positivity
      · apply (div_le_one (by positivity)).mpr; linarith
      · positivity
      · exact (div_le_one (by positivity)).mpr hh
    unfold b65f_polygon
    congr 3
    funext i
    rw [h (hi i).1,h (hi i).2]
  unfold b65f_transport
  rw [hp]

def b65r_pathUnit (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E] (U : Set ℂ) (hU : IsOpen U)
    (A : ℂ → E →L[ℂ] E) (hA : AnalyticOnNhd ℂ A U)
    {x y : U} (p : Path x y) : (E →L[ℂ] E)ˣ :=
  (b65f_path_convergence E U hU A hA x y p).2.unit

theorem b65r_pathUnit_val (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E] (U : Set ℂ) (hU : IsOpen U)
    (A : ℂ → E →L[ℂ] E) (hA : AnalyticOnNhd ℂ A U)
    {x y : U} (p : Path x y) :
    (b65r_pathUnit E U hU A hA p).val =
      b65f_transport E A (fun t ↦ (p.extend t).val) := IsUnit.unit_spec _

theorem b65r_pathUnit_trans (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E] (U : Set ℂ) (hU : IsOpen U)
    (A : ℂ → E →L[ℂ] E) (hA : AnalyticOnNhd ℂ A U)
    {x y z : U} (p : Path x y) (q : Path y z) :
    b65r_pathUnit E U hU A hA (p.trans q) =
      b65r_pathUnit E U hU A hA q*b65r_pathUnit E U hU A hA p := by
  apply Units.ext
  simpa only [Units.val_mul,b65r_pathUnit_val] using b65f_path_composition E U hU A hA x y z p q

theorem b65r_pathUnit_reverse (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E] (U : Set ℂ) (hU : IsOpen U)
    (A : ℂ → E →L[ℂ] E) (hA : AnalyticOnNhd ℂ A U)
    {x y : U} (p : Path x y) :
    b65r_pathUnit E U hU A hA p.symm = (b65r_pathUnit E U hU A hA p)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← b65r_pathUnit_trans]
  apply Units.ext
  rw [b65r_pathUnit_val]
  have h := b65f_homotopy_invariance E U hU A hA x x
    (p.trans p.symm) (Path.refl x) (Path.Homotopic.trans_symm p)
  simpa only [Path.refl_extend,ContinuousMap.const_apply,b65r_transport_constant,Units.val_one] using h

theorem b65r_stemmed_transport (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E] (U : Set ℂ) (hU : IsOpen U)
    (A : ℂ → E →L[ℂ] E) (hA : AnalyticOnNhd ℂ A U)
    {x y : U} (k : Path x y) (d : Path y y) (G : E →L[ℂ] E)
    (hc : ∃ C : (E →L[ℂ] E)ˣ,
      b65f_transport E A (fun t ↦ (d.extend t).val) = C.val*G*(C⁻¹).val) :
    ∃ C : (E →L[ℂ] E)ˣ,
      b65f_transport E A (fun t ↦ (((k.trans d).trans k.symm).extend t).val) =
        C.val*G*(C⁻¹).val := by
  obtain ⟨C,hC⟩ := hc
  let K := b65r_pathUnit E U hU A hA k
  refine ⟨K⁻¹*C,?_⟩
  rw [← b65r_pathUnit_val E U hU A hA ((k.trans d).trans k.symm),
    b65r_pathUnit_trans,b65r_pathUnit_trans,b65r_pathUnit_reverse]
  simp only [Units.val_mul]
  rw [b65r_pathUnit_val E U hU A hA d,hC]
  simp [K,mul_assoc]

end HodgeLean.Foundations.Program
