import HodgeLean.Foundations.Program.MilneTensorGLPairTheorem
import HodgeLean.Foundations.Program.MilneTensorRetractGeneration

noncomputable section
open scoped TensorProduct
open HodgeLean.Foundations
namespace HodgeLean.Foundations.Program
variable {W : Type*} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]

def m1b_vectorDualMultiplicityAction (a b : ℕ) (g : LinearMap.GeneralLinearGroup ℂ W) :
    Module.End ℂ ((Fin a → W) × (Fin b → Module.Dual ℂ W)) :=
  (m1b_copies a (g : Module.End ℂ W)).prodMap
    (m1b_copies b ((g⁻¹ : LinearMap.GeneralLinearGroup ℂ W) : Module.End ℂ W).dualMap)

def m1b_vectorDualMultiplicityIn (a b : ℕ) :
    ((Fin a → W) × (Fin b → Module.Dual ℂ W)) →ₗ[ℂ]
      (Fin (a + b) → W × Module.Dual ℂ W) :=
    { toFun := fun v => Fin.addCases (fun j => (v.1 j, 0)) (fun j => (0, v.2 j))
      map_add' := by
        intro v w
        funext j
        refine Fin.addCases (fun j => ?_) (fun j => ?_) j
        · simp only [Pi.add_apply, Fin.addCases_left, Fin.addCases_right]
          change (v.1 j + w.1 j, (0 : Module.Dual ℂ W)) = (v.1 j + w.1 j, 0 + 0)
          rw [add_zero]
        · simp only [Pi.add_apply, Fin.addCases_left, Fin.addCases_right]
          change ((0 : W), v.2 j + w.2 j) = (0 + 0, v.2 j + w.2 j)
          rw [add_zero]
      map_smul' := by
        intro z v
        funext j
        refine Fin.addCases (fun j => ?_) (fun j => ?_) j
        · simp only [Pi.smul_apply, Fin.addCases_left, Fin.addCases_right, RingHom.id_apply]
          change (z • v.1 j, (0 : Module.Dual ℂ W)) = (z • v.1 j, z • (0 : Module.Dual ℂ W))
          rw [smul_zero]
        · simp only [Pi.smul_apply, Fin.addCases_left, Fin.addCases_right, RingHom.id_apply]
          change ((0 : W), z • v.2 j) = (z • (0 : W), z • v.2 j)
          rw [smul_zero] }

def m1b_vectorDualMultiplicityOut (a b : ℕ) :
    (Fin (a + b) → W × Module.Dual ℂ W) →ₗ[ℂ]
      ((Fin a → W) × (Fin b → Module.Dual ℂ W)) :=
    { toFun := fun v => (fun j => (v (Fin.castAdd b j)).1, fun j => (v (Fin.natAdd a j)).2)
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }

theorem m1b_vectorDualMultiplicity_split (a b : ℕ) : (m1b_vectorDualMultiplicityOut (W := W) a b).comp
    (m1b_vectorDualMultiplicityIn a b) = LinearMap.id := by
  let U := W × Module.Dual ℂ W
  apply LinearMap.ext
  intro v
  apply Prod.ext
  · funext j
    change (Fin.addCases (motive := fun _ => U) (fun j => (v.1 j, (0 : Module.Dual ℂ W)))
      (fun j => ((0 : W), v.2 j)) (Fin.castAdd b j)).1 = v.1 j
    rw [Fin.addCases_left]
  · funext j
    change (Fin.addCases (motive := fun _ => U) (fun j => (v.1 j, (0 : Module.Dual ℂ W)))
      (fun j => ((0 : W), v.2 j)) (Fin.natAdd a j)).2 = v.2 j
    rw [Fin.addCases_right]

theorem m1b_vectorDualMultiplicity_in_action (a b : ℕ) (g : LinearMap.GeneralLinearGroup ℂ W) :
    (m1b_copies (a + b) (m1b_vectorDualAction g)).comp (m1b_vectorDualMultiplicityIn a b) =
      (m1b_vectorDualMultiplicityIn a b).comp (m1b_vectorDualMultiplicityAction a b g) := by
  let U := W × Module.Dual ℂ W
  apply LinearMap.ext
  intro v
  funext j
  change m1b_vectorDualAction g
      (Fin.addCases (motive := fun _ => U) (fun j => (v.1 j, (0 : Module.Dual ℂ W)))
        (fun j => ((0 : W), v.2 j)) j) =
    Fin.addCases (motive := fun _ => U) (fun j => ((g : Module.End ℂ W) (v.1 j), (0 : Module.Dual ℂ W)))
      (fun j => ((0 : W),
        ((g⁻¹ : LinearMap.GeneralLinearGroup ℂ W) : Module.End ℂ W).dualMap (v.2 j))) j
  refine Fin.addCases (fun j => ?_) (fun j => ?_) j <;>
    simp only [Fin.addCases_left, Fin.addCases_right, m1b_vectorDualAction,
      LinearMap.prodMap_apply, map_zero]

theorem m1b_vectorDualMultiplicity_out_action (a b : ℕ) (g : LinearMap.GeneralLinearGroup ℂ W) :
    (m1b_vectorDualMultiplicityAction a b g).comp (m1b_vectorDualMultiplicityOut a b) =
      (m1b_vectorDualMultiplicityOut a b).comp (m1b_copies (a + b) (m1b_vectorDualAction g)) := by
  apply LinearMap.ext
  intro v
  apply Prod.ext <;> funext j <;> rfl

theorem m1b_vectorDualMultiplicity_generation (a b n : ℕ) :
    m1b_fixed (Set.range (m1b_vectorDualMultiplicityAction (W := W) a b)) n =
      m1b_products (m1b_fixed
        (Set.range (m1b_vectorDualMultiplicityAction (W := W) a b)) 2) n := by
  have hgen := m1b_vectorDual_copies_generation (W := W) (a + b) n
  rw [← Set.range_comp] at hgen
  exact m1b_generation_retract
    (G := LinearMap.GeneralLinearGroup ℂ W)
    (V := (Fin a → W) × (Fin b → Module.Dual ℂ W))
    (W := Fin (a + b) → W × Module.Dual ℂ W)
    (m1b_vectorDualMultiplicityAction a b)
    (fun g => m1b_copies (a + b) (m1b_vectorDualAction g)) (m1b_vectorDualMultiplicityIn a b) (m1b_vectorDualMultiplicityOut a b)
    (m1b_vectorDualMultiplicity_split a b)
    (m1b_vectorDualMultiplicity_in_action a b)
    (m1b_vectorDualMultiplicity_out_action a b) n hgen

theorem m1b_vectorDualMultiplicity_copies_generation (a b r n : ℕ) :
    m1b_fixed (m1b_copies r ''
      Set.range (m1b_vectorDualMultiplicityAction (W := W) a b)) n =
      m1b_products (m1b_fixed (m1b_copies r ''
        Set.range (m1b_vectorDualMultiplicityAction (W := W) a b)) 2) n :=
  m1b_copies_generation _ r n (m1b_vectorDualMultiplicity_generation a b n)

end HodgeLean.Foundations.Program
