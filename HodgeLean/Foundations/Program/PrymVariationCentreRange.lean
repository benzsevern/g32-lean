import HodgeLean.Foundations.Program.PrymVariationCentreHomology

noncomputable section
open CategoryTheory AlgebraicTopology.Singular HodgeLean.Papers
namespace HodgeLean.Foundations.Program

def b63d_homologyAct (C : Type) [TopologicalSpace C] [MulAction b4b_Group C]
    (hC : ∀ g : b4b_Group, Continuous (fun x : C ↦ g • x)) (g : b4b_Group) :
    b6m_H1 C →ₗ[ℤ] b6m_H1 C :=
  homologyMap ℤ 1 (TopCat.ofHom ⟨fun x : C ↦ g • x, hC g⟩)

theorem b63d_homologyAct_mul (C : Type) [TopologicalSpace C] [MulAction b4b_Group C]
    (hC : ∀ g : b4b_Group, Continuous (fun x : C ↦ g • x)) (g h : b4b_Group) (x : b6m_H1 C) :
    b63d_homologyAct C hC g (b63d_homologyAct C hC h x) =
      b63d_homologyAct C hC (g * h) x := by
  rw [← LinearMap.comp_apply]
  simp only [b63d_homologyAct]
  rw [← homologyMap_comp]
  congr 3
  ext q
  exact (mul_smul g h q).symm

theorem b63d_centre_projector_commute (C : Type) [TopologicalSpace C]
    [MulAction b4b_Group C]
    (hC : ∀ g : b4b_Group, Continuous (fun x : C ↦ g • x)) (x : b6m_H1 C) :
    (∑ g : b4b_Group, if b4b_toMatrix g = g32h_omega • (1 : Matrix (Fin 4) (Fin 4) ℂ)
      then b63d_homologyAct C hC g else 0)
        ((∑ h : b4b_Group, b4b_projectorCoeff h • b63d_homologyAct C hC h) x) =
    (∑ h : b4b_Group, b4b_projectorCoeff h • b63d_homologyAct C hC h)
      ((∑ g : b4b_Group, if b4b_toMatrix g = g32h_omega •
        (1 : Matrix (Fin 4) (Fin 4) ℂ) then b63d_homologyAct C hC g else 0) x) := by
  classical
  simp only [LinearMap.sum_apply, map_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro g hg
  split_ifs with hz
  · apply Finset.sum_congr rfl
    intro h hh
    calc
      b63d_homologyAct C hC g
          ((b4b_projectorCoeff h • b63d_homologyAct C hC h) x) =
          b4b_projectorCoeff h •
            b63d_homologyAct C hC g (b63d_homologyAct C hC h x) := by
              change b63d_homologyAct C hC g
                (b4b_projectorCoeff h • b63d_homologyAct C hC h x) = _
              rw [map_zsmul]
      _ = b4b_projectorCoeff h •
          b63d_homologyAct C hC h (b63d_homologyAct C hC g x) := by
            rw [b63d_homologyAct_mul, b63d_homologyAct_mul,
              b63d_scalar_commutes g h hz]
      _ = (b4b_projectorCoeff h • b63d_homologyAct C hC h)
          (b63d_homologyAct C hC g x) := rfl
  · simp only [map_zero, LinearMap.zero_apply, Finset.sum_const_zero]

theorem b63d_centre_range_helper (b : Fin 10 → ℂ) (C : Type) [TopologicalSpace C]
    [MulAction b4b_Group C]
    (hC : ∀ g : b4b_Group, Continuous (fun x : C ↦ g • x))
    (V : Set (Fin 10 → ℂ)) (hV : V ⊆ b6t_polydisc b) (t : V) :
    ∃ Z : b63l_parameterLattice b C hC V hV t →ₗ[ℤ]
        b63l_parameterLattice b C hC V hV t,
      ∀ x, (Z x).val = b63d_centre b C hC V hV t x.val := by
  let hD : ∀ g : b4b_Group, Continuous (fun x : b63l_parameterFibre b C V hV t ↦ g • x) :=
    fun g ↦ (b6m_deck b b4b_Group C hC ⟨t.val, hV t.property⟩ g).continuous
  let A : b6m_H1 (b63l_parameterFibre b C V hV t) →ₗ[ℤ] b6m_H1 (b63l_parameterFibre b C V hV t) :=
    ∑ g : b4b_Group, if b4b_toMatrix g = g32h_omega •
      (1 : Matrix (Fin 4) (Fin 4) ℂ) then b63d_homologyAct (b63l_parameterFibre b C V hV t) hD g else 0
  let P : b6m_H1 (b63l_parameterFibre b C V hV t) →ₗ[ℤ] b6m_H1 (b63l_parameterFibre b C V hV t) :=
    ∑ g : b4b_Group, b4b_projectorCoeff g • b63d_homologyAct (b63l_parameterFibre b C V hV t) hD g
  have hcomm (x : b6m_H1 (b63l_parameterFibre b C V hV t)) : A (P x) = P (A x) := by
    exact b63d_centre_projector_commute (b63l_parameterFibre b C V hV t) hD x
  have hA (x : b6m_H1 (b63l_parameterFibre b C V hV t))
      (hx : x ∈ b63l_saturation (LinearMap.range P)) :
      A x ∈ b63l_saturation (LinearMap.range P) := by
    rcases hx with ⟨n, hn, y, hy⟩
    refine ⟨n, hn, A y, ?_⟩
    rw [← hcomm, hy]
    exact A.map_smul n x
  let Za : b63l_parameterLattice b C hC V hV t →+
      b63l_parameterLattice b C hC V hV t := {
    toFun := fun x ↦ ⟨A x.val, hA x.val x.property⟩
    map_zero' := Subtype.ext (map_zero A)
    map_add' := by
      intro x y
      apply Subtype.ext
      exact map_add A x.val y.val }
  let Z := Za.toIntLinearMap
  refine ⟨Z, fun x ↦ ?_⟩
  simp only [Z, Za]
  change A x.val = b63d_centre b C hC V hV t x.val
  simp only [A, b63d_centre, b63d_homologyAct, LinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro g hg
  split_ifs <;> rfl

end HodgeLean.Foundations.Program
