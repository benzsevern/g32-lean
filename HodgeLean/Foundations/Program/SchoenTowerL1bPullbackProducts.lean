import HodgeLean.Foundations.Program.SchoenTowerL1bPullbackEquations
import HodgeLean.Foundations.Program.SchoenTowerL1bWeightedProducts

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Actual scheme pullback preserves products of ideal sheaves. -/
theorem s2v_l1b_comap_mul
    {X Y : Scheme} (f : X ⟶ Y) (I J : Y.IdealSheafData) :
    (I * J).comap f = I.comap f * J.comap f := by
  have hlocal (x : X) : ∃ (U : X.affineOpens) (V : Y.affineOpens),
      x ∈ U.1 ∧ U.1 ≤ f ⁻¹ᵁ V.1 := by
    obtain ⟨V, hV, hxV, _⟩ := exists_isAffineOpen_mem_and_subset
      (show f x ∈ (⊤ : Y.Opens) from trivial)
    obtain ⟨U, hU, hxU, hUV⟩ := exists_isAffineOpen_mem_and_subset
      (show x ∈ f ⁻¹ᵁ V from hxV)
    exact ⟨⟨U, hU⟩, ⟨V, hV⟩, hxU, hUV⟩
  choose U V hxU hUV using hlocal
  have hcover : ⨆ x, (U x).1 = ⊤ := by
    apply top_unique
    intro x _
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hxU x⟩
  apply Scheme.IdealSheafData.ext_of_iSup_eq_top U hcover
  intro x
  change ((I * J).comap f).ideal (U x) =
    (I.comap f).ideal (U x) * (J.comap f).ideal (U x)
  rw [s2v_l1b_pullback_ideal_sections f (I * J) (U x) (V x) (hUV x),
    s2v_l1b_pullback_ideal_sections f I (U x) (V x) (hUV x),
    s2v_l1b_pullback_ideal_sections f J (U x) (V x) (hUV x)]
  exact Ideal.map_mul _ _ _

/-- Powers of ideal sheaves pull back along the actual scheme map. -/
theorem s2v_l1b_comap_pow
    {X Y : Scheme} (f : X ⟶ Y) (I : Y.IdealSheafData) (n : ℕ) :
    (I ^ n).comap f = (I.comap f) ^ n := by
  induction n with
  | zero =>
    simp only [pow_zero, Scheme.IdealSheafData.one_eq_top,
      Scheme.IdealSheafData.comap_top]
  | succ n ih => rw [pow_succ, s2v_l1b_comap_mul, ih, pow_succ]

/-- Finite ideal-sheaf products pull back along the actual scheme map. -/
theorem s2v_l1b_comap_prod
    {X Y : Scheme} (f : X ⟶ Y) {J : Type*} [Fintype J]
    (I : J → Y.IdealSheafData) :
    (∏ j, I j).comap f = ∏ j, (I j).comap f := by
  let pull : Y.IdealSheafData →* X.IdealSheafData :=
    { toFun := fun K => K.comap f
      map_one' := by
        simp only [Scheme.IdealSheafData.one_eq_top, Scheme.IdealSheafData.comap_top]
      map_mul' := s2v_l1b_comap_mul f }
  exact map_prod pull I Finset.univ

end HodgeLean.Foundations.Program
