import HodgeLean.Foundations.DivisorClassHodgeTorus
import HodgeLean.Foundations.SeveralVariableDbarDefs

/-! # Dolbeault on the flat torus `ℂ^n / L` in degree `(0,1)` (DC1-c)

Transport of `dct_torus_solve` along a `ℤ`-basis of a full lattice `L ⊆ ℂ^n`: the real
coordinates of that basis identify `L`-periodic functions on `ℂ^n` with `ℤ^ι`-periodic functions
on `ι → ℝ`, and `dbar_coord n j` with the constant-coefficient operator `dct_P` along the
coordinates of `e_j` and `i e_j`.

Source: BL §1.4; Mumford, *Abelian Varieties*, Ch. I §1.
-/

noncomputable section
open Set Filter Topology
open scoped ContDiff

namespace HodgeLean.Foundations

variable {n : ℕ} (L : Submodule ℤ (Fin n → ℂ)) [DiscreteTopology L] [IsZLattice ℝ L]

/-- The real coordinates along a `ℤ`-basis of `L`. -/
def dct_coord : (Fin n → ℂ) ≃L[ℝ] (Module.Free.ChooseBasisIndex ℤ L → ℝ) :=
  ((Module.Free.chooseBasis ℤ L).ofZLatticeBasis ℝ L).equivFunL

theorem dct_coord_symm_apply (y : Module.Free.ChooseBasisIndex ℤ L → ℝ) :
    (dct_coord L).symm y = ∑ i, y i • ((Module.Free.chooseBasis ℤ L i : L) : Fin n → ℂ) := by
  change ((Module.Free.chooseBasis ℤ L).ofZLatticeBasis ℝ L).equivFun.symm y = _
  rw [Module.Basis.equivFun_symm_apply]
  simp

theorem dct_coord_symm_int (k : Module.Free.ChooseBasisIndex ℤ L → ℤ) :
    (dct_coord L).symm (fun i ↦ (k i : ℝ)) =
      ((∑ i, k i • Module.Free.chooseBasis ℤ L i : L) : Fin n → ℂ) := by
  rw [dct_coord_symm_apply, Submodule.coe_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Submodule.coe_smul_of_tower, Int.cast_smul_eq_zsmul]

theorem dct_coord_lattice (l : L) :
    dct_coord L (l : Fin n → ℂ) = fun i ↦ ((Module.Free.chooseBasis ℤ L).repr l i : ℝ) := by
  funext i
  change ((Module.Free.chooseBasis ℤ L).ofZLatticeBasis ℝ L).equivFun l i = _
  rw [Module.Basis.equivFun_apply, Module.Basis.ofZLatticeBasis_repr_apply]

theorem dct_fderiv_comp_equiv {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (e : E ≃L[ℝ] F) (G : F → ℂ) (x v : E) :
    fderiv ℝ (G ∘ e) x v = fderiv ℝ G (e x) (e v) := by
  rw [e.comp_right_fderiv]
  rfl

/-- `dct_torus_solve` on `ℂ^n / L`. -/
theorem dct_lattice_dbar (w : Fin n → (Fin n → ℂ) → ℂ) (hw : ∀ j, ContDiff ℝ ∞ (w j))
    (hper : ∀ j (l : L) z, w j (z + l) = w j z)
    (hcompat : ∀ j k z, dbar_coord n k (w j) z = dbar_coord n j (w k) z) :
    ∃ (c : Fin n → ℂ) (ψ : (Fin n → ℂ) → ℂ), ContDiff ℝ ∞ ψ ∧
      (∀ (l : L) z, ψ (z + l) = ψ z) ∧ ∀ j z, w j z = c j + dbar_coord n j ψ z := by
  set T := dct_coord L with hT
  set u : Fin n → Module.Free.ChooseBasisIndex ℤ L → ℝ := fun j ↦ T (Pi.single j 1) with hu
  set u' : Fin n → Module.Free.ChooseBasisIndex ℤ L → ℝ := fun j ↦ T (Pi.single j Complex.I)
    with hu'
  set F : Fin n → (Module.Free.ChooseBasisIndex ℤ L → ℝ) → ℂ := fun j ↦ w j ∘ T.symm with hF
  have hP : ∀ (G : (Fin n → ℂ) → ℂ) j x,
      dct_P (u j) (u' j) (G ∘ T.symm) x = dbar_coord n j G (T.symm x) := by
    intro G j x
    simp only [dct_P, dbar_coord, dct_fderiv_comp_equiv, hu, hu',
      ContinuousLinearEquiv.symm_apply_apply]
  have hFs : ∀ j, ContDiff ℝ ∞ (F j) := fun j ↦ (hw j).comp T.symm.contDiff
  have hFp : ∀ j, dct_Periodic (F j) := by
    intro j k x
    simp only [hF, Function.comp_apply, map_add, hT, dct_coord_symm_int]
    exact hper j _ _
  have hFc : ∀ j k x, dct_P (u k) (u' k) (F j) x = dct_P (u j) (u' j) (F k) x := by
    intro j k x
    rw [hP, hP, hcompat]
  have hinj : ∀ ξ : Module.Free.ChooseBasisIndex ℤ L → ℝ,
      (∀ j, ∑ i, ξ i * u j i = 0 ∧ ∑ i, ξ i * u' j i = 0) → ξ = 0 := by
    intro ξ hξ
    let lam : (Fin n → ℂ) →ₗ[ℝ] ℝ :=
      (∑ i, ξ i • (LinearMap.proj i : (Module.Free.ChooseBasisIndex ℤ L → ℝ) →ₗ[ℝ] ℝ)).comp
        (T : (Fin n → ℂ) →ₗ[ℝ] Module.Free.ChooseBasisIndex ℤ L → ℝ)
    have hlam : ∀ z, lam z = ∑ i, ξ i * T z i := by
      intro z; simp [lam]
    have hz : ∀ z : Fin n → ℂ,
        z = ∑ j, ((z j).re • (Pi.single j (1 : ℂ) : Fin n → ℂ) +
          (z j).im • (Pi.single j Complex.I : Fin n → ℂ)) := by
      intro z
      funext m
      rw [Finset.sum_apply, Finset.sum_eq_single m]
      · simp only [Pi.add_apply, Pi.smul_apply, Pi.single_eq_same, Complex.real_smul, mul_one]
        exact (Complex.re_add_im (z m)).symm
      · intro b _ hb
        simp [Pi.single_eq_of_ne (Ne.symm hb)]
      · simp
    have h0 : ∀ z, lam z = 0 := by
      intro z
      rw [hz z, map_sum]
      refine Finset.sum_eq_zero fun j _ ↦ ?_
      rw [map_add, map_smul, map_smul, hlam, hlam, (hξ j).1, (hξ j).2, smul_zero, smul_zero,
        add_zero]
    funext i
    have := h0 (T.symm (Pi.single i 1))
    rw [hlam, ContinuousLinearEquiv.apply_symm_apply] at this
    simpa [Pi.single_apply] using this
  obtain ⟨c, ψ, hψs, hψp, hψ⟩ := dct_torus_solve u u' hinj F hFs hFp hFc
  refine ⟨c, ψ ∘ T, hψs.comp T.contDiff, fun l z ↦ ?_, fun j z ↦ ?_⟩
  · simp only [Function.comp_apply, map_add, hT, dct_coord_lattice]
    exact hψp _ _
  · have h1 := hψ j (T z)
    have h3 := hP (ψ ∘ T) j (T z)
    simp only [ContinuousLinearEquiv.symm_apply_apply] at h3
    have h4 : (ψ ∘ T) ∘ T.symm = ψ := by
      funext x; simp
    rw [h4] at h3
    rw [← h3]
    simpa [hF] using h1

end HodgeLean.Foundations
