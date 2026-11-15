import HodgeLean.Adapters.LatticeClassHQDefs
import HodgeLean.Foundations.AppellHumbertSections

/-! # Proofs for the lattice class in `HQ X 2`

The statements are frozen; this file proves them.

* Additivity: `spec_latticeClass_add` and linearity of `exteriorPower.map 2 _` and `cupWedgeMap 2`.
* Injectivity: `cupWedgeMap 2` is injective (`torusCohomology_cupProductOf`), the exterior square
  of the injective map `(abelianPeriodEquiv X).symm` is injective
  (`exteriorPower.map_injective_field`), and `spec_latticeClass_injective` concludes.
* Top power: `latticeClass E` is nondegenerate for `E = Im H` (the Gram argument of
  `spec_latticeClass_positive_nondegenerate`, redone for a form given directly, without a
  semicharacter), so its `g`-th wedge power is nonzero (`rank Λ = 2g` from `abelianLatticeBasis`).
  The exterior map commutes with wedge powers (`exteriorPower.coe_map`, `map_pow`), and
  `cupWedgeEquiv_wedgePow` identifies the transported wedge power with the cup power.
* Hard Lefschetz: `hardLefschetz_abelian_of_cupPow` applied to the top-power statement.
* Zero form: `latticeClass 0 = 0`; at `k = 0`, `L^g` sends the nonzero unit to
  `cupPow X μ 0 g = 0` (`cupPow_zero_of_pos`), so it is not injective.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open HodgeLean.RealDefs HodgeLean.Foundations HodgeLean.Foundations.AppellHumbert

namespace HodgeLean.Adapters

section Gram

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]

omit [FiniteDimensional ℂ V] in
/-- An integral form equal to `Im H` on a full lattice is alternating. -/
theorem latticeClassHQ_form_self (L : Submodule ℤ V) (H : HermitianForm (V := V))
    (E : L →+ L →+ ℤ) (hE : ∀ l m : L, (E l m : ℝ) = H.imaginary l m) (x : L) : E x x = 0 := by
  apply Int.cast_injective (α := ℝ)
  rw [hE, Int.cast_zero, HermitianForm.imaginary]
  exact Complex.conj_eq_iff_im.mp (H.conj_symm x x)

/-- For `E = Im H` with `H` positive definite on a full lattice, the Gram matrix of `E` on a
`ℤ`-basis has trivial left kernel over `ℚ` (as `gram_nondegenerate`, without a semicharacter). -/
theorem latticeClassHQ_gram_nondegenerate (L : Submodule ℤ V) [DiscreteTopology L]
    [IsZLattice ℝ L] [Module.Free ℤ L] (H : HermitianForm (V := V)) (hH : H.IsPositiveDefinite)
    (E : L →+ L →+ ℤ) (hE : ∀ l m : L, (E l m : ℝ) = H.imaginary l m)
    (q : Module.Free.ChooseBasisIndex ℤ L → ℚ)
    (hq : ∀ k, ∑ i, q i * (E (Module.Free.chooseBasis ℤ L i)
      (Module.Free.chooseBasis ℤ L k) : ℚ) = 0) :
    q = 0 := by
  set b := Module.Free.chooseBasis ℤ L
  let bR := b.ofZLatticeBasis ℝ L
  let B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ := LinearMap.mk₂ ℝ H.imaginary
    (fun x y z ↦ by simp [HermitianForm.imaginary, H.add_left])
    (fun r x y ↦ by simp [HermitianForm.imaginary, hermitian_real_smul_left])
    (fun x y z ↦ by simp [HermitianForm.imaginary, H.add_right])
    (fun r x y ↦ by simp [HermitianForm.imaginary, hermitian_real_smul_right])
  have hBapp : ∀ a c, B a c = H.imaginary a c := fun _ _ ↦ rfl
  set x : V := ∑ i, (q i : ℝ) • (b i : V)
  have hxk : ∀ k, B x (bR k) = 0 := by
    intro k
    simp only [x, bR, Module.Basis.ofZLatticeBasis_apply, map_sum, map_smul,
      LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, hBapp, ← hE]
    exact_mod_cast hq k
  have hB : B x = 0 := bR.ext fun k ↦ by rw [hxk k, LinearMap.zero_apply]
  have hx0 : x = 0 := spec_positive_imaginary_nondegenerate H hH x fun y ↦ by
    simpa [hBapp] using LinearMap.congr_fun hB y
  have hli := Fintype.linearIndependent_iff.mp bR.linearIndependent (fun i ↦ (q i : ℝ))
    (by simpa [bR] using hx0)
  funext i
  exact_mod_cast hli i

/-- For `E = Im H` with `H` positive definite on a full lattice, `latticeClass E` is a
nondegenerate 2-vector (as `spec_latticeClass_positive_nondegenerate`). -/
theorem latticeClassHQ_latticeClass_nondegenerate (L : Submodule ℤ V) [DiscreteTopology L]
    [IsZLattice ℝ L] [Module.Free ℤ L] [Module.Finite ℤ L] (H : HermitianForm (V := V))
    (hH : H.IsPositiveDefinite) (E : L →+ L →+ ℤ)
    (hE : ∀ l m : L, (E l m : ℝ) = H.imaginary l m) :
    Symplectic.IsNondegenerate (latticeClass E) := by
  have : FiniteDimensional ℚ (L →+ ℚ) := Module.Finite.of_basis latticeDualBasisQ
  have hinj : Function.Injective (Symplectic.contract (latticeClass E)) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro ψ hψ
    have hq := latticeClassHQ_gram_nondegenerate L H hH E hE
      (fun i ↦ ψ (latticeDualBasis i)) fun k ↦ by
        rw [← contract_latticeClass_apply_of_alt _ (latticeClassHQ_form_self L H E hE), hψ]
        rfl
    exact latticeDualBasisQ.ext fun i ↦ by
      rw [latticeDualBasisQ_apply, LinearMap.zero_apply]
      exact congrFun hq i
  exact ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    Subspace.dual_finrank_eq).mp hinj⟩

end Gram

/-- The exterior map of a linear map carries wedge powers to wedge powers. -/
theorem latticeClassHQ_wedgePow_map {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] (f : V →ₗ[K] W) (ω : ⋀[K]^2 V) (g : ℕ) :
    Symplectic.wedgePow (exteriorPower.map 2 f ω) g =
      exteriorPower.map (2 * g) f (Symplectic.wedgePow ω g) := by
  apply Subtype.ext
  rw [Symplectic.coe_wedgePow, exteriorPower.coe_map, exteriorPower.coe_map,
    Symplectic.coe_wedgePow, map_pow]

variable (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left]
  [Smooth X.hom] [IsProjective X.hom]

theorem spec_latticeClassHQ_add_aux
    (E₁ E₂ : abelianPeriodLattice X →+ abelianPeriodLattice X →+ ℤ) :
    latticeClassHQ X (E₁ + E₂) = latticeClassHQ X E₁ + latticeClassHQ X E₂ := by
  simp only [latticeClassHQ, spec_latticeClass_add, map_add]

theorem spec_latticeClassHQ_injective_aux
    (E₁ E₂ : abelianPeriodLattice X →+ abelianPeriodLattice X →+ ℤ)
    (h₁ : ∀ x, E₁ x x = 0) (h₂ : ∀ x, E₂ x x = 0)
    (h : latticeClassHQ X E₁ = latticeClassHQ X E₂) : E₁ = E₂ :=
  spec_latticeClass_injective E₁ E₂ h₁ h₂
    (exteriorPower.map_injective_field (abelianPeriodEquiv X).symm.injective
      (((torusCohomology_cupProductOf X).bijective 2).1 h))

theorem spec_latticeClassHQ_cupPow_ne_zero_aux
    (H : HermitianForm (V := Fin (dim X.left) → ℂ)) (hH : H.IsPositiveDefinite)
    (E : abelianPeriodLattice X →+ abelianPeriodLattice X →+ ℤ)
    (hE : ∀ l m : abelianPeriodLattice X, (E l m : ℝ) = H.imaginary l m) :
    cupPow X (cupProductOf X) (latticeClassHQ X E) (dim X.left) ≠ 0 := by
  let : IsCommMonObj X := isCommMonObj_of_complexSelfProductIntegral X
    (complexSelfProductIntegral_of_isIntegral X)
  let := isZLattice_complexExponentialLattice X (dim X.left)
  set T := torusCohomology_cupProductOf X
  have hnd := latticeClassHQ_latticeClass_nondegenerate (abelianPeriodLattice X) H hH E hE
  have : FiniteDimensional ℚ (abelianPeriodLattice X →+ ℚ) :=
    Module.Finite.of_basis latticeDualBasisQ
  have hrank : Module.finrank ℚ (abelianPeriodLattice X →+ ℚ) = 2 * dim X.left := by
    rw [Module.finrank_eq_card_basis latticeDualBasisQ, ← Module.finrank_eq_card_chooseBasisIndex,
      Module.finrank_eq_card_basis (abelianLatticeBasis X), Fintype.card_fin]
  have hw := Symplectic.wedgePow_ne_zero_of_isNondegenerate hnd hrank
  have hsymm : (T.cupWedgeEquiv 2).symm (latticeClassHQ X E) =
      exteriorPower.map 2 (abelianPeriodEquiv X).symm.toLinearMap (latticeClass E) :=
    (T.cupWedgeEquiv 2).symm_apply_apply _
  rw [← cupWedgeEquiv_wedgePow X T, hsymm, latticeClassHQ_wedgePow_map]
  intro h0
  apply hw
  apply exteriorPower.map_injective_field (abelianPeriodEquiv X).symm.injective
  rw [map_zero]
  exact (T.cupWedgeEquiv _).injective (h0.trans (map_zero _).symm)

theorem spec_latticeClassHQ_hardLefschetz_aux
    (H : HermitianForm (V := Fin (dim X.left) → ℂ)) (hH : H.IsPositiveDefinite)
    (E : abelianPeriodLattice X →+ abelianPeriodLattice X →+ ℤ)
    (hE : ∀ l m : abelianPeriodLattice X, (E l m : ℝ) = H.imaginary l m) :
    HardLefschetz X (cupProductOf X) (latticeClassHQ X E) :=
  hardLefschetz_abelian_of_cupPow X (spec_latticeClassHQ_cupPow_ne_zero_aux X H hH E hE)

theorem spec_latticeClassHQ_zero_falsification_aux (hg : 0 < dim X.left) :
    latticeClassHQ X 0 = 0 ∧ ¬ HardLefschetz X (cupProductOf X) (latticeClassHQ X 0) := by
  have h0 : latticeClassHQ X 0 = 0 := by simp [latticeClassHQ, latticeClass]
  refine ⟨h0, fun hL => ?_⟩
  rw [h0] at hL
  have hinj := (hL.bijective (k := 0) (m := 2 * dim X.left) (Nat.zero_le _) (by omega)).1
  have hc : cupPow X (cupProductOf X) 0 (dim X.left) = 0 :=
    cupPow_zero_of_pos X (cupProductOf X) hg
  exact (cupProductOf X).unitClass_ne_zero
    (hinj (a₁ := unitClass X) (a₂ := 0) (hc.trans (map_zero _).symm))

end HodgeLean.Adapters
