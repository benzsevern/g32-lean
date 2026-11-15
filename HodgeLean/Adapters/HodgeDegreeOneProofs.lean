import HodgeLean.Foundations.ComplexSheafSingular

/-! # Proof obligations for the degree-one Hodge decomposition specification

One obligation per statement of `HodgeLean.Adapters.HodgeDegreeOne`, all proved; two parallel provers
wrote them (statements 1-3 and 4-7).

* The degree-one pieces: `hodgePiece_eq_bot_of_lt` off `(1, 0)` and `(0, 1)`, and
  `hodgeFiltration_eq_top_of_nonpos` for `F^0 = ⊤` on them.
* Equal dimensions of `F^p` and `conj F^p`: `deRhamConjSemilinear X n` is a bijection
  (`deRhamConj_deRhamConj`) carrying `conj F^p` onto `F^p`, and `rank_eq_of_equiv_equiv` with
  `starRingEnd ℂ`.
* The linear algebra: `F.comap σ = F.map σ` for an involution, so both have dimension `g`;
  `Submodule.finrank_sup_add_finrank_inf_eq` and `Submodule.isCompl_iff_disjoint`.
* The abelian statements: `spec_bettiDeRhamIso_abelian` with
  `spec_bettiDeRhamIso_iff_finrank_abelian` at `n = 1` gives `finrank H_dR^1 = 2g`;
  `cohomologyHodgePiece_eq_map` transports dimensions to `ℂ ⊗[ℚ] HQ X 1`. -/

noncomputable section
open CategoryTheory AlgebraicGeometry ComplexPoint TopologicalSpace
open HodgeLean.RealDefs
open scoped TensorProduct

namespace HodgeLean.Adapters

theorem spec_deRhamHodgePiece_one_aux (X : Over (Spec ↧ℂ)) [IsIntegral X.left]
    [Smooth X.hom] (pq : ℤ × ℤ) :
    deRhamHodgePiece X 1 pq =
      if pq = (1, 0) then F^1 H_dR^((1 : ℕ) : ℤ)(X)
      else if pq = (0, 1) then conjHodgeFiltrationComplexSubmodule X 1 ((1 : ℕ) : ℤ)
      else ⊥ := by
  obtain ⟨p, q⟩ := pq
  unfold deRhamHodgePiece
  by_cases h : p + q = ((1 : ℕ) : ℤ)
  · by_cases hp : p = 1
    · have hq : q = 0 := by lia
      subst hp hq
      simp only [Nat.cast_one, add_zero, ↓reduceIte, hodgePiece]
      refine inf_eq_left.mpr fun α _ => ?_
      refine (mem_conjHodgeFiltrationComplexSubmodule X α).mpr ?_
      rw [hodgeFiltration_eq_top_of_nonpos X le_rfl]
      exact Submodule.mem_top
    · by_cases hp0 : p = 0
      · have hq : q = 1 := by lia
        subst hp0 hq
        simp only [Nat.cast_one, zero_add, ↓reduceIte, hodgePiece, Prod.mk.injEq,
          zero_ne_one, false_and]
        refine inf_eq_right.mpr fun α _ => ?_
        rw [hodgeFiltration_eq_top_of_nonpos X le_rfl]
        exact Submodule.mem_top
      · have hne : (p, q) ≠ ((1 : ℤ), (0 : ℤ)) := fun he => hp (Prod.mk.inj he).1
        have hne' : (p, q) ≠ ((0 : ℤ), (1 : ℤ)) := fun he => hp0 (Prod.mk.inj he).1
        simp only [h, hne, hne', ↓reduceIte]
        exact hodgePiece_eq_bot_of_lt X (by lia)
  · have hne : (p, q) ≠ ((1 : ℤ), (0 : ℤ)) := fun he => by
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
      exact h (by simp)
    have hne' : (p, q) ≠ ((0 : ℤ), (1 : ℤ)) := fun he => by
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
      exact h (by simp)
    simp only [h, hne, hne', ↓reduceIte]

/-- A conjugate-linear involution preserves the complex dimension of a subspace: it maps
`F.comap σ` bijectively onto `F`. -/
theorem finrank_comap_of_involutive {V : Type*} [AddCommGroup V] [Module ℂ V]
    (σ : V →ₛₗ[starRingEnd ℂ] V) (hσ : Function.Involutive σ) (F : Submodule ℂ V) :
    Module.finrank ℂ (F.comap σ) = Module.finrank ℂ F := by
  let e : F.comap σ ≃+ F :=
    { toFun := fun x => ⟨σ (x : V), x.2⟩
      invFun := fun y => ⟨σ (y : V), by
        change σ (σ (y : V)) ∈ F
        rw [hσ]
        exact y.2⟩
      left_inv := fun x => Subtype.ext (hσ (x : V))
      right_inv := fun y => Subtype.ext (hσ (y : V))
      map_add' := fun x y => Subtype.ext (map_add σ (x : V) y) }
  unfold Module.finrank
  congr 1
  exact rank_eq_of_equiv_equiv (starRingEnd ℂ) e Complex.conjAe.toRingEquiv.bijective
    (fun c x => Subtype.ext (σ.map_smulₛₗ c (x : V)))

theorem spec_finrank_conjHodgeFiltration_aux (X : Over (Spec ↧ℂ)) [IsIntegral X.left]
    [Smooth X.hom] (p n : ℤ) :
    Module.finrank ℂ (conjHodgeFiltrationComplexSubmodule X p n) =
      Module.finrank ℂ (F^p H_dR^n(X)) := by
  exact finrank_comap_of_involutive (deRhamConjSemilinear X n)
    (fun α => deRhamConj_deRhamConj X n α) _

theorem spec_isCompl_comap_of_finrank_of_disjoint_aux {V : Type*} [AddCommGroup V]
    [Module ℂ V] [FiniteDimensional ℂ V] (σ : V →ₛₗ[starRingEnd ℂ] V)
    (hσ : Function.Involutive σ) (F : Submodule ℂ V) {g : ℕ}
    (hV : Module.finrank ℂ V = 2 * g) (hF : Module.finrank ℂ F = g)
    (hdisj : Disjoint F (F.comap σ)) :
    IsCompl F (F.comap σ) := by
  refine (Submodule.isCompl_iff_disjoint F (F.comap σ) ?_).mpr hdisj
  rw [finrank_comap_of_involutive σ hσ F, hV, hF]
  lia

/-- A family of submodules that is `⊥` off two distinct indices `i` and `j` is an internal direct
sum exactly when its entries at `i` and `j` are complements. -/
theorem isInternal_ite_pair_iff {ι M : Type*} [DecidableEq ι] [AddCommGroup M] [Module ℂ M]
    {i j : ι} (hij : i ≠ j) (A B : Submodule ℂ M) :
    DirectSum.IsInternal (fun k => if k = i then A else if k = j then B else ⊥) ↔
      IsCompl A B := by
  rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]
  have hji : j ≠ i := hij.symm
  have hsup : (⨆ k, if k = i then A else if k = j then B else ⊥) = A ⊔ B := by
    refine le_antisymm (iSup_le fun k => ?_) (sup_le (le_iSup_of_le i ?_) (le_iSup_of_le j ?_))
    · split_ifs
      · exact le_sup_left
      · exact le_sup_right
      · exact bot_le
    · simp only [↓reduceIte, le_refl]
    · simp only [hji, ↓reduceIte, le_refl]
  rw [hsup, isCompl_iff, disjoint_iff, codisjoint_iff]
  constructor
  · rintro ⟨hind, htop⟩
    have h := hind.pairwiseDisjoint hij
    simp only [Function.onFun, hji, ↓reduceIte] at h
    exact ⟨disjoint_iff.mp h, htop⟩
  · rintro ⟨hdisj, htop⟩
    refine ⟨fun k => ?_, htop⟩
    by_cases hki : k = i
    · subst hki
      simp only [↓reduceIte]
      refine (disjoint_iff.mpr hdisj).mono_right (iSup₂_le fun l hl => ?_)
      simp only [hl, ↓reduceIte]
      split_ifs
      · exact le_rfl
      · exact bot_le
    · by_cases hkj : k = j
      · subst hkj
        simp only [hki, ↓reduceIte]
        refine (disjoint_iff.mpr hdisj).symm.mono_right (iSup₂_le fun l hl => ?_)
        simp only [hl, ↓reduceIte]
        split_ifs
        · exact le_rfl
        · exact bot_le
      · simp only [hki, hkj, ↓reduceIte]
        exact disjoint_bot_left

theorem spec_deRhamHodgePiece_one_isInternal_iff_aux (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] :
    DirectSum.IsInternal (deRhamHodgePiece X 1) ↔
      IsCompl (F^1 H_dR^((1 : ℕ) : ℤ)(X))
        (conjHodgeFiltrationComplexSubmodule X 1 ((1 : ℕ) : ℤ)) := by
  rw [show deRhamHodgePiece X 1 = _ from funext (spec_deRhamHodgePiece_one_aux X)]
  exact isInternal_ite_pair_iff (by decide) _ _

theorem spec_deRhamHodgePiece_one_isInternal_of_finrank_aux (X : Over (Spec ↧ℂ)) [GrpObj X]
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (hF : Module.finrank ℂ (F^1 H_dR^((1 : ℕ) : ℤ)(X)) = dim X.left)
    (hdisj : Disjoint (F^1 H_dR^((1 : ℕ) : ℤ)(X))
      (conjHodgeFiltrationComplexSubmodule X 1 ((1 : ℕ) : ℤ))) :
    DirectSum.IsInternal (deRhamHodgePiece X 1) := by
  obtain ⟨hfin, hdim⟩ :=
    (spec_bettiDeRhamIso_iff_finrank_abelian X).mp (HodgeLean.Foundations.spec_bettiDeRhamIso_abelian X) 1
  rw [Nat.choose_one_right] at hdim
  refine (spec_deRhamHodgePiece_one_isInternal_iff_aux X).mpr ?_
  exact spec_isCompl_comap_of_finrank_of_disjoint_aux (deRhamConjSemilinear X 1)
    (deRhamConj_deRhamConj X 1) _ hdim hF hdisj

theorem spec_finrank_hodgeFiltration_one_of_isInternal_aux (X : Over (Spec ↧ℂ)) [GrpObj X]
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (h : DirectSum.IsInternal (deRhamHodgePiece X 1)) :
    Module.finrank ℂ (F^1 H_dR^((1 : ℕ) : ℤ)(X)) = dim X.left ∧
      Module.finrank ℂ (conjHodgeFiltrationComplexSubmodule X 1 ((1 : ℕ) : ℤ)) = dim X.left := by
  obtain ⟨hfin, hdim⟩ :=
    (spec_bettiDeRhamIso_iff_finrank_abelian X).mp (HodgeLean.Foundations.spec_bettiDeRhamIso_abelian X) 1
  rw [Nat.choose_one_right] at hdim
  have hadd := Submodule.finrank_add_eq_of_isCompl
    ((spec_deRhamHodgePiece_one_isInternal_iff_aux X).mp h)
  rw [spec_finrank_conjHodgeFiltration_aux X 1 ((1 : ℕ) : ℤ), hdim] at hadd
  rw [spec_finrank_conjHodgeFiltration_aux X 1 ((1 : ℕ) : ℤ)]
  constructor <;> lia

theorem spec_finrank_cohomologyHodgePiece_one_aux (X : Over (Spec ↧ℂ)) [GrpObj X]
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (hD : HodgeDecomposition X) :
    Module.finrank ℂ (cohomologyHodgePiece X 1 (1, 0)) = dim X.left ∧
      Module.finrank ℂ (cohomologyHodgePiece X 1 (0, 1)) = dim X.left := by
  have hB := HodgeLean.Foundations.spec_bettiDeRhamIso_abelian X
  obtain ⟨h1, h2⟩ := spec_finrank_hodgeFiltration_one_of_isInternal_aux X (hD.isInternal 1)
  rw [cohomologyHodgePiece_eq_map hB 1]
  simp only
  have e10 := spec_deRhamHodgePiece_one_aux X (1, 0)
  have e01 := spec_deRhamHodgePiece_one_aux X (0, 1)
  simp only [Prod.mk.injEq, one_ne_zero, zero_ne_one, and_self, ↓reduceIte] at e10 e01
  rw [LinearEquiv.finrank_map_eq, LinearEquiv.finrank_map_eq, e10, e01]
  exact ⟨h1, h2⟩

end HodgeLean.Adapters
