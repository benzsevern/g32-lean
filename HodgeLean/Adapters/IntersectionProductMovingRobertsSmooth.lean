import HodgeLean.Adapters.IntersectionProductMovingRobertsFamily

/-! # Differentials on the cone over a smooth projective variety

The rank condition of `a3s_movingFamily_of_rank` for a smooth `X`: at a relevant point of the
affine cone over `X ⊂ ℙᴺ`, the Kähler differentials have rank at most `dim X + 1`.
* A smooth domain of finite type over `ℂ` of dimension `m` has differentials of rank `m` at every
  point (`a3t_finrank_le_of_smooth`; locally standard smooth of relative dimension `m`), and this
  rank is unchanged by localization (`a3t_finrank_localization`).
* The affine charts `T_j = Γ(X ∩ D₊(x_j))` of a smooth `X` are smooth `ℂ`-algebras
  (`a3t_chart_smooth`), through the dehomogenization `θ_j`.
* Inverting `x_j` in the cone ring `A = ℂ[x]/I_X` gives `A_{x_j} = T_j[x_j, x_j⁻¹]`
  (`a3t_homog`, homogenization), so the differentials of `A_{x_j}` are those of `T_j` plus
  `dx_j`.

Source: Hartshorne, *Algebraic Geometry*, II, Theorem 8.15, Exercise 2.14 and Exercise 8.4;
Stacks Project, Tags 00TA and 00TT. HC no distance; AV milestone no distance.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial TensorProduct
open AlgebraicGeometry.ComplexProjectiveSpace HodgeLean.Foundations

namespace HodgeLean.Adapters

section Rank

/-- The fibre of the differentials is unchanged by a localization. -/
theorem a3t_finrank_localization {S S' K : Type} [CommRing S] [CommRing S'] [Field K]
    [Algebra ℂ S] [Algebra ℂ S'] [Algebra S S'] [IsScalarTower ℂ S S'] (M : Submonoid S)
    [IsLocalization M S'] [Algebra S K] [Algebra S' K] [IsScalarTower S S' K] :
    Module.finrank K (K ⊗[S] Ω[S⁄ℂ]) = Module.finrank K (K ⊗[S'] Ω[S'⁄ℂ]) := by
  have : Algebra.FormallyEtale S S' := Algebra.FormallyEtale.of_isLocalization M
  let e₁ : S' ⊗[S] Ω[S⁄ℂ] ≃ₗ[S'] Ω[S'⁄ℂ] :=
    KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale ℂ S S'
  let e₂ : K ⊗[S'] (S' ⊗[S] Ω[S⁄ℂ]) ≃ₗ[K] K ⊗[S] Ω[S⁄ℂ] :=
    TensorProduct.AlgebraTensorModule.cancelBaseChange S S' K K Ω[S⁄ℂ]
  let e₃ : K ⊗[S'] (S' ⊗[S] Ω[S⁄ℂ]) ≃ₗ[K] K ⊗[S'] Ω[S'⁄ℂ] :=
    TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl K K) e₁
  exact (e₂.symm.trans e₃).finrank_eq

/-- A smooth domain of finite type over `ℂ` of dimension `m` has differentials of rank `m` at every
point, in particular rank at most `m` after base change to any field. -/
theorem a3t_finrank_le_of_smooth {S K : Type} [CommRing S] [IsDomain S] [Algebra ℂ S]
    [Algebra.FiniteType ℂ S] [Algebra.Smooth ℂ S] (m : ℕ) (hm : ringKrullDim S = m)
    [Field K] [Algebra S K] : Module.finrank K (K ⊗[S] Ω[S⁄ℂ]) ≤ m := by
  set p := RingHom.ker (algebraMap S K)
  have hp : p.IsPrime := RingHom.ker_isPrime _
  have : Algebra.FinitePresentation ℂ S := Algebra.FinitePresentation.of_finiteType.1 inferInstance
  have : Algebra.IsSmoothAt ℂ p := by
    have : (⟨p, hp⟩ : PrimeSpectrum S) ∈ Algebra.smoothLocus ℂ S := by
      rw [Algebra.smoothLocus_eq_univ]; trivial
    exact this
  obtain ⟨g, hg, hstd⟩ := Algebra.IsSmoothAt.exists_notMem_isStandardSmooth ℂ p
  set Sg := Localization.Away g
  obtain ⟨ι, σ, _, _, ⟨P⟩⟩ := hstd.out
  have hrel : Algebra.IsStandardSmoothOfRelativeDimension P.dimension ℂ Sg :=
    ⟨⟨ι, σ, inferInstance, inferInstance, P, rfl⟩⟩
  have hg0 : g ≠ 0 := fun h => hg (h ▸ zero_mem p)
  have : IsDomain Sg := IsLocalization.isDomain_localization
    (powers_le_nonZeroDivisors_of_noZeroDivisors hg0)
  have : Algebra.FiniteType ℂ Sg := Algebra.FiniteType.trans (S := S) inferInstance
    (IsLocalization.finiteType_of_monoid_fg (Submonoid.powers g) Sg)
  -- the relative dimension is `m`
  have hdimSg : ringKrullDim Sg = P.dimension :=
    RingHom.IsStandardSmoothOfRelativeDimension.ringKrullDim_eq_complex
      (by rw [RingHom.isStandardSmoothOfRelativeDimension_algebraMap]; exact hrel)
  have hdimS : ringKrullDim Sg = ringKrullDim S := by
    refine le_antisymm (a3r_ringKrullDim_localization_le (Submonoid.powers g)) ?_
    exact a3m_ringKrullDim_le_of_injective (IsScalarTower.toAlgHom ℂ S Sg)
      (IsLocalization.injective Sg (powers_le_nonZeroDivisors_of_noZeroDivisors hg0))
  have hPm : P.dimension = m := by
    have := hdimSg.symm.trans (hdimS.trans hm)
    exact_mod_cast this
  -- `K` is an algebra over `S_g`
  have hgK : IsUnit (algebraMap S K g) := by
    refine isUnit_iff_ne_zero.2 fun h => hg ?_
    exact RingHom.mem_ker.2 h
  let _ : Algebra Sg K := (IsLocalization.Away.lift g hgK).toAlgebra
  have : IsScalarTower S Sg K := IsScalarTower.of_algebraMap_eq fun s =>
    (IsLocalization.Away.lift_eq g hgK s).symm
  rw [a3t_finrank_localization (S' := Sg) (Submonoid.powers g), Module.finrank_baseChange,
    Module.finrank_eq_of_rank_eq (Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential
      (S := Sg) P.dimension), hPm]

end Rank

section Chart

attribute [local instance] MvPolynomial.gradedAlgebra

variable (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [IsProjective X.hom]

omit [IsIntegral X.left] in
/-- The chart `Spec T_j → X` lies over `Spec ℂ` through `θ_j ∘ C`. -/
theorem a3t_chart_over (j : Fin (a3s_N X + 1)) :
    (a3s_CX X).κ j ≫ X.hom = Spec.map (CommRingCat.ofHom (((a3s_CX X).θ j).comp C)) := by
  have h1 : X.hom = a3s_i X ≫ ProjectiveSpace.toBase (Fin (a3s_N X + 1)) (Spec ↧ℂ) :=
    (a3s_pres X).immersion_toBase.symm
  have h2 : (a3s_CX X).κ j ≫ a3s_i X =
      Spec.map (a3m_restrictHom (a3m_projCharts (a3s_N X)) (a3s_i X) j) ≫
        a3m_Pnκ (a3s_N X) j :=
    a3m_restrict_κ_comp (a3m_projCharts (a3s_N X)) (a3s_i X) j
  have h3 : a3m_Pnκ (a3s_N X) j ≫ ProjectiveSpace.toBase (Fin (a3s_N X + 1)) (Spec ↧ℂ) =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom (R := ℤ) (A := ℂ)
        (B := HomogeneousLocalization.Away (UniversalGrading (a3s_N X))
          (MvPolynomial.X j : UniversalRing (a3s_N X))))) := by
    have := a3m_prodChart_fst (𝟙 (Spec ↧ℂ)) (g3c_chartι (a3s_N X) j)
    rw [Category.comp_id] at this
    exact this
  have e1 := congrArg ((a3s_CX X).κ j ≫ ·) h1
  have e2 : (a3s_CX X).κ j ≫ (a3s_i X ≫ ProjectiveSpace.toBase (Fin (a3s_N X + 1)) (Spec ↧ℂ)) =
      ((a3s_CX X).κ j ≫ a3s_i X) ≫ ProjectiveSpace.toBase (Fin (a3s_N X + 1)) (Spec ↧ℂ) :=
    (Category.assoc _ _ _).symm
  have e3 := congrArg (· ≫ ProjectiveSpace.toBase (Fin (a3s_N X + 1)) (Spec ↧ℂ)) h2
  have e4 := Category.assoc (Spec.map (a3m_restrictHom (a3m_projCharts (a3s_N X)) (a3s_i X) j))
    (a3m_Pnκ (a3s_N X) j) (ProjectiveSpace.toBase (Fin (a3s_N X + 1)) (Spec ↧ℂ))
  have e5 := congrArg (Spec.map (a3m_restrictHom (a3m_projCharts (a3s_N X)) (a3s_i X) j) ≫ ·) h3
  refine e1.trans (e2.trans (e3.trans (e4.trans (e5.trans
    ((Spec.map_comp _ _).symm.trans (congrArg Spec.map ?_))))))
  ext c
  change a3m_restrictHom (a3m_projCharts (a3s_N X)) (a3s_i X) j
    (Algebra.TensorProduct.includeLeftRingHom c) =
      a3m_restrictHom _ _ j (a3m_Pnθ _ j (C c))
  simp [a3m_Pnθ]

omit [IsIntegral X.left] in
/-- The charts of a smooth `X` are smooth `ℂ`-algebras. -/
theorem a3t_chart_smooth [Smooth X.hom] (j : Fin (a3s_N X + 1)) :
    letI : Algebra ℂ ((a3s_CX X).T j) := (((a3s_CX X).θ j).comp C).toAlgebra
    Algebra.Smooth ℂ ((a3s_CX X).T j) := by
  have hs : Smooth ((a3s_CX X).κ j ≫ X.hom) := inferInstance
  rw [a3t_chart_over] at hs
  exact HasRingHomProperty.Spec_iff.1 hs

end Chart

/-! ## The chart ring inside the localized cone -/

section Dehom

attribute [local instance] MvPolynomial.gradedAlgebra

variable {Y : Scheme.{0}} {σ : Type} [Fintype σ] (C : a3m_SpecCharts Y σ ℂ) [IsIntegral Y] (j : σ)

/-- The homogenization `Σ_e x_j^{D - e} F_e` of `F` in degree `D = deg F`. -/
def a3t_homog (F : MvPolynomial σ ℂ) : MvPolynomial σ ℂ :=
  ∑ e ∈ Finset.range (F.totalDegree + 1), X j ^ (F.totalDegree - e) * homogeneousComponent e F

omit [Fintype σ] in
theorem a3t_homog_isHomogeneous (F : MvPolynomial σ ℂ) :
    (a3t_homog j F).IsHomogeneous F.totalDegree := by
  refine IsHomogeneous.sum _ _ _ fun e he => ?_
  have h := (isHomogeneous_X_pow (R := ℂ) j (F.totalDegree - e)).mul
    (homogeneousComponent_isHomogeneous e F)
  rwa [Nat.sub_add_cancel (by simpa [Nat.lt_succ_iff] using he)] at h

omit [Fintype σ] in
/-- A ring map sending `x_j` to `1` does not see the homogenization. -/
theorem a3t_map_homog {R : Type} [CommRing R] (f : MvPolynomial σ ℂ →+* R) (hf : f (X j) = 1)
    (F : MvPolynomial σ ℂ) : f (a3t_homog j F) = f F := by
  conv_rhs => rw [← sum_homogeneousComponent F]
  rw [a3t_homog, map_sum, map_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [map_mul, map_pow, hf, one_pow, one_mul]

end Dehom

end HodgeLean.Adapters
