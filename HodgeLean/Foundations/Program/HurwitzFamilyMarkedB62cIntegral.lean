import HodgeLean.Foundations.Program.HurwitzFamilyMarkedB62cPeriods

noncomputable section

namespace HodgeLean.Foundations.Program

open CategoryTheory AlgebraicTopology AlgebraicTopology.Singular

def b6m_integralCochain (Y : SSet.{0}) (n : ℕ) (M : Type) [AddCommGroup M]
    (f : Y.obj (Opposite.op (SimplexCategory.mk n)) → M) :
    (Y.chainComplex (ModuleCat.of ℤ ℤ)).X n →ₗ[ℤ] M :=
  ((Y.isColimitChainComplexXCofan (ModuleCat.of ℤ ℤ) n).desc
    (Limits.Cofan.mk (ModuleCat.of ℤ M) fun σ ↦
      ModuleCat.ofHom (LinearMap.toSpanSingleton ℤ M (f σ)))).hom

theorem b6m_integralCochain_simplex (Y : SSet.{0}) (n : ℕ) (M : Type) [AddCommGroup M]
    (f : Y.obj (Opposite.op (SimplexCategory.mk n)) → M)
    (σ : Y.obj (Opposite.op (SimplexCategory.mk n))) :
    b6m_integralCochain Y n M f (Simplicial.chainOfSimplex ℤ σ) = f σ := by
  have h := (Y.isColimitChainComplexXCofan (ModuleCat.of ℤ ℤ) n).fac
    (Limits.Cofan.mk (ModuleCat.of ℤ M) fun σ ↦
      ModuleCat.ofHom (LinearMap.toSpanSingleton ℤ M (f σ))) ⟨σ⟩
  have h1 := ConcreteCategory.congr_hom h (1 : ℤ)
  exact h1.trans (by simp)

theorem b6m_integralCochain_boundary (Y : SSet.{0}) (M : Type) [AddCommGroup M]
    (f : Y.obj (Opposite.op (SimplexCategory.mk 1)) → M)
    (hf : ∀ τ : Y.obj (Opposite.op (SimplexCategory.mk 2)),
      f (Y.δ 0 τ) - f (Y.δ 1 τ) + f (Y.δ 2 τ) = 0) :
    (b6m_integralCochain Y 1 M f).comp
      ((Y.chainComplex (ModuleCat.of ℤ ℤ)).d 2 1).hom = 0 := by
  suffices h : ModuleCat.ofHom ((b6m_integralCochain Y 1 M f).comp
      ((Y.chainComplex (ModuleCat.of ℤ ℤ)).d 2 1).hom) =
      (0 : (Y.chainComplex (ModuleCat.of ℤ ℤ)).X 2 ⟶ ModuleCat.of ℤ M) from
    congrArg ModuleCat.Hom.hom h
  apply SSet.chainComplex_hom_ext
  intro τ
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  change ℤ at a
  have hi : (Y.ιChainComplex (R := ModuleCat.of ℤ ℤ) τ).hom a =
      a • Simplicial.chainOfSimplex ℤ τ := by
    rw [Simplicial.chainOfSimplex, ← map_zsmul]
    simp
  change b6m_integralCochain Y 1 M f
    (((Y.chainComplex (ModuleCat.of ℤ ℤ)).d 2 1).hom
      ((Y.ιChainComplex (R := ModuleCat.of ℤ ℤ) τ).hom a)) = 0
  rw [hi, map_zsmul, map_zsmul]
  change a • b6m_integralCochain Y 1 M f
    (Simplicial.boundary ℤ 1 (Simplicial.chainOfSimplex ℤ τ)) = 0
  suffices h : b6m_integralCochain Y 1 M f (Simplicial.boundary ℤ 1
      (Simplicial.chainOfSimplex ℤ τ)) = 0 by rw [h, smul_zero]
  rw [Simplicial.boundary_chainOfSimplex, map_sum]
  simpa [Fin.sum_univ_succ, b6m_integralCochain_simplex,
    sub_eq_add_neg, add_assoc] using hf τ

set_option backward.isDefEq.respectTransparency false in
theorem b6m_descIntegralCocycle (R : Type) [CommRing R]
    (S : ShortComplex (ModuleCat.{0} R))
    (M : Type) [AddCommGroup M] [Module R M] (φ : S.X₂ →ₗ[R] M)
    (hφ : φ.comp S.f.hom = 0) :
    ∃ P : S.homology →ₗ[R] M,
      ∀ z : LinearMap.ker S.g.hom, P (S.moduleCatHomologyClass z) = φ z := by
  let F := (LinearMap.range S.moduleCatToCycles).liftQ
      (φ.comp (LinearMap.ker S.g.hom).subtype) (by
        rintro _ ⟨z, rfl⟩
        exact LinearMap.congr_fun hφ z)
  refine ⟨F.comp S.moduleCatHomologyIso.hom.hom, fun z ↦ ?_⟩
  change F (S.moduleCatHomologyIso.toLinearEquiv
    (S.moduleCatHomologyIso.toLinearEquiv.symm
      ((LinearMap.range S.moduleCatToCycles).mkQ z))) = φ z
  rw [LinearEquiv.apply_symm_apply]
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem b6m_integral_eval_complex_cocycle (C : Type) [TopologicalSpace C]
    (ψ : Simplicial.Cocycle ℂ (TopCat.toSSet.obj (TopCat.of C)) 1) :
    ∃ P : b6m_H1 C →ₗ[ℤ] ℂ, ∀ p : C(UnitAddCircle, C),
      P (((SingularChainComplex ℤ (TopCat.of C)).sc 1).moduleCatHomologyClass
        (HodgeLean.Adapters.loopCycle ℤ p)) =
      ψ.1 (Simplicial.chainOfSimplex ℂ (HodgeLean.Adapters.loopSimplex p)) := by
  let Y := TopCat.toSSet.obj (TopCat.of C)
  let f := fun σ ↦ ψ.1 (Simplicial.chainOfSimplex ℂ σ)
  have hf : ∀ τ : Y.obj (Opposite.op (SimplexCategory.mk 2)),
      f (Y.δ 0 τ) - f (Y.δ 1 τ) + f (Y.δ 2 τ) = 0 :=
    b3Rest2_cocycle_tri ψ
  obtain ⟨P, hP⟩ := b6m_descIntegralCocycle ℤ
    ((SingularChainComplex ℤ (TopCat.of C)).sc 1) ℂ
    (b6m_integralCochain Y 1 ℂ f) (by
      change (b6m_integralCochain Y 1 ℂ f).comp
        ((Y.chainComplex (ModuleCat.of ℤ ℤ)).d ((ComplexShape.down ℕ).prev 1) 1).hom = 0
      rw [ChainComplex.prev]
      exact b6m_integralCochain_boundary Y ℂ f hf)
  refine ⟨P, fun p ↦ ?_⟩
  exact (hP (HodgeLean.Adapters.loopCycle ℤ p)).trans
    (b6m_integralCochain_simplex Y 1 ℂ f _)

open scoped Manifold ContDiff

theorem b6m_period_evaluation_exists (C : Type) [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] [T2Space C] [CompactSpace C] [ConnectedSpace C] :
    ∃ P : b6m_H1 C →ₗ[ℤ] (b3_HolForm ℂ C → ℂ),
      ∀ γ : b3_SmoothLoop ℂ C, P (b6m_loopClass C γ) = b3_period ℂ C γ := by
  classical
  obtain ⟨hfin, _, hdisc⟩ := b3Rest2_lattice_instances (C := C) (E := ℂ) (by simp)
  let := hfin
  let := hdisc
  let p₀ : C := Classical.choice inferInstance
  obtain ⟨aj, haj⟩ := b3A_exists_abelJacobi (E := ℂ) (by simp) p₀
  have hc : Continuous aj := (b3Rest_abelJacobi_holomorphic (by simp) p₀ aj haj).continuous
  choose P hP using fun θ : b3_HolForm ℂ C ↦
    b6m_integral_eval_complex_cocycle C
      (b3Rest2_integCocycle aj hc (AddMonoidHom.id ℂ) θ)
  refine ⟨LinearMap.pi P, fun γ ↦ funext fun θ ↦ ?_⟩
  exact (hP θ (b3Rest2_circ γ)).trans
    (b3Rest2_integCocycle_loop aj hc (by simp) p₀ haj (AddMonoidHom.id ℂ)
      θ γ (b3Rest2_circ γ) (fun _ ↦ rfl))

theorem b6m_period_eq_of_loopClass_eq (C : Type) [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (γ δ : b3_SmoothLoop ℂ C) (h : b6m_loopClass C γ = b6m_loopClass C δ) :
    b3_latticePeriod ℂ C γ = b3_latticePeriod ℂ C δ := by
  obtain ⟨P, hP⟩ := b6m_period_evaluation_exists C
  apply Subtype.ext
  exact (hP γ).symm.trans ((congrArg P h).trans (hP δ))

theorem b6m_period_evaluation_range (C : Type) [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (P : b6m_H1 C →ₗ[ℤ] (b3_HolForm ℂ C → ℂ))
    (hP : ∀ γ : b3_SmoothLoop ℂ C, P (b6m_loopClass C γ) = b3_period ℂ C γ)
    (y : b3_periodLattice ℂ C) : ∃ x : b6m_H1 C, P x = y := by
  apply b3Rest2_lattice_induction (E := ℂ) (C := C)
    (fun y ↦ ∃ x : b6m_H1 C, P x = y)
  · exact ⟨0, map_zero P⟩
  · rintro y z ⟨x, hx⟩ ⟨w, hw⟩
    exact ⟨x + w, (map_add P x w).trans (congrArg₂ (· + ·) hx hw)⟩
  · rintro y ⟨x, hx⟩
    exact ⟨-x, (map_neg P x).trans (congrArg Neg.neg hx)⟩
  · intro γ
    exact ⟨b6m_loopClass C γ, hP γ⟩

theorem b6m_period_lattice_lift (C : Type) [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (P : b6m_H1 C →ₗ[ℤ] (b3_HolForm ℂ C → ℂ))
    (hP : ∀ γ : b3_SmoothLoop ℂ C, P (b6m_loopClass C γ) = b3_period ℂ C γ) :
    ∃ S : b3_periodLattice ℂ C →ₗ[ℤ] b6m_H1 C,
      (∀ y : b3_periodLattice ℂ C, P (S y) = y) ∧ Function.Injective S := by
  classical
  have := (b3Rest2_lattice_instances (C := C) (E := ℂ) (by simp)).2.1
  choose x hx using b6m_period_evaluation_range C P hP
  let b := Module.Free.chooseBasis ℤ (b3_periodLattice ℂ C)
  let S := (Finsupp.linearCombination ℤ (fun i ↦ x (b i))).comp b.repr.toLinearMap
  have h : P.comp S = (b3_periodLattice ℂ C).subtype.toIntLinearMap := by
    apply b.ext
    intro i
    simpa [S] using hx (b i)
  have hS : ∀ y : b3_periodLattice ℂ C, P (S y) = y :=
    fun y ↦ LinearMap.congr_fun h y
  refine ⟨S, hS, fun y z hyz ↦ ?_⟩
  apply Subtype.ext
  exact (hS y).symm.trans ((congrArg P hyz).trans (hS z))

end HodgeLean.Foundations.Program
