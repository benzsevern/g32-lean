import HodgeLean.Foundations.Program.PrymParabolicIntersectionHomology
import HodgeLean.Foundations.Port.AlgebraicTopology.Singular.CoefficientBaseChange

noncomputable section
open CategoryTheory AlgebraicTopology AlgebraicTopology.Singular
namespace HodgeLean.Foundations.Program

set_option backward.isDefEq.respectTransparency false in
theorem hga_chainFinsupp_simplex (T : TopCat.{0}) (n : ℕ)
    (σ : (TopCat.toSSet.obj T).obj (Opposite.op (SimplexCategory.mk n))) :
    (chainGroupFinsuppIso ℤ T n).toLinearEquiv (Simplicial.chainOfSimplex ℤ σ) =
      Finsupp.single σ 1 := by
  exact chainGroupFinsuppIso_iota ℤ T n σ 1

#print axioms hga_chainFinsupp_simplex
set_option backward.isDefEq.respectTransparency false in
theorem hga_singular_boundary_split (T : TopCat.{0}) :
    ∃ d : Simplicial.ChainGroup ℤ (TopCat.toSSet.obj T) 0 →ₗ[ℤ]
        Simplicial.ChainGroup ℤ (TopCat.toSSet.obj T) 1,
      Simplicial.boundary ℤ 0 ∘ₗ d ∘ₗ Simplicial.boundary ℤ 0 =
        (Simplicial.boundary ℤ 0 : Simplicial.ChainGroup ℤ (TopCat.toSSet.obj T) 1 →ₗ[ℤ] _) := by
  classical
  let Y := TopCat.toSSet.obj T
  let e0 := (chainGroupFinsuppIso ℤ T 0).toLinearEquiv
  let e1 := (chainGroupFinsuppIso ℤ T 1).toLinearEquiv
  let b := e0.toLinearMap ∘ₗ Simplicial.boundary ℤ 0 ∘ₗ e1.symm.toLinearMap
  have hb (σ : Y.obj (Opposite.op (SimplexCategory.mk 1))) :
      b (Finsupp.single σ 1) = Finsupp.single (Y.δ 0 σ) 1 - Finsupp.single (Y.δ 1 σ) 1 := by
    have he : e1.symm (Finsupp.single σ 1) = Simplicial.chainOfSimplex ℤ σ :=
      e1.symm_apply_eq.mpr (hga_chainFinsupp_simplex T 1 σ).symm
    change e0 (Simplicial.boundary ℤ 0 (e1.symm (Finsupp.single σ 1))) = _
    rw [he]
    change (chainGroupFinsuppIso ℤ T 0).toLinearEquiv _ = _
    simp only [Simplicial.boundary_chainOfSimplex,
      Fin.sum_univ_succ, Fin.val_zero, pow_zero, one_smul, Fin.val_succ,
      Fin.sum_univ_zero, add_zero, pow_one, neg_smul, map_add, map_neg,
      Nat.zero_add, Fin.succ_zero_eq_one]
    rw [hga_chainFinsupp_simplex T 0 (Y.δ 0 σ),
      hga_chainFinsupp_simplex T 0 (Y.δ 1 σ)]
    exact (sub_eq_add_neg _ _).symm
  obtain ⟨d, hd⟩ := hg2_graph_boundary_split (fun σ => Y.δ 1 σ) (fun σ => Y.δ 0 σ) b hb
  refine ⟨e1.symm.toLinearMap ∘ₗ d ∘ₗ e0.toLinearMap, ?_⟩
  ext x
  apply e0.injective
  have h := LinearMap.congr_fun hd (e1 x)
  change e0 (Simplicial.boundary ℤ 0 (e1.symm (d
      (e0 (Simplicial.boundary ℤ 0 (e1.symm (e1 x))))))) =
    e0 (Simplicial.boundary ℤ 0 (e1.symm (e1 x))) at h
  change e0 (Simplicial.boundary ℤ 0 (e1.symm (d
      (e0 (Simplicial.boundary ℤ 0 x))))) = e0 (Simplicial.boundary ℤ 0 x)
  simpa only [LinearEquiv.symm_apply_apply] using h

#print axioms hga_singular_boundary_split
set_option backward.isDefEq.respectTransparency false in
theorem hga_extend_homology_functional {R : Type} [CommRing R]
    (S : ShortComplex (ModuleCat.{0} R)) (d : S.X₃ →ₗ[R] S.X₂)
    (hd : S.g.hom ∘ₗ d ∘ₗ S.g.hom = S.g.hom) (l : S.homology →ₗ[R] R) :
    ∃ φ : S.X₂ →ₗ[R] R, φ ∘ₗ S.f.hom = 0 ∧
      ∀ z : LinearMap.ker S.g.hom, φ z.1 = l (S.moduleCatHomologyClass z) := by
  let P : S.X₂ →ₗ[R] LinearMap.ker S.g.hom :=
    (LinearMap.id - d ∘ₗ S.g.hom).codRestrict _ (by
      intro z
      change S.g.hom (z - d (S.g.hom z)) = 0
      rw [map_sub]
      have h := LinearMap.congr_fun hd z
      change S.g.hom (d (S.g.hom z)) = S.g.hom z at h
      exact sub_eq_zero.mpr h.symm)
  have hP (z : LinearMap.ker S.g.hom) : P z.1 = z := by
    apply Subtype.ext
    change z.1 - d (S.g.hom z.1) = z.1
    rw [show S.g.hom z.1 = 0 from z.2, map_zero, sub_zero]
  let φ := l ∘ₗ S.moduleCatHomologyClass ∘ₗ P
  have hφ (z : LinearMap.ker S.g.hom) : φ z.1 = l (S.moduleCatHomologyClass z) := by
    change l (S.moduleCatHomologyClass (P z.1)) = _
    rw [hP]
  refine ⟨φ, ?_, hφ⟩
  ext x
  change φ (S.f.hom x) = 0
  let z : LinearMap.ker S.g.hom := ⟨S.f.hom x, S.moduleCat_zero_apply x⟩
  change φ z.1 = 0
  rw [hφ, hg8_homologyClass_eq_zero S z ⟨x, rfl⟩, map_zero]

#print axioms hga_extend_homology_functional
set_option backward.isDefEq.respectTransparency false in
theorem hga_singular_cocycle_of_functional (T : TopCat.{0})
    (l : Homology ℤ T 1 →ₗ[ℤ] ℤ) :
    ∃ φ : Simplicial.Cochain ℤ (TopCat.toSSet.obj T) 1,
      φ ∘ₗ Simplicial.boundary ℤ 1 = 0 ∧
      ∀ z : LinearMap.ker ((SingularChainComplex ℤ T).sc 1).g.hom,
        φ z.1 = l (((SingularChainComplex ℤ T).sc 1).moduleCatHomologyClass z) := by
  let K := SingularChainComplex ℤ T
  have hs : ∃ d : (K.sc 1).X₃ →ₗ[ℤ] (K.sc 1).X₂,
      (K.sc 1).g.hom ∘ₗ d ∘ₗ (K.sc 1).g.hom = (K.sc 1).g.hom := by
    change ∃ d : K.X ((ComplexShape.down ℕ).next 1) →ₗ[ℤ] K.X 1,
      (K.d 1 ((ComplexShape.down ℕ).next 1)).hom ∘ₗ d ∘ₗ
        (K.d 1 ((ComplexShape.down ℕ).next 1)).hom =
          (K.d 1 ((ComplexShape.down ℕ).next 1)).hom
    rw [ChainComplex.next_nat_succ 0]
    exact hga_singular_boundary_split T
  obtain ⟨d, hd⟩ := hs
  obtain ⟨φ, hφ, heval⟩ := hga_extend_homology_functional (K.sc 1) d hd l
  change Simplicial.Cochain ℤ (TopCat.toSSet.obj T) 1 at φ
  refine ⟨φ, ?_, heval⟩
  change φ ∘ₗ (K.d ((ComplexShape.down ℕ).prev 1) 1).hom =
    (0 : K.X ((ComplexShape.down ℕ).prev 1) →ₗ[ℤ] ℤ) at hφ
  ext c
  let hp := ChainComplex.prev ℕ 1
  have h := LinearMap.congr_fun hφ ((K.XIsoOfEq hp).inv.hom c)
  change φ ((K.d ((ComplexShape.down ℕ).prev 1) 1).hom
    ((K.XIsoOfEq hp).inv.hom c)) = 0 at h
  have hd' := congrArg (fun m ↦ m.hom c) (K.XIsoOfEq_inv_comp_d hp 1)
  change (K.d ((ComplexShape.down ℕ).prev 1) 1).hom
    ((K.XIsoOfEq hp).inv.hom c) = (K.d 2 1).hom c at hd'
  exact (congrArg φ hd').symm.trans h

#print axioms hga_singular_cocycle_of_functional
theorem hga_factor_through_split {R : Type} [CommRing R]
    {M N A : Type} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [AddCommGroup A] [Module R A] (b : M →ₗ[R] N) (d : N →ₗ[R] M)
    (hd : b ∘ₗ d ∘ₗ b = b) (l : M →ₗ[R] A)
    (hl : ∀ z : LinearMap.ker b, l z.1 = 0) : l = (l ∘ₗ d) ∘ₗ b := by
  ext x
  have hz : b (x - d (b x)) = 0 := by
    rw [map_sub]
    exact sub_eq_zero.mpr (LinearMap.congr_fun hd x).symm
  have h := hl ⟨x - d (b x), hz⟩
  simpa only [map_sub, sub_eq_zero, LinearMap.comp_apply] using h

#print axioms hga_factor_through_split

theorem hga_integral_coboundary_of_zero_cycles {G : Type} [Group G] {r : ℕ}
    (g : Fin r → G) (α : hg2_Edge G r → ℤ)
    (hα : ∀ z : LinearMap.ker (hg2_bd1 ℤ g), z.1.sum (fun ε n ↦ n * α ε) = 0) :
    ∃ φ : hg2_Vert g → ℤ, hg2_delta0 ℤ ℤ g φ = α := by
  classical
  obtain ⟨d, hd⟩ := hg2_graph_boundary_split (hg2_src g) (hg2_tgt g) (hg2_bd1 ℤ g)
    (fun ε ↦ by simp [hg2_bd1])
  let l : (hg2_Edge G r →₀ ℤ) →ₗ[ℤ] ℤ := Finsupp.linearCombination ℤ α
  have hl : ∀ z : LinearMap.ker (hg2_bd1 ℤ g), l z.1 = 0 := by
    intro z
    simpa only [l, Finsupp.linearCombination_apply, smul_eq_mul] using hα z
  have he := hga_factor_through_split (hg2_bd1 ℤ g) d hd l hl
  refine ⟨fun v ↦ l (d (Finsupp.single v 1)), ?_⟩
  ext ε
  have h := LinearMap.congr_fun he (Finsupp.single ε 1)
  change _ = l (d (hg2_bd1 ℤ g (Finsupp.single ε 1))) at h
  simpa [l, hg2_bd1, hg2_delta0, LinearMap.funLeft] using h.symm

#print axioms hga_integral_coboundary_of_zero_cycles

theorem hga_integral_coboundary_of_same_cycles {G : Type} [Group G] {r : ℕ}
    (g : Fin r → G) (α β : hg2_Edge G r → ℤ)
    (h : ∀ z : LinearMap.ker (hg2_bd1 ℤ g),
      z.1.sum (fun ε n ↦ n * α ε) = z.1.sum (fun ε n ↦ n * β ε)) :
    ∃ φ : hg2_Vert g → ℤ, hg2_delta0 ℤ ℤ g φ = α - β := by
  apply hga_integral_coboundary_of_zero_cycles
  intro z
  change (∑ ε ∈ z.1.support, z.1 ε * (α ε - β ε)) = 0
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib]
  exact sub_eq_zero.mpr (h z)

#print axioms hga_integral_coboundary_of_same_cycles

theorem hga_field_coboundary_of_zero_cycles {K : Type} [Field K]
    {G : Type} [Group G] {r : ℕ} (g : Fin r → G) (α : hg2_Edge G r → K)
    (hα : ∀ z : LinearMap.ker (hg2_bd1 ℤ g),
      z.1.sum (fun ε n ↦ (n : K) * α ε) = 0) :
    ∃ φ : hg2_Vert g → K, hg2_delta0 K K g φ = α := by
  classical
  obtain ⟨d, hd⟩ := hg2_graph_boundary_split (hg2_src g) (hg2_tgt g) (hg2_bd1 ℤ g)
    (fun ε ↦ by simp [hg2_bd1])
  let l : (hg2_Edge G r →₀ ℤ) →ₗ[ℤ] K := Finsupp.linearCombination ℤ α
  have hl : ∀ z : LinearMap.ker (hg2_bd1 ℤ g), l z.1 = 0 := by
    intro z
    simpa only [l, Finsupp.linearCombination_apply, zsmul_eq_mul] using hα z
  have he := hga_factor_through_split (hg2_bd1 ℤ g) d hd l hl
  refine ⟨fun v ↦ l (d (Finsupp.single v 1)), ?_⟩
  ext ε
  have h := LinearMap.congr_fun he (Finsupp.single ε 1)
  change _ = l (d (hg2_bd1 ℤ g (Finsupp.single ε 1))) at h
  simpa [l, hg2_bd1, hg2_delta0, LinearMap.funLeft] using h.symm

#print axioms hga_field_coboundary_of_zero_cycles

end HodgeLean.Foundations.Program
