import HodgeLean.Foundations.Program.PrymParabolicIntersectionCochains

noncomputable section
open CategoryTheory AlgebraicTopology AlgebraicTopology.Singular
namespace HodgeLean.Foundations.Program

theorem hga_cochain_chain1 {G : Type} [Group G] {r : ℕ} {g : Fin r → G}
    {T : Type} [TopologicalSpace T] (F : hg8_DeltaMap g T)
    (φ : Simplicial.Cochain ℤ (TopCat.toSSet.obj (TopCat.of T)) 1)
    (z : hg2_Edge G r →₀ ℤ) :
    φ (hg5_chain1 F.edge z) =
      z.sum (fun ε n ↦ n * φ (hg5_chain1 F.edge (Finsupp.single ε 1))) := by
  classical
  simp only [hg5_chain1, Finsupp.linearCombination_apply, map_finsuppSum, map_smul,
    smul_eq_mul, Finsupp.sum_single_index, zero_mul, one_mul]

theorem hga_restriction_cocycle {G : Type} [Group G] {r : ℕ} {g : Fin r → G}
    {T : Type} [TopologicalSpace T] (F : hg8_DeltaMap g T)
    (φ : Simplicial.Cochain ℤ (TopCat.toSSet.obj (TopCat.of T)) 1)
    (hφ : φ ∘ₗ Simplicial.boundary ℤ 1 = 0) :
    hg2_delta1 ℤ ℤ g
      (fun ε ↦ φ (hg5_chain1 F.edge (Finsupp.single ε 1))) = 0 := by
  classical
  ext τ
  have h := LinearMap.congr_fun hφ (hg5_chain2 F.tri (Finsupp.single τ 1))
  change φ (Simplicial.boundary ℤ 1 (hg5_chain2 F.tri (Finsupp.single τ 1))) = 0 at h
  rw [hg5_bd_chain2 F.tri F.edge _ _ _ F.faces] at h
  simpa [hg2_delta1, LinearMap.funLeft, Finsupp.lmapDomain_apply,
    Finsupp.mapDomain_single] using h

set_option backward.isDefEq.respectTransparency false in
theorem hga_H1map_mapDelta {G : Type} [Group G] {r : ℕ} {g : Fin r → G}
    {T T' : Type} [TopologicalSpace T] [TopologicalSpace T']
    (F : hg8_DeltaMap g T) (φ : C(T, T')) (x : hg2_H1 ℤ g) :
    hg8_H1map (hga_mapDelta F φ) x =
      homologyMap ℤ 1 (TopCat.ofHom φ) (hg8_H1map F x) := by
  obtain ⟨z, rfl⟩ := Submodule.mkQ_surjective _ x
  let f := ((singularChainComplexFunctor.{0} (ModuleCat.{0} ℤ)).obj (ModuleCat.of ℤ ℤ)).map
    (TopCat.ofHom φ)
  let S := (HomologicalComplex.shortComplexFunctor (ModuleCat ℤ) (.down ℕ) 1).map f
  change _ = (ShortComplex.homologyMap S).hom _
  change ((SingularChainComplex ℤ (TopCat.of T')).sc 1).moduleCatHomologyClass
    (hg8_cycle1 (hga_mapDelta F φ) z) =
      (ShortComplex.homologyMap S).hom
        (((SingularChainComplex ℤ (TopCat.of T)).sc 1).moduleCatHomologyClass (hg8_cycle1 F z))
  rw [ShortComplex.moduleCatHomologyClass_naturality]
  congr 1
  apply Subtype.ext
  change hg5_chain1 (fun ε ↦ φ.comp (F.edge ε)) z.1 = hg8_chainMap φ 1 (hg5_chain1 F.edge z.1)
  exact (hg8_chain1_map φ F.edge z.1).symm

theorem hga_H1map_fibre {C : Type} [TopologicalSpace C]
    (F : hg8_DeltaMap b4b_root C) (V : Set (Fin 10 → ℂ))
    (hV : V ⊆ b6t_polydisc mr_base) (t : V) (x : hg2_H1 ℤ b4b_root) :
    hg8_H1map (hga_fibreMap F V hV t) x = hg9_toFibre F V hV t x := by
  exact hga_H1map_mapDelta F _ x

theorem hga_cellular_cocycle_of_singular_functional {G : Type} [Group G]
    {r : ℕ} {g : Fin r → G} {T : Type} [TopologicalSpace T]
    (F : hg8_DeltaMap g T) (l : Homology ℤ (TopCat.of T) 1 →ₗ[ℤ] ℤ) :
    ∃ α : hg2_Edge G r → ℤ, hg2_delta1 ℤ ℤ g α = 0 ∧
      ∀ z : LinearMap.ker (hg2_bd1 ℤ g),
        z.1.sum (fun ε n ↦ n * α ε) = l (hg8_H1map F (Submodule.Quotient.mk z)) := by
  obtain ⟨φ, hφ, he⟩ := hga_singular_cocycle_of_functional (TopCat.of T) l
  refine ⟨fun ε ↦ φ (hg5_chain1 F.edge (Finsupp.single ε 1)),
    hga_restriction_cocycle F φ hφ, ?_⟩
  intro z
  rw [← hga_cochain_chain1 F φ]
  exact he (hg8_cycle1 F z)

set_option backward.isDefEq.respectTransparency false in
theorem hga_chain2_map {I T T' : Type} [TopologicalSpace T] [TopologicalSpace T']
    (φ : C(T, T')) (σ : I → C(Convexity.StdSimplex ℝ (Fin 3), T)) (z : I →₀ ℤ) :
    hg8_chainMap φ 2 (hg5_chain2 σ z) = hg5_chain2 (fun i ↦ φ.comp (σ i)) z := by
  have he : hg8_chainMap φ 2 ∘ₗ hg5_chain2 σ =
      hg5_chain2 (fun i ↦ φ.comp (σ i)) := by
    ext i
    simp only [LinearMap.comp_apply, hg5_chain2, Finsupp.lsingle_apply, Finsupp.linearCombination_single, one_smul]
    change ((SSet.chainComplexMap (TopCat.toSSet.map (TopCat.ofHom φ))
      (ModuleCat.of ℤ ℤ)).f 2).hom _ = _
    rw [Simplicial.chainOfSimplex_map]
    rfl
  exact LinearMap.congr_fun he z

set_option backward.isDefEq.respectTransparency false in
theorem hga_fundClass_mapDelta {T T' : Type} [TopologicalSpace T] [TopologicalSpace T']
    (F : hg8_DeltaMap b4b_root T) (φ : C(T, T')) :
    hga_fundClass (hga_mapDelta F φ) =
      homologyMap ℤ 2 (TopCat.ofHom φ) (hga_fundClass F) := by
  let f := ((singularChainComplexFunctor.{0} (ModuleCat.{0} ℤ)).obj (ModuleCat.of ℤ ℤ)).map
    (TopCat.ofHom φ)
  let S := (HomologicalComplex.shortComplexFunctor (ModuleCat ℤ) (.down ℕ) 2).map f
  change _ = (ShortComplex.homologyMap S).hom _
  unfold hga_fundClass
  rw [ShortComplex.moduleCatHomologyClass_naturality]
  congr 1
  apply Subtype.ext
  change hg5_chain2 (fun τ ↦ φ.comp (F.tri τ)) hg2_orient =
    hg8_chainMap φ 2 (hg5_chain2 F.tri hg2_orient)
  exact (hga_chain2_map φ F.tri hg2_orient).symm

set_option backward.isDefEq.respectTransparency false in
theorem hga_generator_map_homeomorph {T T' : Type} [TopologicalSpace T] [TopologicalSpace T']
    (F : hg8_DeltaMap b4b_root T) (φ : T ≃ₜ T')
    (he : ∃ e : Homology ℤ (TopCat.of T) 2 ≃ₗ[ℤ] ℤ, e (hga_fundClass F) = 1) :
    ∃ e : Homology ℤ (TopCat.of T') 2 ≃ₗ[ℤ] ℤ,
      e (hga_fundClass (hga_mapDelta F ⟨φ, φ.continuous⟩)) = 1 := by
  obtain ⟨e, he⟩ := he
  let H : Homology ℤ (TopCat.of T) 2 ≃ₗ[ℤ] Homology ℤ (TopCat.of T') 2 :=
    ((((singularHomologyFunctor.{0} (ModuleCat.{0} ℤ) 2).obj (ModuleCat.of ℤ ℤ)).mapIso
      (TopCat.isoOfHomeo (X := TopCat.of T) (Y := TopCat.of T') φ))).toLinearEquiv
  refine ⟨H.symm.trans e, ?_⟩
  rw [hga_fundClass_mapDelta]
  change e (H.symm (H (hga_fundClass F))) = 1
  rw [LinearEquiv.symm_apply_apply]
  exact he

#print axioms hga_cochain_chain1
#print axioms hga_restriction_cocycle
#print axioms hga_H1map_mapDelta
#print axioms hga_H1map_fibre
#print axioms hga_cellular_cocycle_of_singular_functional
#print axioms hga_chain2_map
#print axioms hga_fundClass_mapDelta
#print axioms hga_generator_map_homeomorph

end HodgeLean.Foundations.Program
