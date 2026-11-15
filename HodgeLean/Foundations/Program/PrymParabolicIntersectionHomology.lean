import HodgeLean.Foundations.Program.PrymParabolicIntersectionDefs

noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicTopology AlgebraicTopology.Singular
namespace HodgeLean.Foundations.Program

set_option backward.isDefEq.respectTransparency false in
theorem hga_proj_injective (P : TopPair.{0}) (n : ℕ)
    [Subsingleton (Homology ℤ P.snd n)] : Function.Injective (hg8_proj P n) := by
  apply LinearMap.ker_eq_bot.mp
  apply bot_unique
  intro x hx
  obtain ⟨a, ha⟩ := (ShortComplex.moduleCat_exact_iff _).mp
    ((relativeChainShortComplex_shortExact ℤ P).homology_exact₂ n) x hx
  have ha0 : a = 0 := (inferInstance : Subsingleton (Homology ℤ P.snd n)).elim _ _
  change x = 0
  simpa only [ha0, map_zero] using ha.symm

theorem hga_skel0_homology {G : Type} [Group G] [Finite G] {r : ℕ}
    {g : Fin r → G} {T : Type} [TopologicalSpace T] [T2Space T]
    (F : hg8_DeltaMap g T) (n : ℕ) (hn : n ≠ 0) :
    Subsingleton (Homology ℤ (hg8_pair10 F).snd n) := by
  letI : Finite (hg8_skel0 F) := (Set.finite_range F.vert).to_subtype
  let j : (hg8_pair10 F).snd → hg8_skel0 F := fun x ↦ ⟨x.1.1, x.2⟩
  have hj : Function.Injective j := by
    intro x y h
    have h' : x.1.1 = y.1.1 := congrArg (fun v : hg8_skel0 F ↦ (v : T)) h
    exact Subtype.ext (Subtype.ext h')
  letI : Finite (hg8_pair10 F).snd := Finite.of_injective j hj
  letI : T2Space (hg8_pair10 F).snd := by
    change T2Space (Subtype.val ⁻¹' hg8_skel0 F : Set (hg8_skel1 F))
    infer_instance
  letI : DiscreteTopology (hg8_pair10 F).snd := inferInstance
  exact ModuleCat.subsingleton_of_isZero
    (isZero_singularHomologyFunctor_of_totallyDisconnectedSpace
      (ModuleCat ℤ) n (ModuleCat.of ℤ ℤ) (hg8_pair10 F).snd hn)

set_option backward.isDefEq.respectTransparency false in
theorem hga_proj_fundClass {T : Type} [TopologicalSpace T]
    (F : hg8_DeltaMap b4b_root T) :
    hg8_proj (hg8_pair21 F) 2 (hga_fundClass F) = hg8_triRel F hg2_orient := by
  exact ShortComplex.moduleCatHomologyClass_naturality
    ((HomologicalComplex.shortComplexFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) 2).map
      (relativeChainProjection ℤ (hg8_pair21 F)))
    ⟨hga_fundChain F, hga_d_fundChain F _⟩

theorem hga_delta_proj (P : TopPair.{0}) (n : ℕ)
    (x : Homology ℤ P.fst (n + 1)) :
    hg8_delta P n (hg8_proj P (n + 1) x) = 0 := by
  exact congrArg (fun m ↦ m.hom x)
    ((relativeChainShortComplex_shortExact ℤ P).comp_δ (n + 1) n (by simp))

set_option backward.isDefEq.respectTransparency false in
theorem hga_generator_from_skeleta {T : Type} [TopologicalSpace T] [T2Space T]
    (F : hg8_DeltaMap b4b_root T)
    (hrel : Subsingleton (RelativeHomology ℤ (hg8_pair10 F) 2))
    (htri : Function.Bijective (hg8_triRel F))
    (hedge : Function.Injective (hg8_edgeRel F)) :
    ∃ e : Homology ℤ (TopCat.of T) 2 ≃ₗ[ℤ] ℤ, e (hga_fundClass F) = 1 := by
  letI := hga_skel0_homology F 2 (by omega)
  letI := hrel
  have hi0 := hga_proj_injective (hg8_pair10 F) 2
  letI : Subsingleton (Homology ℤ (hg8_pair21 F).snd 2) := hi0.subsingleton
  have hi := hga_proj_injective (hg8_pair21 F) 2
  let s : ℤ →ₗ[ℤ] Homology ℤ (hg8_pair21 F).fst 2 :=
    LinearMap.toSpanSingleton ℤ _ (hga_fundClass F)
  have hsproj (n : ℤ) : hg8_proj (hg8_pair21 F) 2 (s n) =
      hg8_triRel F (n • hg2_orient) := by
    calc
      hg8_proj (hg8_pair21 F) 2 (s n) =
          n • hg8_proj (hg8_pair21 F) 2 (hga_fundClass F) := by
        have hs : s n = n • hga_fundClass F :=
          int_smul_eq_zsmul (inferInstance : Module ℤ (Homology ℤ (hg8_pair21 F).fst 2)) n _
        exact (congrArg (hg8_proj (hg8_pair21 F) 2) hs).trans
          (map_zsmul (hg8_proj (hg8_pair21 F) 2) n (hga_fundClass F))
      _ = n • hg8_triRel F hg2_orient := congrArg (fun x ↦ n • x) (hga_proj_fundClass F)
      _ = hg8_triRel F (n • hg2_orient) := (map_zsmul (hg8_triRel F) n hg2_orient).symm
  have hsinj : Function.Injective s := by
    apply LinearMap.ker_eq_bot.mp
    apply bot_unique
    intro n hn
    have he : n • (hg2_orient : hg2_Tri b4b_Group 13 →₀ ℤ) = 0 := by
      apply htri.1
      rw [← hsproj, show s n = 0 from hn]
      simp only [map_zero]
    have hc := congrArg (fun w : hg2_Tri b4b_Group 13 →₀ ℤ ↦ w (Sum.inl (0, 1))) he
    change n = 0
    simpa only [Finsupp.smul_apply, (hg2_orient_coeffs (0 : Fin 13) (1 : b4b_Group)).1,
      smul_eq_mul, mul_one, Finsupp.zero_apply] using hc
  have hssurj : Function.Surjective s := by
    intro x
    obtain ⟨w, hw⟩ := htri.2 (hg8_proj (hg8_pair21 F) 2 x)
    have hw0 : hg2_bd2 ℤ b4b_root w = 0 := by
      apply hedge
      rw [← hg8_connecting2, hw, hga_delta_proj (hg8_pair21 F) 1 x]
      simp only [map_zero]
    have hwm : w ∈ Submodule.span ℤ {hg2_orient} := by
      rw [← hg2_cycles2 b4b_root b63d_root_product b63d_root_subgroup]
      exact hw0
    obtain ⟨n, hn⟩ := Submodule.mem_span_singleton.mp hwm
    refine ⟨n, hi ?_⟩
    rw [hsproj, hn, hw]
  let e := (LinearEquiv.ofBijective s ⟨hsinj, hssurj⟩).symm
  refine ⟨e, ?_⟩
  have he := (LinearEquiv.ofBijective s ⟨hsinj, hssurj⟩).symm_apply_apply 1
  change e (s 1) = 1 at he
  have hs1 : s 1 = hga_fundClass F := by
    exact LinearMap.toSpanSingleton_apply_one _ _ _
  rwa [hs1] at he

theorem hga_generator_eq_or_neg {M : Type} [AddCommGroup M] [Module ℤ M]
    (e : M ≃ₗ[ℤ] ℤ) (c v : M) (hc : e c = 1)
    (hv : Function.Surjective (fun n : ℤ ↦ n • v)) : c = v ∨ c = -v := by
  obtain ⟨n, hn⟩ := hv c
  have he : n * e v = 1 := by
    have h := congrArg e hn
    simpa only [map_zsmul, zsmul_eq_mul, Int.cast_id, hc] using h
  have hu : IsUnit n := isUnit_iff_dvd_one.mpr ⟨e v, he.symm⟩
  rcases Int.isUnit_iff.mp hu with h | h
  · left
    simpa only [h, one_smul] using hn.symm
  · right
    simpa only [h, neg_one_zsmul] using hn.symm

#print axioms hga_generator_eq_or_neg

end HodgeLean.Foundations.Program
