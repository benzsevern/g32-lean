import HodgeLean.Foundations.Program.G32SelectedRealizationProjector

noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Papers HodgeLean.Foundations
open HodgeLean.Foundations.AppellHumbert
open scoped TensorProduct CategoryTheory.MonObj Manifold ContDiff
namespace HodgeLean.Foundations.Program

theorem g32x_precomp_trace (Λ : Type) [AddCommGroup Λ]
    [Module.Free ℤ Λ] [Module.Finite ℤ Λ] (φ : Λ →+ Λ) :
    LinearMap.trace ℚ (Λ →+ ℚ) (b63g_precomp φ) =
      (LinearMap.trace ℤ Λ φ.toIntLinearMap : ℚ) := by
  classical
  let b := Module.Free.chooseBasis ℤ Λ
  let d := latticeDualBasisQ (Λ := Λ)
  rw [LinearMap.trace_eq_matrix_trace ℚ d,
    LinearMap.trace_eq_matrix_trace ℤ b]
  simp only [Matrix.trace, Int.cast_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Matrix.diag_apply, LinearMap.toMatrix_apply]
  change d.repr ((d i).comp φ) i = (b.repr (φ (b i)) i : ℚ)
  simp [d, b, latticeDualBasisQ, latticeDualEquiv, b63g_precomp,
    latticeDualBasis, Int.coe_castAddHom]

theorem g32x_modelOperator_trace (Λ : Type) [AddCommGroup Λ]
    [Module.Free ℤ Λ] [Module.Finite ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) (hQ : b2_IsRiemannForm Λ F Q) (φ : Λ →+ Λ) :
    LinearMap.trace ℚ (HQ (b5_model Λ F hF Q) 1) (b63g_modelOperator Λ F hF Q hQ φ) =
      (LinearMap.trace ℤ Λ φ.toIntLinearMap : ℚ) := by
  letI := b5_groupObj Λ F hF Q hQ
  letI : IsIntegral (b5_model Λ F hF Q).left := b5_integral Λ F hF Q hQ
  letI := b5_smooth Λ F hF Q hQ
  letI := b5_projective Λ F hF Q hQ
  letI : FiniteDimensional ℚ (Λ →+ ℚ) := Module.Finite.of_basis latticeDualBasisQ
  let e := b5_periodEquiv Λ F hF Q hQ
  let p := abelianPeriodEquiv (b5_model Λ F hF Q)
  let ep : HQ (b5_model Λ F hF Q) 1 ≃ₗ[ℚ] (Λ →+ ℚ) :=
    { toFun := fun x ↦ (p x).comp e.toAddMonoidHom
      invFun := fun x ↦ p.symm (x.comp e.symm.toAddMonoidHom)
      map_add' := fun x y ↦ by ext l; simp
      map_smul' := fun c x ↦ by ext l; simp
      left_inv := fun x ↦ by apply p.injective; ext l; simp
      right_inv := fun x ↦ by ext l; simp }
  have he : b63g_modelOperator Λ F hF Q hQ φ = ep.symm.conj (b63g_precomp φ) := by
    apply LinearMap.ext
    intro x
    apply p.injective
    ext l
    simp [b63g_modelOperator, b63g_dualOperator, b63g_precomp,
      b63g_modelMap, ep, p, e, LinearMap.comp_apply, LinearEquiv.conj_apply]
  rw [he, LinearMap.trace_conj', g32x_precomp_trace]

theorem g32x_bar_character {G V : Type} [Group G] [Finite G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) (g : G) :
    (HurwitzPrymRex_barRep ρ).character g = star (ρ.character g) := by
  unfold Representation.character
  rw [Module.End.trace_eq_sum_roots_charpoly_of_splits (IsAlgClosed.splits _),
    Module.End.trace_eq_sum_roots_charpoly_of_splits (IsAlgClosed.splits _),
    HurwitzPrymRex_roots_bar]
  exact (map_multiset_sum (starRingEnd ℂ) _).symm

theorem g32x_homG_top_finrank {G V W : Type} [Group G]
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ G V) (σ : Representation ℂ G W) :
    Module.finrank ℂ (b4_HomG ρ (fun g ↦ σ g) ⊤) =
      Module.finrank ℂ (Representation.IntertwiningMap ρ σ) := by
  let e : b4_HomG ρ (fun g ↦ σ g) ⊤ ≃ₗ[ℂ] Representation.IntertwiningMap ρ σ :=
    { toFun := fun φ ↦ ⟨φ.val, fun g ↦ LinearMap.ext (fun v ↦ φ.property.2 g v)⟩
      invFun := fun ψ ↦ ⟨ψ.toLinearMap, fun _ ↦ Submodule.mem_top, ψ.isIntertwining⟩
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  exact e.finrank_eq

theorem g32x_period_character_average
    (C : Type) [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] [T2Space C] [CompactSpace C] [ConnectedSpace C]
    [MulAction b4b_Group C]
    (hG : ∀ a : b4b_Group, ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (fun x : C ↦ a • x))
    (τ : FDRep ℂ b4b_Group) :
    (Fintype.card b4b_Group : ℂ)⁻¹ * ∑ a : b4b_Group,
      ((LinearMap.trace ℤ (b3_periodLattice ℂ C)
        (b4_latticeAct ℂ a⁻¹).toIntLinearMap : ℤ) : ℂ) * star (τ.character a) =
      (Module.finrank ℂ (b4_HomG τ.ρ (fun a ↦ b4_cplxAct ℂ (C := C) a) ⊤) : ℂ) := by
  letI : Module.Finite ℤ (b3_periodLattice ℂ C) := b3_periodLattice_finite (by simp)
  let σ := b63d_periodRep C hG
  have htrace (a : b4b_Group) : σ.character a =
      ((LinearMap.trace ℤ (b3_periodLattice ℂ C)
        (b4_latticeAct ℂ a).toIntLinearMap : ℤ) : ℂ) := by
    exact LinearMap.trace_baseChange _ ℂ
  have htop : b2_conjSubmodule (b3_periodLattice ℂ C)
      (⊤ : Submodule ℂ (ℂ ⊗[ℤ] b3_periodLattice ℂ C)) = ⊤ := by
    apply top_unique
    intro x _
    apply Submodule.subset_span
    exact ⟨b2_conj _ x, Submodule.mem_top, b2a_conj_conj x⟩
  have hbar := HurwitzPrymRex_finrank_homG_bar
    (fun a : b4b_Group ↦ b4_latticeAct ℂ (C := C) a) ⊤ τ.ρ
  rw [htop] at hbar
  calc
    _ = (Fintype.card b4b_Group : ℂ)⁻¹ * ∑ a : b4b_Group,
        σ.character a * (HurwitzPrymRex_barRep τ.ρ).character a⁻¹ := by
      congr 1
      symm
      refine Fintype.sum_equiv (Equiv.inv b4b_Group) _ _ fun a ↦ ?_
      simp only [Equiv.inv_apply, inv_inv, g32x_bar_character, htrace]
      rfl
    _ = (Module.finrank ℂ (Representation.IntertwiningMap
        (HurwitzPrymRex_barRep τ.ρ) σ) : ℂ) := by
      simpa only [Nat.card_eq_fintype_card] using
        Representation.card_inv_mul_sum_char_mul_char_eq_finrank
          (HurwitzPrymRex_barRep τ.ρ) σ
    _ = _ := by
      congr 1
      rw [← g32x_homG_top_finrank]
      exact hbar.symm

theorem g32x_nielsen_rank_sum (g : Fin 13 → b4b_Group)
    (hg : g32h_Nielsen (fun j ↦ b4b_toMatrix (g j))) (τ : FDRep ℂ g32p_G) :
    ∑ j : Fin 13, Module.finrank ℂ (LinearMap.range (τ.ρ (g j) - LinearMap.id)) =
      ∑ j : Fin 13, Module.finrank ℂ (LinearMap.range (τ.ρ (g32p_classDatum j) - LinearMap.id)) := by
  obtain ⟨σ, hσ⟩ := hg.1
  have he (j : Fin 13) :
      Module.finrank ℂ (LinearMap.range (τ.ρ (g j) - LinearMap.id)) =
        Module.finrank ℂ (LinearMap.range (τ.ρ (g32p_classDatum (σ j)) - LinearMap.id)) := by
    obtain ⟨a, ha, b, hb, hab, hj⟩ := hσ j
    let a' : g32p_G := ⟨a, ha⟩
    let b' : g32p_G := ⟨b, hb⟩
    have hab' : a' * b' = 1 := Subtype.ext hab
    have hb' : b' = a'⁻¹ := by
      simpa [mul_assoc] using congrArg (fun z ↦ a'⁻¹ * z) hab'
    have hj' : g j = a' * g32p_classDatum (σ j) * b' := Subtype.ext hj
    rw [hj', hb']
    exact b63d_rep_rank_conjugate τ.ρ a' (g32p_classDatum (σ j))
  calc
    _ = ∑ j : Fin 13, Module.finrank ℂ
        (LinearMap.range (τ.ρ (g32p_classDatum (σ j)) - LinearMap.id)) :=
      Finset.sum_congr rfl (fun j _ ↦ he j)
    _ = _ := Fintype.sum_equiv σ _ _ (fun _ ↦ rfl)

theorem g32x_irreducible_of_simple {G : Type} [Group G]
    (τ : FDRep ℂ G) (hτ : CategoryTheory.Simple τ) : Representation.IsIrreducible τ.ρ := by
  letI := hτ
  have htop : (⊤ : Subrepresentation τ.ρ) ≠ ⊥ := by
    intro he
    apply CategoryTheory.id_nonzero τ
    apply (forget (FDRep ℂ G)).map_injective
    ext v
    change v = 0
    have hv : v ∈ (⊥ : Subrepresentation τ.ρ) := he ▸ (show v ∈ (⊤ : Subrepresentation τ.ρ) from trivial)
    exact (Submodule.mem_bot ℂ).mp hv
  refine { exists_pair_ne := ⟨⊤, ⊥, htop⟩, eq_bot_or_eq_top := fun W ↦ ?_ }
  by_cases hW : W = ⊥
  · exact Or.inl hW
  right
  let i : FDRep.of W.toRepresentation ⟶ τ :=
    ⟨InducedCategory.homMk (ModuleCat.ofHom W.toSubmodule.subtype), fun g ↦ by
      ext v
      rfl⟩
  letI : Mono i := ConcreteCategory.mono_of_injective i (fun a b h ↦ Subtype.ext h)
  have hi : i ≠ 0 := by
    intro he
    apply hW
    apply SetLike.ext
    intro v
    constructor
    · intro hv
      have hv0 := congrArg (fun f : FDRep.of W.toRepresentation ⟶ τ ↦ f ⟨v, hv⟩) he
      change v = 0 at hv0
      exact (Submodule.mem_bot ℂ).mpr hv0
    · intro hv
      have hv0 : v = 0 := (Submodule.mem_bot ℂ).mp hv
      subst v
      exact W.toSubmodule.zero_mem
  letI : IsIso i := CategoryTheory.isIso_of_mono_of_nonzero hi
  apply top_unique
  intro v _
  obtain ⟨w, hw⟩ := (ConcreteCategory.bijective_of_isIso i).surjective v
  rw [← hw]
  exact w.property

end HodgeLean.Foundations.Program
