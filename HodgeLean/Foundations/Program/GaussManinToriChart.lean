import HodgeLean.Foundations.Program.GaussManinToriVHS

/-!
# The chart period map of marked period data

In coordinates, `F¹(P) ⊕ \bar F¹(P₀) = H` is the bijectivity of the map
`(a, a') ↦ a P + a' \bar P₀`, an affine family of continuous linear maps in `P`. Invertible maps
form an open set and inversion is analytic there, so the domain of the chart at `b₀` is a
neighbourhood of `b₀`, and the matrix of the projection onto `F¹_b` along `\bar F¹_{b₀}` is a
holomorphic function of `b`. Helper names carry the prefix `d2v_`.
-/

noncomputable section

open scoped TensorProduct ContDiff
open Manifold
namespace HodgeLean.Foundations.Program
open HodgeBlocks

variable {g : ℕ}

/-- The row combination `a ↦ (∑_i a_i P_{ik})_k`, the coordinates of the restriction of the
linear form with coefficients `a` to the lattice.
Source: Birkenhake--Lange, *Complex Abelian Varieties*, 2nd ed., §1.4 (`H^{1,0}` as the row
space of the period matrix). -/
def d2v_rowLin (P : Fin g → Fin (2 * g) → ℂ) : (Fin g → ℂ) →ₗ[ℂ] (Fin (2 * g) → ℂ) where
  toFun a := fun k ↦ ∑ i, a i * P i k
  map_add' a b := by funext k; simp [add_mul, Finset.sum_add_distrib]
  map_smul' c a := by funext k; simp [Finset.mul_sum, mul_assoc]

example (P : Fin g → Fin (2 * g) → ℂ) : d2v_rowLin P 0 = 0 := map_zero _

theorem d2v_evalBilin_eq_rowLin (P : Fin g → Fin (2 * g) → ℂ) (φ : Module.Dual ℂ (Fin g → ℂ)) :
    d2_evalBilin P φ = d2_vec _ (d2v_rowLin P (fun i ↦ φ (Pi.single i 1))) := by
  show d2_vec _ _ = _
  congr 1
  funext k
  rw [d2v_dual_apply]
  simp only [d2v_rowLin, LinearMap.coe_mk, AddHom.coe_mk]
  exact Finset.sum_congr rfl fun i _ ↦ mul_comm _ _

theorem d2v_rowLin_eq_evalBilin (P : Fin g → Fin (2 * g) → ℂ) (a : Fin g → ℂ) :
    d2_vec _ (d2v_rowLin P a) = d2_evalBilin P (∑ i, a i • LinearMap.proj i) := by
  rw [d2v_evalBilin_eq_rowLin]
  congr 2
  funext i
  simp [Pi.single_apply]

theorem d2v_mem_hodgeOne_iff (P : Fin g → Fin (2 * g) → ℂ) (x : ℂ ⊗[ℚ] (Fin (2 * g) → ℚ)) :
    x ∈ d2_hodgeOne P ↔ ∃ a, x = d2_vec _ (d2v_rowLin P a) := by
  constructor
  · rintro ⟨φ, rfl⟩
    exact ⟨_, d2v_evalBilin_eq_rowLin P φ⟩
  · rintro ⟨a, rfl⟩
    rw [d2v_rowLin_eq_evalBilin]
    exact LinearMap.mem_range_self _ _

theorem d2v_rowLin_injective {P : Fin g → Fin (2 * g) → ℂ} (hP : d2_IsPeriodMatrix P) :
    Function.Injective (d2v_rowLin P) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro a ha
  have h := congrArg (d2_vec _) ha
  rw [map_zero, d2v_rowLin_eq_evalBilin, ← map_zero (d2_evalBilin P)] at h
  have h0 := d2v_evalBilin_injective hP h
  funext j
  have := congrArg (fun φ : Module.Dual ℂ (Fin g → ℂ) ↦ φ (Pi.single j 1)) h0
  simpa [Pi.single_apply] using this

variable (P₀ : Fin g → Fin (2 * g) → ℂ)

/-- The map `(a, a') ↦ a P + a' \bar P₀`, bijective exactly when `F¹(P) ⊕ \bar F¹(P₀) = H`.
Source: Griffiths, Publ. Math. IHES 38 (1970), §1 (the chart of the Grassmannian at a
complement); Griffiths--Harris, *Principles of Algebraic Geometry*, ch. 1, §5. -/
def d2v_T (P : Fin g → Fin (2 * g) → ℂ) :
    ((Fin g → ℂ) × (Fin g → ℂ)) →ₗ[ℂ] (Fin (2 * g) → ℂ) :=
  (d2v_rowLin P).coprod (d2v_rowLin (d2v_conj P₀))

example (P : Fin g → Fin (2 * g) → ℂ) : d2v_T P₀ P 0 = 0 := map_zero _

theorem d2v_isCompl_iff {P : Fin g → Fin (2 * g) → ℂ} (hP : d2_IsPeriodMatrix P)
    (hP₀ : d2_IsPeriodMatrix P₀) :
    IsCompl (d2_hodgeOne P) (d2_hodgeOne (d2v_conj P₀)) ↔ Function.Bijective (d2v_T P₀ P) := by
  have hfin : Module.finrank ℂ ((Fin g → ℂ) × (Fin g → ℂ)) =
      Module.finrank ℂ (Fin (2 * g) → ℂ) := by
    simp [Module.finrank_prod, two_mul]
  have hinj := d2v_rowLin_injective hP
  have hinj₀ := d2v_rowLin_injective (d2v_isPeriodMatrix_conj hP₀)
  constructor
  · intro h
    have hi : Function.Injective (d2v_T P₀ P) := by
      rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      rintro ⟨a, a'⟩ ha
      have ha' : d2v_rowLin P a = d2v_rowLin (d2v_conj P₀) (-a') := by
        rw [map_neg, eq_neg_iff_add_eq_zero]; exact ha
      have hx : d2_vec _ (d2v_rowLin P a) = 0 := by
        refine (Submodule.disjoint_def.mp h.disjoint) _ ((d2v_mem_hodgeOne_iff _ _).mpr ⟨a, rfl⟩)
          ((d2v_mem_hodgeOne_iff _ _).mpr ⟨-a', by rw [ha']⟩)
      have ha0 : a = 0 := hinj (by
        rw [map_zero]; exact (d2_vec _).injective (by rw [hx, map_zero]))
      have ha0' : -a' = 0 := hinj₀ (by rw [← ha', ha0, map_zero, map_zero])
      ext <;> simp_all
    exact ⟨hi, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfin).mp hi⟩
  · intro h
    refine ⟨Submodule.disjoint_def.mpr fun x hx hx' ↦ ?_, codisjoint_iff.mpr ?_⟩
    · obtain ⟨a, rfl⟩ := (d2v_mem_hodgeOne_iff _ _).mp hx
      obtain ⟨a', ha'⟩ := (d2v_mem_hodgeOne_iff _ _).mp hx'
      have h0 : d2v_T P₀ P (a, -a') = d2v_T P₀ P 0 := by
        rw [map_zero]
        simp only [d2v_T, LinearMap.coprod_apply, map_neg]
        rw [(d2_vec _).injective ha', add_neg_cancel]
      have := h.1 h0
      simp only [Prod.mk_eq_zero] at this
      rw [this.1, map_zero, map_zero]
    · refine eq_top_iff.mpr fun y _ ↦ ?_
      obtain ⟨c, rfl⟩ := (d2_vec (2 * g)).surjective y
      obtain ⟨⟨a, a'⟩, rfl⟩ := h.2 c
      simp only [d2v_T, LinearMap.coprod_apply, map_add]
      exact Submodule.add_mem_sup ((d2v_mem_hodgeOne_iff _ _).mpr ⟨a, rfl⟩)
        ((d2v_mem_hodgeOne_iff _ _).mpr ⟨a', rfl⟩)


theorem d2v_mem_chartDomainSet_iff (P : Fin g → Fin (2 * g) → ℂ) :
    d2_filtration P ∈ d1_chartDomainSet 1 (d2_filtration P₀) 1 1 ↔
      IsCompl (d2_hodgeOne P) (d2_hodgeOne (d2v_conj P₀)) := by
  have h1 : d2_filtration P 1 = d2_hodgeOne P := by simp [d2_filtration]
  have h2 : d2_filtration P₀ 1 = d2_hodgeOne P₀ := by simp [d2_filtration]
  simp only [d1_chartDomainSet, Set.mem_ofPred_eq, Fin.forall_fin_one, Fin.val_zero,
    Nat.cast_zero, add_zero, sub_self, zero_add, h1, h2, d2v_map_sigmaQ_hodgeOne]

theorem d2v_graphProjection_eq (P : Fin g → Fin (2 * g) → ℂ) (i : Fin 1)
    (h : IsCompl (d2_hodgeOne P) (d2_hodgeOne (d2v_conj P₀)))
    (hb : Function.Bijective (d2v_T P₀ P)) (c : Fin (2 * g) → ℂ) :
    d1_graphProjection 1 (d2_filtration P₀) (d2_filtration P) (1 + i) (d2_vec _ c) =
      d2_vec _ (d2v_rowLin P ((LinearEquiv.ofBijective _ hb).symm c).1) := by
  obtain rfl : i = 0 := Subsingleton.elim _ _
  have h1 : d2_filtration P 1 = d2_hodgeOne P := by simp [d2_filtration]
  have h2 : d2_filtration P₀ 1 = d2_hodgeOne P₀ := by simp [d2_filtration]
  have h' : IsCompl (d2_filtration P (1 + ((0 : Fin 1) : ℤ)))
      ((d2_filtration P₀ (1 - (1 + ((0 : Fin 1) : ℤ)) + 1)).map (sigmaQ _)) := by
    simpa [h1, h2, d2v_map_sigmaQ_hodgeOne] using h
  simp only [d1_graphProjection, h', ↓reduceDIte]
  obtain ⟨ac, hac⟩ : ∃ ac, (LinearEquiv.ofBijective _ hb).symm c = ac := ⟨_, rfl⟩
  have hc : c = d2v_T P₀ P ac := by
    rw [← hac]; exact ((LinearEquiv.ofBijective _ hb).apply_symm_apply c).symm
  rw [hac, hc]
  obtain ⟨a, a'⟩ := ac
  simp only [d2v_T, LinearMap.coprod_apply, map_add, LinearMap.comp_apply,
    Submodule.coe_subtype]
  have hx : d2_vec _ (d2v_rowLin P a) ∈ d2_filtration P (1 + ((0 : Fin 1) : ℤ)) := by
    simpa [h1] using (d2v_mem_hodgeOne_iff _ _).mpr ⟨a, rfl⟩
  have hy : d2_vec _ (d2v_rowLin (d2v_conj P₀) a') ∈
      (d2_filtration P₀ (1 - (1 + ((0 : Fin 1) : ℤ)) + 1)).map (sigmaQ _) := by
    simpa [h2, d2v_map_sigmaQ_hodgeOne] using (d2v_mem_hodgeOne_iff _ _).mpr ⟨a', rfl⟩
  rw [Submodule.projectionOnto_apply_of_mem_left h' hx,
    Submodule.projectionOnto_apply_of_mem_right h' hy, Submodule.coe_zero, add_zero]


/-- The row combination as a linear function of the matrix, with values in continuous linear
maps on the first factor of `ℂ^g × ℂ^g`.
Source: Birkenhake--Lange, *Complex Abelian Varieties*, 2nd ed., §1.4. -/
def d2v_rowLinL : (Fin g → Fin (2 * g) → ℂ) →ₗ[ℂ]
    (((Fin g → ℂ) × (Fin g → ℂ)) →L[ℂ] (Fin (2 * g) → ℂ)) where
  toFun P := LinearMap.toContinuousLinearMap ((d2v_rowLin P).comp (LinearMap.fst ℂ _ _))
  map_add' P Q := by
    refine ContinuousLinearMap.ext fun x ↦ funext fun k ↦ ?_
    simp [d2v_rowLin, mul_add, Finset.sum_add_distrib]
  map_smul' c P := by
    refine ContinuousLinearMap.ext fun x ↦ funext fun k ↦ ?_
    simp [d2v_rowLin, Finset.mul_sum, mul_left_comm]

/-- `d2v_T` as a continuous linear map.
Source: Griffiths, Publ. Math. IHES 38 (1970), §1. -/
def d2v_Tc (P : Fin g → Fin (2 * g) → ℂ) :
    ((Fin g → ℂ) × (Fin g → ℂ)) →L[ℂ] (Fin (2 * g) → ℂ) :=
  LinearMap.toContinuousLinearMap (d2v_T P₀ P)

example : d2v_rowLinL (0 : Fin g → Fin (2 * g) → ℂ) = 0 := map_zero _

example (P : Fin g → Fin (2 * g) → ℂ) : d2v_Tc P₀ P 0 = 0 := map_zero _

theorem d2v_Tc_eq (P : Fin g → Fin (2 * g) → ℂ) :
    d2v_Tc P₀ P = d2v_rowLinL P + LinearMap.toContinuousLinearMap
      ((d2v_rowLin (d2v_conj P₀)).comp (LinearMap.snd ℂ _ _)) := by
  refine ContinuousLinearMap.ext fun x ↦ funext fun k ↦ ?_
  simp [d2v_Tc, d2v_T, d2v_rowLinL]

theorem d2v_Tc_contDiff : ContDiff ℂ ω (d2v_Tc P₀) := by
  have : d2v_Tc P₀ = fun P ↦ LinearMap.toContinuousLinearMap d2v_rowLinL P +
      LinearMap.toContinuousLinearMap ((d2v_rowLin (d2v_conj P₀)).comp (LinearMap.snd ℂ _ _)) := by
    funext P; rw [d2v_Tc_eq]; rfl
  rw [this]
  exact (LinearMap.toContinuousLinearMap d2v_rowLinL).contDiff.add contDiff_const

/-- The matrices `P` for which `d2v_T P₀ P` is bijective: in coordinates, those with
`F¹(P) ⊕ \bar F¹(P₀) = H`.
Source: Griffiths, Publ. Math. IHES 38 (1970), §1; Carlson--Müller-Stach--Peters, ch. 4. -/
def d2v_goodSet : Set (Fin g → Fin (2 * g) → ℂ) := {P | Function.Bijective (d2v_T P₀ P)}

example (P : Fin g → Fin (2 * g) → ℂ) (h : Function.Bijective (d2v_T P₀ P)) :
    P ∈ d2v_goodSet P₀ := h

theorem d2v_goodSet_eq : d2v_goodSet P₀ =
    d2v_Tc P₀ ⁻¹' Set.range ((↑) : (((Fin g → ℂ) × (Fin g → ℂ)) ≃L[ℂ] (Fin (2 * g) → ℂ)) →
      ((Fin g → ℂ) × (Fin g → ℂ)) →L[ℂ] (Fin (2 * g) → ℂ)) := by
  ext P
  simp only [d2v_goodSet, Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_range]
  constructor
  · intro hb
    exact ⟨(LinearEquiv.ofBijective _ hb).toContinuousLinearEquiv, ContinuousLinearMap.ext fun x ↦ rfl⟩
  · rintro ⟨e, he⟩
    have : ⇑(d2v_T P₀ P) = ⇑e := by
      funext x; exact (congrArg (fun L : _ →L[ℂ] _ ↦ L x) he).symm
    rw [this]
    exact e.bijective

theorem d2v_goodSet_isOpen : IsOpen (d2v_goodSet P₀) := by
  rw [d2v_goodSet_eq]
  exact ContinuousLinearEquiv.isOpen.preimage (d2v_Tc_contDiff P₀).continuous

theorem d2v_inverse_Tc {P : Fin g → Fin (2 * g) → ℂ} (hb : Function.Bijective (d2v_T P₀ P))
    (c : Fin (2 * g) → ℂ) :
    (d2v_Tc P₀ P).inverse c = (LinearEquiv.ofBijective _ hb).symm c := by
  have he : d2v_Tc P₀ P = ((LinearEquiv.ofBijective _ hb).toContinuousLinearEquiv :
      ((Fin g → ℂ) × (Fin g → ℂ)) →L[ℂ] (Fin (2 * g) → ℂ)) := ContinuousLinearMap.ext fun x ↦ rfl
  rw [he, ContinuousLinearMap.inverse_equiv]
  rfl

/-- The chart coordinates of `d1_chartCoord` as a function of the matrix: the matrix of the
projection onto `F¹(P)` along `\bar F¹(P₀)`, written with the inverse of `d2v_Tc P₀ P`.
Source: Griffiths, Publ. Math. IHES 38 (1970), §1; Carlson--Müller-Stach--Peters, ch. 4. -/
def d2v_chartFun (P : Fin g → Fin (2 * g) → ℂ) : d2_ChartTarget g :=
  fun _ j k ↦ (Module.finBasis ℂ (ℂ ⊗[ℚ] (Fin (2 * g) → ℚ))).equivFun
    (d2_vec _ (d2v_rowLin P ((d2v_Tc P₀ P).inverse
      ((d2_vec _).symm (Module.finBasis ℂ (ℂ ⊗[ℚ] (Fin (2 * g) → ℚ)) k))).1)) j

example (P : Fin g → Fin (2 * g) → ℂ) : d2_ChartTarget g := d2v_chartFun P₀ P

theorem d2v_chartCoord_eq {P : Fin g → Fin (2 * g) → ℂ}
    (h : IsCompl (d2_hodgeOne P) (d2_hodgeOne (d2v_conj P₀)))
    (hb : Function.Bijective (d2v_T P₀ P)) :
    d1_chartCoord 1 (d2_filtration P₀) 1 1 (d2_filtration P) = d2v_chartFun P₀ P := by
  funext i j k
  rw [d1_chartCoord, LinearMap.toMatrix_apply, d2v_chartFun, Module.Basis.equivFun_apply]
  congr 2
  conv_lhs => rw [← (d2_vec (2 * g)).apply_symm_apply (Module.finBasis ℂ _ k)]
  rw [d2v_graphProjection_eq P₀ P i h hb, d2v_inverse_Tc P₀ hb]

theorem d2v_chartFun_contDiffAt {P : Fin g → Fin (2 * g) → ℂ} (hP : P ∈ d2v_goodSet P₀) :
    ContDiffAt ℂ ω (d2v_chartFun P₀) P := by
  have hinv : ContDiffAt ℂ ω (fun Q ↦ (d2v_Tc P₀ Q).inverse) P := by
    have he : d2v_Tc P₀ P = ((LinearEquiv.ofBijective _ hP).toContinuousLinearEquiv :
        ((Fin g → ℂ) × (Fin g → ℂ)) →L[ℂ] (Fin (2 * g) → ℂ)) := ContinuousLinearMap.ext fun x ↦ rfl
    have h1 := contDiffAt_map_inverse (𝕜 := ℂ) (n := ω)
      (LinearEquiv.ofBijective _ hP).toContinuousLinearEquiv
    rw [← he] at h1
    exact h1.comp P (d2v_Tc_contDiff P₀).contDiffAt
  let L := (((Module.finBasis ℂ (ℂ ⊗[ℚ] (Fin (2 * g) → ℚ))).equivFun.toLinearMap ∘ₗ
    (d2_vec (2 * g)).toLinearMap).toContinuousLinearMap)
  refine contDiffAt_pi.2 fun _ ↦ contDiffAt_pi.2 fun j ↦ contDiffAt_pi.2 fun k ↦ ?_
  have ha : ContDiffAt ℂ ω (fun Q ↦ ((d2v_Tc P₀ Q).inverse
      ((d2_vec _).symm (Module.finBasis ℂ (ℂ ⊗[ℚ] (Fin (2 * g) → ℚ)) k))).1) P :=
    (hinv.clm_apply contDiffAt_const).fst
  have hr : ContDiffAt ℂ ω (fun Q ↦ d2v_rowLin Q ((d2v_Tc P₀ Q).inverse
      ((d2_vec _).symm (Module.finBasis ℂ (ℂ ⊗[ℚ] (Fin (2 * g) → ℚ)) k))).1) P := by
    refine contDiffAt_pi.2 fun l ↦ ?_
    simp only [d2v_rowLin, LinearMap.coe_mk, AddHom.coe_mk]
    refine ContDiffAt.sum fun i _ ↦ (contDiffAt_pi.1 ha i).mul ?_
    exact contDiffAt_pi.1 (contDiffAt_pi.1 contDiffAt_id i) l
  exact contDiffAt_pi.1 (L.contDiff.contDiffAt.comp P hr) j


section Family

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable {B : Type*} [TopologicalSpace B] [ChartedSpace E B]

omit P₀ in
theorem d2v_isCompl_iff_bijective (X : d2_MarkedPeriodFamily E B g) (b₀ b : B) :
    d2_filtration (X.period b) ∈ d1_chartDomainSet 1 (d2_filtration (X.period b₀)) 1 1 ↔
      X.period b ∈ d2v_goodSet (X.period b₀) := by
  rw [d2v_mem_chartDomainSet_iff, d2v_isCompl_iff _ (X.isPeriod b) (X.isPeriod b₀)]
  rfl

omit P₀ in
theorem d2v_mem_chartDomain (X : d2_MarkedPeriodFamily E B g) (b₀ : B) :
    b₀ ∈ d2_chartDomain X b₀ := by
  have hO : IsOpen (X.period ⁻¹' d2v_goodSet (X.period b₀)) :=
    (d2v_goodSet_isOpen _).preimage X.holomorphic.continuous
  refine interior_maximal (fun b hb ↦ (d2v_isCompl_iff_bijective X b₀ b).mpr hb) hO ?_
  show X.period b₀ ∈ d2v_goodSet (X.period b₀)
  rw [← d2v_isCompl_iff_bijective, d2v_mem_chartDomainSet_iff, ← d2v_map_sigmaQ_hodgeOne]
  exact d2v_isCompl_hodgeOne (X.isPeriod b₀)

omit P₀ in
theorem d2v_chartPeriod_holomorphic (X : d2_MarkedPeriodFamily E B g) (b₀ : B) :
    ContMDiffOn 𝓘(ℂ, E) 𝓘(ℂ, d2_ChartTarget g) ω (d2_chartPeriod X b₀)
      (d2_chartDomain X b₀) := by
  have hsub : d2_chartDomain X b₀ ⊆ {b | d2_filtration (X.period b) ∈
      d1_chartDomainSet 1 (d2_filtration (X.period b₀)) 1 1} := interior_subset
  have hmem : ∀ b ∈ d2_chartDomain X b₀, X.period b ∈ d2v_goodSet (X.period b₀) :=
    fun b hb ↦ (d2v_isCompl_iff_bijective X b₀ b).mp (hsub hb)
  have hF : ContDiffOn ℂ ω (d2v_chartFun (X.period b₀)) (d2v_goodSet (X.period b₀)) :=
    fun P hP ↦ (d2v_chartFun_contDiffAt _ hP).contDiffWithinAt
  refine ((contMDiffOn_iff_contDiffOn.mpr hF).comp X.holomorphic.contMDiffOn hmem).congr
    fun b hb ↦ ?_
  have hc := (d2v_mem_chartDomainSet_iff (X.period b₀) (X.period b)).mp (hsub hb)
  exact d2v_chartCoord_eq (X.period b₀) hc (hmem b hb)

end Family

end HodgeLean.Foundations.Program
