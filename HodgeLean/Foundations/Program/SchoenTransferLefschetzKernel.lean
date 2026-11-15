import HodgeLean.Foundations.Program.SchoenTransferComposition
import HodgeLean.Foundations.Program.SchoenTransferKernelRepresentation
import HodgeLean.Foundations.Program.CycleFoundationsZeroSectionProjection
import HodgeLean.Foundations.Program.SchoenTransferPolarization
import HodgeLean.Foundations.Program.CycleFoundationsPullback

/-! Algebraic divisor-power classes pulled back along the group sum. -/
noncomputable section
set_option maxHeartbeats 400000
set_option maxRecDepth 2000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint MonoidalCategory
open scoped CategoryTheory.MonObj
open CategoryTheory.CartesianMonoidalCategory
open HodgeLean.RealDefs HodgeLean.Adapters
attribute [local irreducible] cupProductOf homPullback algebraicCycleClassSpan
namespace HodgeLean.Foundations.Program

/-- The mixed part of the polarization pulled back by the group sum. -/
def s4_mixedPolarization
    (A : Over (Spec ↧ℂ)) [GrpObj A] [IsCommMonObj A]
    [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    (pol : HQ A 2) : HQ (A ⊗ A) 2 :=
  homPullback (fst A A * snd A A) 2 pol -
    homPullback (fst A A) 2 pol - homPullback (snd A A) 2 pol

/-- The mixed polarization is algebraic when the original divisor class is algebraic. -/
theorem s4_mixedPolarization_algebraic
    (A : Over (Spec ↧ℂ)) [GrpObj A] [IsCommMonObj A]
    [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    (pol : HQ A 2) (hpol : pol ∈ cfd_cycleSpan A 1) :
    s4_mixedPolarization A pol ∈ cfd_cycleSpan (A ⊗ A) 1 := by
  letI : IsMonHom (fst A A * snd A A) := by
    rw [Hom.mul_def]
    infer_instance
  exact Submodule.sub_mem _
    (Submodule.sub_mem _
      (cfd_hom_pullback_span A (A ⊗ A) (fst A A * snd A A) 1 pol hpol)
      (cfd_hom_pullback_span A (A ⊗ A) (fst A A) 1 pol hpol))
    (cfd_hom_pullback_span A (A ⊗ A) (snd A A) 1 pol hpol)

theorem s4_algebraic_polarization_power
    (A : Over (Spec ↧ℂ)) [GrpObj A] [IsCommMonObj A]
    [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    (pol : HQ A 2) (hpol : pol ∈ cfd_cycleSpan A 1) (r : ℕ) :
    lefschetzPow A (cupProductOf A) pol r (show 0 + 2 * r = 2 * r by omega)
      (cupUnit A) ∈ cfd_cycleSpan A r := by
  have hm := hc9k_cycleClassMultiplicative A
  have hD : AlgebraicTimesDivisor A (cupProductOf A) pol :=
    { η_mem := hpol
      cup_mem := by
        intro p h a ha
        exact hm.mem_of_eq (p := 1) (q := p) (r := p + 1) h pol a hpol ha }
  exact lefschetzPow_mem_algebraicCycleClassSpan hD r 0 r (by omega)
    (cupUnit A) unitClass_mem_algebraicCycleClassSpan

theorem s4_sum_polarization_power_algebraic
    (A : Over (Spec ↧ℂ)) [GrpObj A] [IsCommMonObj A]
    [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    (pol : HQ A 2) (hpol : pol ∈ cfd_cycleSpan A 1) (r : ℕ) :
    homPullback (fst A A * snd A A) (2 * r)
      (lefschetzPow A (cupProductOf A) pol r (show 0 + 2 * r = 2 * r by omega)
        (cupUnit A)) ∈ cfd_cycleSpan (A ⊗ A) r := by
  letI : IsMonHom (fst A A * snd A A) := by
    rw [Hom.mul_def]
    infer_instance
  exact cfd_hom_pullback_span A (A ⊗ A) (fst A A * snd A A) r _
    (s4_algebraic_polarization_power A pol hpol r)

theorem s4_sum_class_correspondence_top
    (A : Over (Spec ↧ℂ)) [GrpObj A] [IsCommMonObj A]
    [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    (g : ℕ) (hdim : TopologicalSpace.dim A.left = g)
    (I : HQ A (2 * g) ≃ₗ[ℚ] ℚ) (t : HQ A (2 * g)) (ht : I t = 1)
    (r : ℕ) (x : HQ A (2 * r)) :
    cfd_corrAction A A g I r g r (by omega)
      (homPullback (fst A A * snd A A) (2 * r) x) t = x := by
  change cfd_projection A A g I (2 * r)
    ((cupProductOf (A ⊗ A)).cup rfl
      (homPullback (fst A A * snd A A) (2 * r) x)
      (homPullback (snd A A) (2 * g) t)) = x
  rw [← cfd_zero_section_projection A A g hdim I t ht (2 * r),
    ← LinearMap.comp_apply, ← spec_homPullback_comp]
  have hsection : lift (𝟙 A) (1 : A ⟶ A) ≫ (fst A A * snd A A) = 𝟙 A := by
    rw [MonObj.comp_mul, lift_fst, lift_snd, mul_one]
  rw [hsection, spec_homPullback_id, LinearMap.id_apply]

set_option maxHeartbeats 200000

/-- A Lefschetz power is cup product with its value on the unit. -/
theorem s4_lefschetzPow_cup_unit
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (pol : HQ X 2) (r n : ℕ) {m : ℕ} (h : n + 2 * r = m) (x : HQ X n) :
    lefschetzPow X (cupProductOf X) pol r h x =
      (cupProductOf X).cup (show 2 * r + n = m by omega)
        (lefschetzPow X (cupProductOf X) pol r (by omega) (cupUnit X)) x := by
  subst m
  induction r with
  | zero =>
      change x = (cupProductOf X).cup (by omega) (cupUnit X) x
      exact ((cupProductOf X).one_cup x).symm
  | succ r ih =>
      rw [lefschetzPow_succ (cupProductOf X) pol r _ rfl (by omega),
        lefschetzPow_succ (cupProductOf X) pol r _ (show 0 + 2 * r = 2 * r by omega)
          (by omega), ih]
      exact ((cupProductOf X).assoc (show 2 + 2 * r = 2 * (r + 1) by omega)
        (show 2 * r + n = n + 2 * r by omega) (by omega) (by omega) pol
        (lefschetzPow X (cupProductOf X) pol r (by omega) (cupUnit X)) x).symm

/-- Multiplication on the source factor preserves algebraic correspondence kernels. -/
theorem s4_source_lefschetz_kernel_algebraic
    (A : Over (Spec ↧ℂ)) [GrpObj A] [IsCommMonObj A]
    [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    (B : Over (Spec ↧ℂ)) [GrpObj B] [IsCommMonObj B]
    [IsIntegral B.left] [Smooth B.hom] [IsProjective B.hom]
    (pol : HQ B 2) (hpol : pol ∈ cfd_cycleSpan B 1)
    (c r : ℕ) (ξ : HQ (A ⊗ B) (2 * c))
    (hξ : ξ ∈ cfd_cycleSpan (A ⊗ B) c) :
    (cupProductOf (A ⊗ B)).cup (show 2 * c + 2 * r = 2 * (c + r) by omega) ξ
      (homPullback (snd A B) (2 * r)
        (lefschetzPow B (cupProductOf B) pol r (by omega) (cupUnit B))) ∈
      cfd_cycleSpan (A ⊗ B) (c + r) := by
  exact (hc9k_cycleClassMultiplicative (A ⊗ B)).mem (by omega) _ _ hξ
    (cfd_hom_pullback_span B (A ⊗ B) (snd A B) r _
      (s4_algebraic_polarization_power B pol hpol r))

/-- Moving a Lefschetz power from the input into the source factor of the kernel. -/
theorem s4_corrAction_precomp_lefschetz
    (A : Over (Spec ↧ℂ)) [GrpObj A] [IsCommMonObj A]
    [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    (B : Over (Spec ↧ℂ)) [GrpObj B] [IsCommMonObj B]
    [IsIntegral B.left] [Smooth B.hom] [IsProjective B.hom]
    (d : ℕ) (I : HQ B (2 * d) ≃ₗ[ℚ] ℚ)
    (c r p q : ℕ) (h : 2 * c + 2 * (p + r) = 2 * q + 2 * d)
    (ξ : HQ (A ⊗ B) (2 * c)) (pol : HQ B 2) (x : HQ B (2 * p)) :
    cfd_corrAction A B d I (c + r) p q (by omega)
      ((cupProductOf (A ⊗ B)).cup (by omega) ξ
        (homPullback (snd A B) (2 * r)
          (lefschetzPow B (cupProductOf B) pol r (by omega) (cupUnit B)))) x =
      cfd_corrAction A B d I c (p + r) q h ξ
        (lefschetzPow B (cupProductOf B) pol r (by omega) x) := by
  change cfd_projection A B d I (2 * q)
    ((cupProductOf (A ⊗ B)).cup (by omega)
      ((cupProductOf (A ⊗ B)).cup (by omega) ξ
        (homPullback (snd A B) (2 * r)
          (lefschetzPow B (cupProductOf B) pol r (by omega) (cupUnit B))))
      (homPullback (snd A B) (2 * p) x)) = _
  rw [(cupProductOf (A ⊗ B)).assoc (by omega)
    (show 2 * r + 2 * p = 2 * (p + r) by omega) (by omega) h,
    ← spec_homPullback_cup (snd A B) (show 2 * r + 2 * p = 2 * (p + r) by omega)]
  rw [← s4_lefschetzPow_cup_unit B pol r (2 * p) (show 2 * p + 2 * r = 2 * (p + r) by omega) x]
  rfl

/-- Algebraic correspondence operators are stable under composition with an algebraic kernel and a Lefschetz power. -/
theorem s4_lefschetz_algebraic_operator_stable
    (A : Over (Spec ↧ℂ)) [GrpObj A] [IsCommMonObj A]
    [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    (g k : ℕ) (hdim : TopologicalSpace.dim A.left = g) (hk : 2 * k ≤ g)
    (I : HQ A (2 * g) ≃ₗ[ℚ] ℚ) (pol : HQ A 2)
    (hpol : pol ∈ cfd_cycleSpan A 1)
    (κ : HQ (A ⊗ A) (2 * (2 * k))) (hκ : κ ∈ cfd_cycleSpan (A ⊗ A) (2 * k)) :
    let L := lefschetzPow A (cupProductOf A) pol (g - 2 * k)
      (show 2 * k + 2 * (g - 2 * k) = 2 * (g - k) by omega)
    let F := s4_corrActionLinear A A g I (2 * k) (g - k) k (by omega)
    ∀ T ∈ (cfd_cycleSpan (A ⊗ A) (2 * k)).map F,
      ((F κ).comp L).comp T ∈ (cfd_cycleSpan (A ⊗ A) (2 * k)).map F := by
  dsimp only
  let r := g - 2 * k
  have hr : 2 * k + r = g := by dsimp only [r]; omega
  have hpr : k + r = g - k := by dsimp only [r]; omega
  let L := lefschetzPow A (cupProductOf A) pol r
    (show 2 * k + 2 * r = 2 * (g - k) by omega)
  let F := s4_corrActionLinear A A g I (2 * k) (g - k) k (by omega)
  let κ' : HQ (A ⊗ A) (2 * g) :=
    (cupProductOf (A ⊗ A)).cup (by omega) κ
      (homPullback (snd A A) (2 * r)
        (lefschetzPow A (cupProductOf A) pol r (by omega) (cupUnit A)))
  have hκ' : κ' ∈ cfd_cycleSpan (A ⊗ A) g := by
    exact (hc9k_cycleClassMultiplicative (A ⊗ A)).mem_of_eq
      (p := 2 * k) (q := r) (r := g) (by omega) κ _ hκ
      (cfd_hom_pullback_span A (A ⊗ A) (snd A A) r _
        (s4_algebraic_polarization_power A pol hpol r))
  have ha : cfd_corrAction A A g I g k k (by omega) κ' = (F κ).comp L := by
    ext x
    change cfd_projection A A g I (2 * k)
      ((cupProductOf (A ⊗ A)).cup (by omega)
        ((cupProductOf (A ⊗ A)).cup (by omega) κ
          (homPullback (snd A A) (2 * r)
            (lefschetzPow A (cupProductOf A) pol r (by omega) (cupUnit A))))
        (homPullback (snd A A) (2 * k) x)) =
      cfd_projection A A g I (2 * k)
        ((cupProductOf (A ⊗ A)).cup (by omega) κ
          (homPullback (snd A A) (2 * (g - k))
            (lefschetzPow A (cupProductOf A) pol r (by omega) x)))
    rw [(cupProductOf (A ⊗ A)).assoc (by omega)
      (show 2 * r + 2 * k = 2 * (g - k) by omega) (by omega) (by omega),
      ← spec_homPullback_cup (snd A A) (show 2 * r + 2 * k = 2 * (g - k) by omega),
      ← s4_lefschetzPow_cup_unit A pol r (2 * k)
        (show 2 * k + 2 * r = 2 * (g - k) by omega) x]
  intro T hT
  obtain ⟨ξ, hξ, hFξ⟩ := Submodule.mem_map.mp hT
  let K := s4_compositeKernel A A A g I g (2 * k) (2 * k) (by omega) κ' ξ
  have hK : K ∈ cfd_cycleSpan (A ⊗ A) (2 * k) :=
    s4_compositeKernel_mem A A A g hdim I g (2 * k) (2 * k) (by omega) κ' hκ' ξ hξ
  refine Submodule.mem_map.mpr ⟨K, hK, ?_⟩
  have hc := s4_corrAction_composite A A A g g hdim hdim I I
    g (2 * k) (2 * k) (g - k) k k (by omega) (by omega) (by omega) κ' ξ
  change F K = ((F κ).comp L).comp T
  calc
    F K = (cfd_corrAction A A g I g k k (by omega) κ').comp (F ξ) := hc
    _ = ((F κ).comp L).comp T := by rw [ha, hFξ]

/-- An algebraic kernel whose Lefschetz composite is injective supplies an algebraic inverse correspondence. -/
theorem s4_inverse_lefschetz_of_injective_kernel
    (A : Over (Spec ↧ℂ)) [GrpObj A] [IsCommMonObj A]
    [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    (g k : ℕ) (hdim : TopologicalSpace.dim A.left = g) (hk : 2 * k ≤ g)
    (I : HQ A (2 * g) ≃ₗ[ℚ] ℚ) (pol : HQ A 2)
    (hpol : pol ∈ cfd_cycleSpan A 1)
    (κ : HQ (A ⊗ A) (2 * (2 * k))) (hκ : κ ∈ cfd_cycleSpan (A ⊗ A) (2 * k))
    (hinj : Function.Injective
      ((cfd_corrAction A A g I (2 * k) (g - k) k (by omega) κ).comp
        (lefschetzPow A (cupProductOf A) pol (g - 2 * k) (k := 2 * k) (by omega)))) :
    ∃ ξ : HQ (A ⊗ A) (2 * (2 * k)), ξ ∈ cfd_cycleSpan (A ⊗ A) (2 * k) ∧
      ∀ x : HQ A (2 * k),
        cfd_corrAction A A g I (2 * k) (g - k) k (by omega) ξ
          (lefschetzPow A (cupProductOf A) pol (g - 2 * k) (by omega) x) = x := by
  obtain ⟨ξ, hξ, hξL⟩ := s4_algebraic_correspondence_retraction A A g I
    (2 * k) (g - k) k (by omega)
    (lefschetzPow A (cupProductOf A) pol (g - 2 * k) (by omega)) κ hκ
    (s4_lefschetz_algebraic_operator_stable A g k hdim hk I pol hpol κ hκ) hinj
  exact ⟨ξ, hξ, fun x => LinearMap.congr_fun hξL x⟩

/-- The concrete even power of the mixed polarization used as a correspondence kernel. -/
def s4_mixedKernel
    (A : Over (Spec ↧ℂ)) [GrpObj A] [IsCommMonObj A]
    [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    (pol : HQ A 2) (k : ℕ) : HQ (A ⊗ A) (2 * (2 * k)) :=
  lefschetzPow (A ⊗ A) (cupProductOf (A ⊗ A)) (s4_mixedPolarization A pol)
    (2 * k) (by omega) (cupUnit (A ⊗ A))

/-- The mixed kernel is algebraic for an algebraic polarization. -/
theorem s4_mixedKernel_mem
    (A : Over (Spec ↧ℂ)) [GrpObj A] [IsCommMonObj A]
    [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    (pol : HQ A 2) (hpol : pol ∈ cfd_cycleSpan A 1) (k : ℕ) :
    s4_mixedKernel A pol k ∈ cfd_cycleSpan (A ⊗ A) (2 * k) :=
  s4_algebraic_polarization_power (A ⊗ A) (s4_mixedPolarization A pol)
    (s4_mixedPolarization_algebraic A pol hpol) (2 * k)

/-- A nondegenerate polarization has a symplectic basis of the actual first cohomology. -/
theorem s4_polarization_symplectic_basis
    (A : Over (Spec ↧ℂ)) [GrpObj A] [IsCommMonObj A]
    [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    (g : ℕ) (hdim : TopologicalSpace.dim A.left = g) (pol : HQ A 2)
    (hη : HodgeLean.Foundations.Symplectic.IsNondegenerate
      (polarizationVec (torusCohomology_cupProductOf A) pol)) :
    ∃ b : Module.Basis (Fin g ⊕ Fin g) ℚ (HQ A 1),
      polarizationVec (torusCohomology_cupProductOf A) pol =
        HodgeLean.Foundations.Symplectic.sympVec (b ∘ Sum.inl) (b ∘ Sum.inr) := by
  letI := (finiteBetti_abelian A).finite 1
  obtain ⟨d, b, hd, hb⟩ :=
    HodgeLean.Foundations.Symplectic.exists_basis_sympVec_of_isNondegenerate hη
  have hg : Module.finrank ℚ (HQ A 1) = 2 * g := by
    simpa only [hdim] using (torusCohomology_cupProductOf A).finrank_eq
  have he : d = g := by omega
  subst d
  exact ⟨b, hb⟩

/-- The mixed polarization of a degree-one cup product is its alternating cross term. -/
theorem s4_mixedPolarization_cup_one
    (A : Over (Spec ↧ℂ)) [GrpObj A] [IsCommMonObj A]
    [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    (v w : HQ A 1) :
    s4_mixedPolarization A ((cupProductOf A).cup rfl v w) =
      (cupProductOf (A ⊗ A)).cup rfl
        (homPullback (fst A A) 1 v) (homPullback (snd A A) 1 w) -
      (cupProductOf (A ⊗ A)).cup rfl
        (homPullback (fst A A) 1 w) (homPullback (snd A A) 1 v) := by
  have hc := (cupProductOf (A ⊗ A)).graded_comm rfl rfl
    (homPullback (fst A A) 1 w) (homPullback (snd A A) 1 v)
  simp only [Nat.mul_one, pow_one, neg_one_smul] at hc
  unfold s4_mixedPolarization
  simp only [spec_homPullback_cup, spec_homPullback_mul, LinearMap.add_apply,
    map_add]
  rw [hc]
  abel

/-- The polarization is the cup sum attached to its symplectic basis. -/
theorem s4_polarization_eq_basis_sum
    (A : Over (Spec ↧ℂ)) [GrpObj A] [IsCommMonObj A]
    [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    (g : ℕ) (pol : HQ A 2) (b : Module.Basis (Fin g ⊕ Fin g) ℚ (HQ A 1))
    (hb : polarizationVec (torusCohomology_cupProductOf A) pol =
      HodgeLean.Foundations.Symplectic.sympVec (b ∘ Sum.inl) (b ∘ Sum.inr)) :
    pol = ∑ i : Fin g, (cupProductOf A).cup rfl (b (Sum.inl i)) (b (Sum.inr i)) := by
  rw [← cupWedgeMap_polarizationVec (torusCohomology_cupProductOf A) pol,
    hb, HodgeLean.Foundations.Symplectic.sympVec, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [CupProduct.cupWedgeMap_ιMulti, CupProduct.cupMulti_succ _ 1 rfl,
    CupProduct.cupMulti_succ _ 0 rfl, CupProduct.cupMulti_zero, CupProduct.cup_one]
  simp only [Fin.tail, Matrix.cons_val_zero, Matrix.cons_val_succ, Function.comp_apply]

/-- The mixed polarization is a sum of alternating cross terms in a symplectic basis. -/
theorem s4_mixedPolarization_eq_basis_cross
    (A : Over (Spec ↧ℂ)) [GrpObj A] [IsCommMonObj A]
    [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    (g : ℕ) (pol : HQ A 2) (b : Module.Basis (Fin g ⊕ Fin g) ℚ (HQ A 1))
    (hb : polarizationVec (torusCohomology_cupProductOf A) pol =
      HodgeLean.Foundations.Symplectic.sympVec (b ∘ Sum.inl) (b ∘ Sum.inr)) :
    s4_mixedPolarization A pol = ∑ i : Fin g,
      ((cupProductOf (A ⊗ A)).cup rfl
        (homPullback (fst A A) 1 (b (Sum.inl i)))
        (homPullback (snd A A) 1 (b (Sum.inr i))) -
      (cupProductOf (A ⊗ A)).cup rfl
        (homPullback (fst A A) 1 (b (Sum.inr i)))
        (homPullback (snd A A) 1 (b (Sum.inl i)))) := by
  have hh : s4_mixedPolarization A pol = ∑ i : Fin g,
      s4_mixedPolarization A ((cupProductOf A).cup rfl (b (Sum.inl i)) (b (Sum.inr i))) := by
    rw [s4_polarization_eq_basis_sum A g pol b hb]
    simp only [s4_mixedPolarization, map_sum, Finset.sum_sub_distrib]
  rw [hh]
  apply Finset.sum_congr rfl
  intro i _
  exact s4_mixedPolarization_cup_one A (b (Sum.inl i)) (b (Sum.inr i))

/-- Product hard Lefschetz and the pure Künneth bidegree give an injective kernel action. -/
theorem s4_crossKernel_action_injective
    (A : Over (Spec ↧ℂ)) [GrpObj A] [IsCommMonObj A]
    [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    (g k : ℕ) (hdim : TopologicalSpace.dim A.left = g) (hk : k ≤ g)
    (I : HQ A (2 * g) ≃ₗ[ℚ] ℚ) (θ : HQ (A ⊗ A) 2)
    (hθ : θ ∈ LinearMap.range (s4_crossMap A A 1 1 2 rfl))
    (hθnd : HodgeLean.Foundations.Symplectic.IsNondegenerate
      (polarizationVec (torusCohomology_cupProductOf (A ⊗ A)) θ)) :
    Function.Injective
      (cfd_corrAction A A g I (2 * k) (g - k) k (by omega)
        (lefschetzPow (A ⊗ A) (cupProductOf (A ⊗ A)) θ (2 * k) (by omega)
          (cupUnit (A ⊗ A)))) := by
  let κ := lefschetzPow (A ⊗ A) (cupProductOf (A ⊗ A)) θ (2 * k)
    (show 0 + 2 * (2 * k) = 2 * (2 * k) by omega) (cupUnit (A ⊗ A))
  apply (LinearMap.ker_eq_bot).mp
  apply LinearMap.ker_eq_bot'.mpr
  intro x hx
  change cfd_projection A A g I (2 * k)
    ((cupProductOf (A ⊗ A)).cup (by omega) κ
      (homPullback (snd A A) (2 * (g - k)) x)) = 0 at hx
  have hκ := s4_lefschetzPow_mem_cross A A θ hθ (2 * k)
  have hxp : homPullback (snd A A) (2 * (g - k)) x ∈
      LinearMap.range (s4_crossMap A A 0 (2 * (g - k)) (2 * (g - k)) (by omega)) := by
    refine LinearMap.mem_range.mpr ⟨cupUnit A ⊗ₜ[ℚ] x, ?_⟩
    rw [s4_crossMap_tmul, spec_homPullback_unit]
    exact (cupProductOf (A ⊗ A)).one_cup (homPullback (snd A A) (2 * (g - k)) x)
  have hpure := s4_crossMap_cup_mem A A (2 * k) (2 * k) 0 (2 * (g - k))
    (2 * (2 * k)) (2 * (g - k)) (2 * k) (2 * g) (2 * k + 2 * g)
    (by omega) (by omega) (by omega) (by omega) (by omega)
    κ (homPullback (snd A A) (2 * (g - k)) x) hκ hxp
  have hzero := s4_projection_zero_on_cross A A g hdim I (2 * k) _ hpure hx
  have hdimAA : TopologicalSpace.dim (A ⊗ A).left = 2 * g := by
    rw [cp_product_dim, hdim]
    omega
  have hr : TopologicalSpace.dim (A ⊗ A).left - 2 * (g - k) = 2 * k := by
    rw [hdimAA]
    omega
  let L := lefschetzPow (A ⊗ A) (cupProductOf (A ⊗ A)) θ (2 * k)
    (k := 2 * (g - k)) (m := 2 * k + 2 * g) (by omega)
  have hL := (hardLefschetz_abelian (A ⊗ A) hθnd).bijective
    (k := 2 * (g - k)) (m := 2 * k + 2 * g)
    (by rw [hdimAA]; omega) (by rw [hdimAA]; omega)
  have hLi : Function.Injective L := by
    simpa only [hr] using hL.1
  have hLzero : L (homPullback (snd A A) (2 * (g - k)) x) = 0 := by
    change lefschetzPow (A ⊗ A) (cupProductOf (A ⊗ A)) θ (2 * k)
      (show 2 * (g - k) + 2 * (2 * k) = 2 * k + 2 * g by omega)
      (homPullback (snd A A) (2 * (g - k)) x) = 0
    rw [s4_lefschetzPow_cup_unit (A ⊗ A) θ (2 * k) (2 * (g - k))
      (show 2 * (g - k) + 2 * (2 * k) = 2 * k + 2 * g by omega)]
    exact hzero
  have hpzero : homPullback (snd A A) (2 * (g - k)) x = 0 :=
    hLi (hLzero.trans L.map_zero.symm)
  have hpi := spec_homPullback_section (snd A A)
    (lift (1 : A ⟶ A) (𝟙 A)) (lift_snd _ _) (2 * (g - k))
  calc
    x = homPullback (lift (1 : A ⟶ A) (𝟙 A)) (2 * (g - k))
        (homPullback (snd A A) (2 * (g - k)) x) := (LinearMap.congr_fun hpi x).symm
    _ = 0 := by rw [hpzero, map_zero]

/-- The mixed polarization lies in Künneth bidegree (1,1). -/
theorem s4_mixedPolarization_mem_cross
    (A : Over (Spec ↧ℂ)) [GrpObj A] [IsCommMonObj A]
    [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    (g : ℕ) (hdim : TopologicalSpace.dim A.left = g) (pol : HQ A 2)
    (hη : HodgeLean.Foundations.Symplectic.IsNondegenerate
      (polarizationVec (torusCohomology_cupProductOf A) pol)) :
    s4_mixedPolarization A pol ∈ LinearMap.range (s4_crossMap A A 1 1 2 rfl) := by
  obtain ⟨b, hb⟩ := s4_polarization_symplectic_basis A g hdim pol hη
  rw [s4_mixedPolarization_eq_basis_cross A g pol b hb]
  apply Submodule.sum_mem
  intro i _
  apply Submodule.sub_mem
  · exact LinearMap.mem_range.mpr ⟨b (Sum.inl i) ⊗ₜ[ℚ] b (Sum.inr i), rfl⟩
  · exact LinearMap.mem_range.mpr ⟨b (Sum.inr i) ⊗ₜ[ℚ] b (Sum.inl i), rfl⟩

/-- The mixed polarization is nondegenerate on the first cohomology of the product. -/
theorem s4_mixedPolarization_nondegenerate
    (A : Over (Spec ↧ℂ)) [GrpObj A] [IsCommMonObj A]
    [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    (g : ℕ) (hdim : TopologicalSpace.dim A.left = g) (pol : HQ A 2)
    (hη : HodgeLean.Foundations.Symplectic.IsNondegenerate
      (polarizationVec (torusCohomology_cupProductOf A) pol)) :
    HodgeLean.Foundations.Symplectic.IsNondegenerate
      (polarizationVec (torusCohomology_cupProductOf (A ⊗ A)) (s4_mixedPolarization A pol)) := by
  letI := (finiteBetti_abelian (A ⊗ A)).finite 1
  obtain ⟨b, hb⟩ := s4_polarization_symplectic_basis A g hdim pol hη
  let ε : (Fin g ⊕ Fin g) → ℚˣ := Sum.elim (fun _ => 1) (fun _ => -1)
  let c := (b.reindex (Equiv.sumComm (Fin g) (Fin g))).unitsSMul ε
  have hcL (i : Fin g) : c (Sum.inl i) = b (Sum.inr i) := by
    dsimp only [c]
    rw [Module.Basis.unitsSMul_apply]
    simp only [ε, Sum.elim_inl, one_smul]
    rw [Module.Basis.reindex_apply]
    rfl
  have hcR (i : Fin g) : c (Sum.inr i) = -b (Sum.inl i) := by
    dsimp only [c]
    rw [Module.Basis.unitsSMul_apply]
    simp only [ε, Sum.elim_inr, Units.neg_smul, one_smul]
    rw [Module.Basis.reindex_apply]
    rfl
  let e : (Fin g ⊕ Fin g) ≃ Fin (g + g) := finSumFinEquiv
  let b₀ := b.reindex e
  let c₀ := c.reindex e
  let D := (b₀.prod c₀).map (cp_H1Equiv A A)
  have hDL (i : Fin (g + g)) : D (Sum.inl i) = homPullback (fst A A) 1 (b₀ i) := by
    dsimp only [D]
    rw [Module.Basis.map_apply]
    change homPullback (fst A A) 1 ((b₀.prod c₀ (Sum.inl i)).1) +
      homPullback (snd A A) 1 ((b₀.prod c₀ (Sum.inl i)).2) = _
    rw [Module.Basis.prod_apply_inl_fst, Module.Basis.prod_apply_inl_snd, map_zero, add_zero]
  have hDR (i : Fin (g + g)) : D (Sum.inr i) = homPullback (snd A A) 1 (c₀ i) := by
    dsimp only [D]
    rw [Module.Basis.map_apply]
    change homPullback (fst A A) 1 ((b₀.prod c₀ (Sum.inr i)).1) +
      homPullback (snd A A) 1 ((b₀.prod c₀ (Sum.inr i)).2) = _
    rw [Module.Basis.prod_apply_inr_fst, Module.Basis.prod_apply_inr_snd, map_zero, zero_add]
  let ρ := (cupProductOf (A ⊗ A)).cupWedgeMap 2
    (HodgeLean.Foundations.Symplectic.sympVec (D ∘ Sum.inl) (D ∘ Sum.inr))
  have hρ : polarizationVec (torusCohomology_cupProductOf (A ⊗ A)) ρ =
      HodgeLean.Foundations.Symplectic.sympVec (D ∘ Sum.inl) (D ∘ Sum.inr) := by
    unfold polarizationVec
    change ((torusCohomology_cupProductOf (A ⊗ A)).cupWedgeEquiv 2).symm
      (((torusCohomology_cupProductOf (A ⊗ A)).cupWedgeEquiv 2)
        (HodgeLean.Foundations.Symplectic.sympVec (D ∘ Sum.inl) (D ∘ Sum.inr))) = _
    exact LinearEquiv.symm_apply_apply _ _
  have hρφ : ρ = s4_mixedPolarization A pol := by
    rw [s4_polarization_eq_basis_sum (A ⊗ A) (g + g) ρ D hρ]
    simp_rw [hDL, hDR]
    rw [← e.sum_comp (fun i : Fin (g + g) => (cupProductOf (A ⊗ A)).cup rfl
      (homPullback (fst A A) 1 (b₀ i)) (homPullback (snd A A) 1 (c₀ i)))]
    simp only [b₀, c₀, Module.Basis.reindex_apply, Equiv.symm_apply_apply]
    rw [Fintype.sum_sum_type]
    simp only [hcL, hcR, map_neg, Finset.sum_neg_distrib]
    rw [s4_mixedPolarization_eq_basis_cross A g pol b hb]
    simp only [sub_eq_add_neg, Finset.sum_add_distrib, Finset.sum_neg_distrib]
  rw [← hρφ, hρ]
  exact HodgeLean.Foundations.Symplectic.isNondegenerate_sympVec_basis D

/-- The actual mixed-polarization kernel acts injectively in complementary even degrees. -/
theorem s4_mixedKernel_action_injective
    (A : Over (Spec ↧ℂ)) [GrpObj A] [IsCommMonObj A]
    [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    (g k : ℕ) (hdim : TopologicalSpace.dim A.left = g) (hk : k ≤ g)
    (I : HQ A (2 * g) ≃ₗ[ℚ] ℚ) (pol : HQ A 2)
    (hη : HodgeLean.Foundations.Symplectic.IsNondegenerate
      (polarizationVec (torusCohomology_cupProductOf A) pol)) :
    Function.Injective
      (cfd_corrAction A A g I (2 * k) (g - k) k (by omega) (s4_mixedKernel A pol k)) :=
  s4_crossKernel_action_injective A g k hdim hk I (s4_mixedPolarization A pol)
    (s4_mixedPolarization_mem_cross A g hdim pol hη)
    (s4_mixedPolarization_nondegenerate A g hdim pol hη)

end HodgeLean.Foundations.Program
