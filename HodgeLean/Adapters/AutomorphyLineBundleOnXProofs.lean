import HodgeLean.Adapters.AutomorphyLineBundleOnXDefs
import HodgeLean.Adapters.UniformizationBiholomorphic
import HodgeLean.Foundations.AutomorphyLineBundle
import HodgeLean.Foundations.AppellHumbertSections

/-! # Proof obligations for the line bundle `L(H, χ)` on `X(ℂ)`

One obligation per statement of `HodgeLean.Adapters.AutomorphyLineBundleOnX`. All twelve are proved, by three parallel provers.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
open HodgeLean.Foundations HodgeLean.Foundations.AppellHumbert
open HodgeLean.Foundations.AutomorphyLineBundle
open scoped Manifold CategoryTheory.MonObj

namespace HodgeLean.Adapters

section General

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]

theorem spec_sections_eq_bot_of_hermitian_zero_aux (D : Datum (V := V))
    (hH : ∀ x y, D.hermitian.toFun x y = 0) (hχ : ∃ l, D.semicharacter l ≠ 1) :
    sections D = ⊥ := by
  have hfac : ∀ l v, holFactor D l v = D.semicharacter l := fun l v ↦ by
    simp [holFactor, hH]
  rw [eq_bot_iff]
  rintro θ ⟨hd, hfe⟩
  rw [Submodule.mem_bot]
  have hper : ∀ (l : D.lattice) v, ‖θ (v + l)‖ = ‖θ v‖ := fun l v ↦ by
    rw [hfe l v, hfac l v, norm_mul, Circle.norm_coe, one_mul]
  have : Module.Free ℤ D.lattice := ZLattice.module_free ℝ D.lattice
  have : Module.Finite ℤ D.lattice := ZLattice.module_finite ℝ D.lattice
  let b := (Module.Free.chooseBasis ℤ D.lattice).ofZLatticeBasis ℝ D.lattice
  have hspan : Submodule.span ℤ (Set.range b) = D.lattice :=
    Module.Basis.ofZLatticeBasis_span ℝ D.lattice _
  have hK : IsCompact (closure (ZSpan.fundamentalDomain b)) :=
    (ZSpan.fundamentalDomain_isBounded b).isCompact_closure
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hd.continuous.continuousOn
  have hall : ∀ v, ‖θ v‖ = ‖θ (ZSpan.fract b v)‖ := by
    intro v
    have hm : (ZSpan.floor b v : V) ∈ D.lattice := hspan.le (ZSpan.floor b v).2
    rw [ZSpan.fract_apply]
    conv_lhs => rw [← sub_add_cancel v (ZSpan.floor b v : V)]
    exact hper ⟨_, hm⟩ _
  have hb : Bornology.IsBounded (Set.range θ) := by
    rw [isBounded_iff_forall_norm_le]
    refine ⟨C, ?_⟩
    rintro _ ⟨v, rfl⟩
    rw [hall]
    exact hC _ (subset_closure (ZSpan.fract_mem_fundamentalDomain b v))
  have hc : ∀ v, θ v = θ 0 := fun v ↦ hd.apply_eq_apply_of_bounded hb v 0
  obtain ⟨l, hl⟩ := hχ
  have h0 : θ 0 = 0 := by
    have h := hfe l 0
    rw [hc, hc 0, hfac] at h
    by_contra hne
    exact hl (Circle.coe_injective (by
      simpa using (mul_eq_right₀ hne).1 h.symm))
  funext v
  rw [hc, h0]; rfl

/-- The imaginary part of a Hermitian form as an `ℝ`-linear function of its first argument.

Source: Birkenhake--Lange, *Complex Abelian Varieties*, 2nd ed., Lemma 1.3.1. -/
def hermitianImaginaryLeft (H : HermitianForm (V := V)) (w : V) : V →ₗ[ℝ] ℝ where
  toFun v := H.imaginary v w
  map_add' x y := by simp only [HermitianForm.imaginary, H.add_left, Complex.add_im]
  map_smul' r x := by
    simp only [HermitianForm.imaginary, RingHom.id_apply, smul_eq_mul]
    rw [← Complex.coe_smul, H.smul_left]
    simp

example (H : HermitianForm (V := V)) (v w : V) :
    hermitianImaginaryLeft H w v = H.imaginary v w := rfl

/-- The imaginary part of a Hermitian form as an `ℝ`-linear function of its second argument.

Source: Birkenhake--Lange, *Complex Abelian Varieties*, 2nd ed., Lemma 1.3.1. -/
def hermitianImaginaryRight (H : HermitianForm (V := V)) (v : V) : V →ₗ[ℝ] ℝ where
  toFun w := H.imaginary v w
  map_add' x y := by simp only [HermitianForm.imaginary, H.add_right, Complex.add_im]
  map_smul' r x := by
    simp only [HermitianForm.imaginary, RingHom.id_apply, smul_eq_mul]
    rw [← Complex.coe_smul, H.smul_right]
    simp

example (H : HermitianForm (V := V)) (v w : V) :
    hermitianImaginaryRight H v w = H.imaginary v w := rfl

theorem spec_exists_twist_semicharacter_aux (D : Datum (V := V))
    (hH : D.hermitian.IsPositiveDefinite) (ψ : D.lattice → Circle)
    (hψ : ∀ l m, ψ (l + m) = ψ l * ψ m) :
    ∃ w : V, ∀ l, (D.twist w).semicharacter l = D.semicharacter l * ψ l := by
  have : Module.Free ℤ D.lattice := ZLattice.module_free ℝ D.lattice
  have : Module.Finite ℤ D.lattice := ZLattice.module_finite ℝ D.lattice
  let b' := Module.Free.chooseBasis ℤ D.lattice
  let b := b'.ofZLatticeBasis ℝ D.lattice
  let Φ : V →ₗ[ℝ] (Module.Free.ChooseBasisIndex ℤ D.lattice → ℝ) :=
    LinearMap.pi fun i ↦ hermitianImaginaryRight D.hermitian (b i)
  have hinj : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro w hw
    rw [LinearMap.mem_ker] at hw
    rw [Submodule.mem_bot]
    have h0 : hermitianImaginaryLeft D.hermitian w = 0 := b.ext fun i ↦ congrFun hw i
    refine spec_positive_imaginary_nondegenerate D.hermitian hH w fun v ↦ ?_
    have h := LinearMap.congr_fun h0 v
    change D.hermitian.imaginary v w = 0 at h
    simp only [HermitianForm.imaginary] at h ⊢
    rw [← D.hermitian.conj_symm, Complex.star_def, Complex.conj_im, h, neg_zero]
  have hsurj : Function.Surjective Φ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (by rw [Module.finrank_eq_card_basis b, Module.finrank_fintype_fun_eq_card])).1 hinj
  choose s hs using fun i ↦ Circle.exp_surjective (ψ (b' i))
  obtain ⟨w, hw⟩ := hsurj fun i ↦ s i / (2 * Real.pi)
  refine ⟨w, fun l ↦ ?_⟩
  let f₁ : D.lattice →+ Additive Circle :=
    AddMonoidHom.mk' (fun l ↦ Additive.ofMul (ψ l)) fun l m ↦ by rw [hψ]; rfl
  let f₂ : D.lattice →+ Additive Circle :=
    AddMonoidHom.mk'
      (fun l ↦ Additive.ofMul (Circle.exp (2 * Real.pi * D.hermitian.imaginary l w)))
      fun l m ↦ by
        rw [← ofMul_mul, ← Circle.exp_add]
        congr 2
        simp only [HermitianForm.imaginary, Submodule.coe_add, D.hermitian.add_left,
          Complex.add_im]
        ring
  have hf : f₁.toIntLinearMap = f₂.toIntLinearMap := by
    refine b'.ext fun i ↦ ?_
    change Additive.ofMul (ψ (b' i)) =
      Additive.ofMul (Circle.exp (2 * Real.pi * D.hermitian.imaginary (b' i) w))
    have hi := congrFun hw i
    change D.hermitian.imaginary (b i) w = s i / (2 * Real.pi) at hi
    rw [Module.Basis.ofZLatticeBasis_apply] at hi
    rw [hi, mul_div_cancel₀ _ (by positivity), hs]
  have hl := LinearMap.congr_fun hf l
  change Additive.ofMul (ψ l) =
    Additive.ofMul (Circle.exp (2 * Real.pi * D.hermitian.imaginary l w)) at hl
  change D.semicharacter l * Circle.exp (2 * Real.pi * D.hermitian.imaginary l w) = _
  rw [← Additive.ofMul.injective hl]

theorem spec_sections_twist_ne_bot_aux (D : Datum (V := V))
    (hH : D.hermitian.IsPositiveDefinite) (hD : sections D ≠ ⊥) (ψ : D.lattice → Circle)
    (hψ : ∀ l m, ψ (l + m) = ψ l * ψ m) :
    ∃ w : V, (∀ l, (D.twist w).semicharacter l = D.semicharacter l * ψ l) ∧
      sections (D.twist w) ≠ ⊥ := by
  obtain ⟨w, hw⟩ := spec_exists_twist_semicharacter_aux D hH ψ hψ
  refine ⟨w, hw, ?_⟩
  obtain ⟨θ, hθ, hne⟩ := (Submodule.ne_bot_iff _).1 hD
  obtain ⟨v, hv⟩ : ∃ v, θ v ≠ 0 := by
    by_contra h
    push Not at h
    exact hne (funext h)
  rw [Submodule.ne_bot_iff]
  refine ⟨_, spec_sections_translate D w θ hθ, fun h ↦ ?_⟩
  have h' := congrFun h (v - w)
  simp only [sub_add_cancel, Pi.zero_apply, mul_eq_zero, Complex.exp_ne_zero, false_or] at h'
  exact hv h'

end General

variable (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left]
  [Smooth X.hom] [IsProjective X.hom]

theorem abelianExp_preimage_eq_proj_preimage (U : Set (ComplexPoint X)) :
    abelianExp X ⁻¹' U = proj (abelianPeriodLattice X) ⁻¹'
      (proj (abelianPeriodLattice X) '' (abelianExp X ⁻¹' U)) := by
  ext y
  refine ⟨fun hy ↦ Set.mem_image_of_mem _ hy, ?_⟩
  rintro ⟨x, hx, hxy⟩
  have hl : y - x ∈ abelianPeriodLattice X := by
    have := (QuotientAddGroup.eq (s := (abelianPeriodLattice X).toAddSubgroup)).mp hxy
    rwa [neg_add_eq_sub] at this
  have : y = x + (⟨y - x, hl⟩ : abelianPeriodLattice X) := by simp
  change abelianExp X y ∈ U
  rw [this, abelianExp_add_lattice]; exact hx

/-- Sections of `L(a)` on `X(ℂ)` over `U` and stage-1 sections over any `S` with the same
preimage in `ℂ^g`, by the identity on values.

Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., §1.1 and §2.1;
`AutomorphyLineBundle.sectionsOn`. -/
def sectionsOnXEquiv (a : abelianPeriodLattice X → (Fin (dim X.left) → ℂ) → ℂ)
    (U : Set (ComplexPoint X)) (S : Set (Torus (abelianPeriodLattice X)))
    (h : abelianExp X ⁻¹' U = proj (abelianPeriodLattice X) ⁻¹' S) :
    sectionsOnX X a U ≃ₗ[ℂ] sectionsOn (abelianPeriodLattice X) a S where
  toFun f := ⟨fun x ↦ (f : abelianExp X ⁻¹' U → ℂ) ⟨x, by rw [h]; exact x.2⟩, by
    obtain ⟨⟨F, hF, hfF⟩, heq⟩ := f.2
    exact ⟨⟨F, by rw [← h]; exact hF, fun x ↦ hfF _⟩,
      fun l x ↦ heq l ⟨x, by rw [h]; exact x.2⟩⟩⟩
  invFun g := ⟨fun x ↦ (g : proj (abelianPeriodLattice X) ⁻¹' S → ℂ)
    ⟨x, by rw [← h]; exact x.2⟩, by
    obtain ⟨⟨F, hF, hfF⟩, heq⟩ := g.2
    exact ⟨⟨F, by rw [h]; exact hF, fun x ↦ hfF _⟩,
      fun l x ↦ heq l ⟨x, by rw [← h]; exact x.2⟩⟩⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

example (a : abelianPeriodLattice X → (Fin (dim X.left) → ℂ) → ℂ) (f : sectionsOnX X a Set.univ)
    (x : proj (abelianPeriodLattice X) ⁻¹' Set.univ) :
    (sectionsOnXEquiv X a Set.univ Set.univ rfl f :
      proj (abelianPeriodLattice X) ⁻¹' Set.univ → ℂ) x =
      (f : abelianExp X ⁻¹' Set.univ → ℂ) ⟨x, Set.mem_univ _⟩ := rfl

theorem spec_sectionsOnX_equiv_aux (a : abelianPeriodLattice X → (Fin (dim X.left) → ℂ) → ℂ)
    (U : Set (ComplexPoint X)) :
    ∃ e : sectionsOnX X a U ≃ₗ[ℂ]
        sectionsOn (abelianPeriodLattice X) a
          (proj (abelianPeriodLattice X) '' (abelianExp X ⁻¹' U)),
      ∀ f (x : abelianExp X ⁻¹' U),
        (e f : proj (abelianPeriodLattice X) ⁻¹'
            (proj (abelianPeriodLattice X) '' (abelianExp X ⁻¹' U)) → ℂ)
          ⟨x, Set.mem_image_of_mem _ x.2⟩ = (f : abelianExp X ⁻¹' U → ℂ) x :=
  ⟨sectionsOnXEquiv X a U _ (abelianExp_preimage_eq_proj_preimage X U), fun _ _ ↦ rfl⟩

theorem continuous_abelianExp : Continuous (abelianExp X) := by
  let : IsCommMonObj X := isCommMonObj_of_complexSelfProductIntegral X
    (complexSelfProductIntegral_of_isIntegral X)
  exact continuous_complexExponential X (dim X.left)

theorem spec_presheafX_isSheaf_aux (a : abelianPeriodLattice X → (Fin (dim X.left) → ℂ) → ℂ) :
    TopCat.Presheaf.IsSheaf (presheafX X a) := by
  refine TopCat.Presheaf.isSheaf_of_isSheafUniqueGluing_types _ fun _ U sf hsf ↦ ?_
  let f : ∀ i, abelianExp X ⁻¹' (U i : Set (ComplexPoint X)) → ℂ := fun i ↦
    (show sectionsOnX X a (U i : Set (ComplexPoint X)) from sf i).1
  have hf : ∀ i, f i ∈ sectionsOnX X a (U i : Set (ComplexPoint X)) := fun i ↦
    (show sectionsOnX X a (U i : Set (ComplexPoint X)) from sf i).2
  have hcompat : ∀ i j (x : Fin (dim X.left) → ℂ) (hi : abelianExp X x ∈ (U i : Set _))
      (hj : abelianExp X x ∈ (U j : Set _)), f i ⟨x, hi⟩ = f j ⟨x, hj⟩ := fun i j x hi hj ↦
    congrArg (fun t : sectionsOnX X a ((U i ⊓ U j : Opens _) : Set (ComplexPoint X)) ↦
      (t : abelianExp X ⁻¹' ((U i ⊓ U j : Opens _) : Set (ComplexPoint X)) → ℂ)
        ⟨x, ⟨hi, hj⟩⟩) (hsf i j)
  have hcov : ∀ x : abelianExp X ⁻¹' ((iSup U : Opens _) : Set (ComplexPoint X)),
      ∃ i, abelianExp X x ∈ (U i : Set (ComplexPoint X)) := fun x ↦ Opens.mem_iSup.mp x.2
  let s : abelianExp X ⁻¹' ((iSup U : Opens _) : Set (ComplexPoint X)) → ℂ := fun x ↦
    f (hcov x).choose ⟨x, (hcov x).choose_spec⟩
  have hs : ∀ i (x : abelianExp X ⁻¹' ((iSup U : Opens _) : Set (ComplexPoint X)))
      (hx : abelianExp X x ∈ (U i : Set (ComplexPoint X))), s x = f i ⟨x, hx⟩ :=
    fun i x hx ↦ hcompat _ _ _ _ _
  have hmem : ∀ i (x : Fin (dim X.left) → ℂ), abelianExp X x ∈ (U i : Set (ComplexPoint X)) →
      abelianExp X x ∈ ((iSup U : Opens _) : Set (ComplexPoint X)) := fun i x hx ↦
    Opens.mem_iSup.mpr ⟨i, hx⟩
  have hsec : s ∈ sectionsOnX X a ((iSup U : Opens _) : Set (ComplexPoint X)) := by
    classical
    refine ⟨⟨fun v ↦ if h : abelianExp X v ∈ ((iSup U : Opens _) : Set (ComplexPoint X))
        then s ⟨v, h⟩ else 0, fun x hx ↦ ?_, fun x ↦ by
        beta_reduce
        split_ifs with h
        · rfl
        · exact absurd x.2 h⟩, fun l x ↦ ?_⟩
    · obtain ⟨i, hi⟩ := hcov ⟨x, hx⟩
      obtain ⟨⟨F, hF, hfF⟩, -⟩ := hf i
      have hO : IsOpen (abelianExp X ⁻¹' (U i : Set (ComplexPoint X))) :=
        (U i).isOpen.preimage (continuous_abelianExp X)
      have hnhds := hO.mem_nhds hi
      refine ((hF.differentiableAt hnhds).congr_of_eventuallyEq ?_).differentiableWithinAt
      filter_upwards [hnhds] with y hy
      split_ifs with h
      · rw [hs i ⟨y, h⟩ hy]; exact hfF ⟨y, hy⟩
      · exact absurd (hmem i y hy) h
    · obtain ⟨i, hi⟩ := hcov x
      have hi' : abelianExp X ((x : Fin (dim X.left) → ℂ) + l) ∈ (U i : Set (ComplexPoint X)) := by
        rw [abelianExp_add_lattice]; exact hi
      exact (hs i ⟨(x : Fin (dim X.left) → ℂ) + l, hmem i _ hi'⟩ hi').trans
        (((hf i).2 l ⟨x, hi⟩).trans (congrArg _ (hs i x hi).symm))
  refine ⟨⟨s, hsec⟩, fun i ↦ Subtype.ext (funext fun x ↦ hs i ⟨x, hmem i x x.2⟩ x.2), fun t ht ↦
    Subtype.ext (funext fun x ↦ ?_)⟩
  obtain ⟨i, hi⟩ := hcov x
  refine (congrArg (fun t : sectionsOnX X a (U i : Set (ComplexPoint X)) ↦
    (t : abelianExp X ⁻¹' (U i : Set (ComplexPoint X)) → ℂ) ⟨x, hi⟩) (ht i)).trans ?_
  exact (hs i x hi).symm

theorem spec_globalSectionsX_aux (H : HermitianForm (V := Fin (dim X.left) → ℂ))
    (E : abelianPeriodLattice X →+ abelianPeriodLattice X →+ ℤ)
    (hE : ∀ l m : abelianPeriodLattice X, (E l m : ℝ) = H.imaginary l m)
    (χ : abelianPeriodLattice X → Circle)
    (hχ : ∀ l m : abelianPeriodLattice X,
      χ (l + m) = χ l * χ m * Circle.exp (Real.pi * H.imaginary l m)) :
    ∃ e : sectionsOnX X (holFactor (datumOfX X H E hE χ hχ)) Set.univ ≃ₗ[ℂ]
        sections (datumOfX X H E hE χ hχ),
      ∀ f (v : Fin (dim X.left) → ℂ),
        (e f : (Fin (dim X.left) → ℂ) → ℂ) v =
          (f : abelianExp X ⁻¹' Set.univ → ℂ) ⟨v, Set.mem_univ _⟩ := by
  obtain ⟨e, he⟩ := spec_appellHumbert_globalSections (datumOfX X H E hE χ hχ)
  exact ⟨(sectionsOnXEquiv X _ Set.univ Set.univ rfl).trans e, fun f v ↦ he _ v⟩

theorem isOpenMap_abelianExp : IsOpenMap (abelianExp X) := by
  let : IsCommMonObj X := isCommMonObj_of_complexSelfProductIntegral X
    (complexSelfProductIntegral_of_isIntegral X)
  exact isOpenMap_complexExponential X (dim X.left)

theorem surjective_abelianExp : Function.Surjective (abelianExp X) := by
  let : IsCommMonObj X := isCommMonObj_of_complexSelfProductIntegral X
    (complexSelfProductIntegral_of_isIntegral X)
  exact surjective_complexExponential X (dim X.left)

theorem sub_mem_of_abelianExp_eq {x y : Fin (dim X.left) → ℂ}
    (h : abelianExp X x = abelianExp X y) : y - x ∈ abelianPeriodLattice X := by
  let : IsCommMonObj X := isCommMonObj_of_complexSelfProductIntegral X
    (complexSelfProductIntegral_of_isIntegral X)
  change complexExponentialHom X (dim X.left) (y - x) = 0
  have h' : complexExponentialHom X (dim X.left) x = complexExponentialHom X (dim X.left) y :=
    Additive.toMul.injective h
  rw [map_sub, h', sub_self]

theorem mdifferentiableAt_of_abelianExp
    (F : ComplexPoint X → ℂ) (G : (Fin (dim X.left) → ℂ) → ℂ) (O : Set (Fin (dim X.left) → ℂ))
    (hO : IsOpen O) (hG : DifferentiableOn ℂ G O) (hFG : ∀ w ∈ O, F (abelianExp X w) = G w)
    {v : Fin (dim X.left) → ℂ} (hv : v ∈ O) :
    MDifferentiableAt 𝓘(ℂ, Fin (dim X.left) → ℂ) 𝓘(ℂ, ℂ) F (abelianExp X v) := by
  let : IsCommMonObj X := isCommMonObj_of_complexSelfProductIntegral X
    (complexSelfProductIntegral_of_isIntegral X)
  obtain ⟨e, hve, heq, hs⟩ := spec_complexExponential_localBiholomorph X (dim X.left) v
  have hexp : abelianExp X v = e v := heq hve
  have hsymm : e.symm (abelianExp X v) = v := by rw [hexp, e.left_inv hve]
  have hT : abelianExp X v ∈ e.target := by rw [hexp]; exact e.map_source hve
  have hsm : MDifferentiableAt 𝓘(ℂ, Fin (dim X.left) → ℂ) 𝓘(ℂ, Fin (dim X.left) → ℂ) e.symm
      (abelianExp X v) :=
    ((hs _ hT).contMDiffAt (e.open_target.mem_nhds hT)).mdifferentiableAt (by simp)
  have hGd : MDifferentiableAt 𝓘(ℂ, Fin (dim X.left) → ℂ) 𝓘(ℂ, ℂ) G (e.symm (abelianExp X v)) := by
    rw [hsymm]
    exact (hG.differentiableAt (hO.mem_nhds hv)).mdifferentiableAt
  have hcomp := hGd.comp (abelianExp X v) hsm
  refine hcomp.congr_of_eventuallyEq ?_
  have hpre : IsOpen (e.target ∩ e.symm ⁻¹' (O ∩ e.source)) :=
    e.isOpen_inter_preimage_symm (hO.inter e.open_source)
  filter_upwards [hpre.mem_nhds ⟨hT, by rw [Set.mem_preimage, hsymm]; exact ⟨hv, hve⟩⟩] with y hy
  obtain ⟨hyT, hyO, hyS⟩ := hy
  have h1 : abelianExp X (e.symm y) = y := by
    rw [show abelianExp X (e.symm y) = e (e.symm y) from heq hyS, e.right_inv hyT]
  change F y = G (e.symm y)
  rw [← hFG _ hyO, h1]

theorem differentiableOn_comp_abelianExp (F : ComplexPoint X → ℂ) (U : Set (ComplexPoint X))
    (hU : IsOpen U) (hF : MDifferentiableOn 𝓘(ℂ, Fin (dim X.left) → ℂ) 𝓘(ℂ, ℂ) F U) :
    DifferentiableOn ℂ (F ∘ abelianExp X) (abelianExp X ⁻¹' U) := by
  let : IsCommMonObj X := isCommMonObj_of_complexSelfProductIntegral X
    (complexSelfProductIntegral_of_isIntegral X)
  intro v hv
  have h1 := (hF.mdifferentiableAt (hU.mem_nhds hv)).comp v
    (spec_mdifferentiable_complexExponential X (dim X.left) v)
  exact (mdifferentiableAt_iff_differentiableAt.mp h1).differentiableWithinAt


theorem abelianExp_eq_iff_proj_eq (x y : Fin (dim X.left) → ℂ) :
    abelianExp X x = abelianExp X y ↔
      proj (abelianPeriodLattice X) x = proj (abelianPeriodLattice X) y := by
  constructor
  · intro h
    refine (QuotientAddGroup.eq (s := (abelianPeriodLattice X).toAddSubgroup)).mpr ?_
    rw [neg_add_eq_sub]; exact sub_mem_of_abelianExp_eq X h
  · intro h
    have hl : y - x ∈ abelianPeriodLattice X := by
      have := (QuotientAddGroup.eq (s := (abelianPeriodLattice X).toAddSubgroup)).mp h
      rwa [neg_add_eq_sub] at this
    have : y = x + (⟨y - x, hl⟩ : abelianPeriodLattice X) := by simp
    rw [this, abelianExp_add_lattice]

theorem spec_restrictEquivX_aux (H : HermitianForm (V := Fin (dim X.left) → ℂ))
    (E : abelianPeriodLattice X →+ abelianPeriodLattice X →+ ℤ)
    (hE : ∀ l m : abelianPeriodLattice X, (E l m : ℝ) = H.imaginary l m)
    (χ : abelianPeriodLattice X → Circle)
    (hχ : ∀ l m : abelianPeriodLattice X,
      χ (l + m) = χ l * χ m * Circle.exp (Real.pi * H.imaginary l m))
    (W : Set (Fin (dim X.left) → ℂ)) (hW : IsOpen W)
    (hdisj : ∀ l : abelianPeriodLattice X,
      ((· + (l : Fin (dim X.left) → ℂ)) '' W ∩ W).Nonempty → l = 0) :
    IsOpen (abelianExp X '' W) ∧
      ∃ e : sectionsOnX X (holFactor (datumOfX X H E hE χ hχ)) (abelianExp X '' W) ≃ₗ[ℂ]
          holomorphicOnX X (abelianExp X '' W),
        ∀ f (w : W),
          (e f : abelianExp X '' W → ℂ) ⟨abelianExp X w, Set.mem_image_of_mem _ w.2⟩ =
            (f : abelianExp X ⁻¹' (abelianExp X '' W) → ℂ)
              ⟨w, Set.subset_preimage_image _ _ w.2⟩ := by
  have hopen : IsOpen (abelianExp X '' W) := isOpenMap_abelianExp X W hW
  refine ⟨hopen, ?_⟩
  have hinj : Set.InjOn (abelianExp X) W := by
    intro w hw w' hw' hww'
    have hl := sub_mem_of_abelianExp_eq X hww'
    have h0 := hdisj ⟨_, hl⟩ ⟨w', ⟨w, hw, by simp⟩, hw'⟩
    have : w' - w = 0 := congrArg Subtype.val h0
    exact (sub_eq_zero.mp this).symm
  have hpre : abelianExp X ⁻¹' (abelianExp X '' W) =
      proj (abelianPeriodLattice X) ⁻¹' (proj (abelianPeriodLattice X) '' W) := by
    ext y
    simp only [Set.mem_preimage, Set.mem_image, abelianExp_eq_iff_proj_eq]
  obtain ⟨r, hr⟩ := spec_appellHumbert_restrictEquiv (datumOfX X H E hE χ hχ) W hW hdisj
  let invW : abelianExp X '' W → W := fun u ↦ ⟨u.2.choose, u.2.choose_spec.1⟩
  have hinvW : ∀ u, abelianExp X (invW u) = u := fun u ↦ u.2.choose_spec.2
  have hinvW' : ∀ w : W, invW ⟨abelianExp X w, Set.mem_image_of_mem _ w.2⟩ = w := fun w ↦
    Subtype.ext (hinj (invW _).2 w.2 (hinvW _))
  classical
  let φ : AutomorphyLineBundle.holomorphicOn W ≃ₗ[ℂ] holomorphicOnX X (abelianExp X '' W) :=
    { toFun := fun g ↦ ⟨fun u ↦ (g : W → ℂ) (invW u), by
        obtain ⟨G, hG, hgG⟩ := g.2
        refine ⟨fun y ↦ if h : y ∈ abelianExp X '' W then G h.choose else 0,
          fun y hy ↦ ?_, fun u ↦ by simp only [u.2, ↓reduceDIte]; exact hgG _⟩
        obtain ⟨v, hv, rfl⟩ := hy
        refine (mdifferentiableAt_of_abelianExp X _ G W hW hG (fun w hw ↦ ?_)
          hv).mdifferentiableWithinAt
        have hm : abelianExp X w ∈ abelianExp X '' W := Set.mem_image_of_mem _ hw
        simp only [hm, ↓reduceDIte]
        exact congrArg G (hinj hm.choose_spec.1 hw hm.choose_spec.2)⟩
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl
      invFun := fun g ↦ ⟨fun w ↦ (g : abelianExp X '' W → ℂ)
          ⟨abelianExp X w, Set.mem_image_of_mem _ w.2⟩, by
        obtain ⟨G, hG, hgG⟩ := g.2
        exact ⟨G ∘ abelianExp X, (differentiableOn_comp_abelianExp X G _ hopen hG).mono
          (Set.subset_preimage_image _ _), fun w ↦ hgG _⟩⟩
      left_inv := fun g ↦ Subtype.ext (funext fun w ↦ by
        change (g : W → ℂ) (invW _) = (g : W → ℂ) w
        rw [hinvW'])
      right_inv := fun g ↦ Subtype.ext (funext fun u ↦ by
        change (g : abelianExp X '' W → ℂ) ⟨abelianExp X (invW u), _⟩ = _
        exact congrArg (g : abelianExp X '' W → ℂ) (Subtype.ext (hinvW u))) }
  refine ⟨(sectionsOnXEquiv X _ _ _ hpre).trans (r.trans φ), fun f w ↦ ?_⟩
  change (r (sectionsOnXEquiv X _ _ _ hpre f) : W → ℂ) (invW _) = _
  rw [hinvW']
  exact hr _ w

theorem spec_one_equiv_holomorphicOnX_aux (U : Set (ComplexPoint X)) (hU : IsOpen U) :
    ∃ e : sectionsOnX X 1 U ≃ₗ[ℂ] holomorphicOnX X U,
      ∀ f (x : abelianExp X ⁻¹' U),
        (e f : U → ℂ) ⟨abelianExp X x, x.2⟩ = (f : abelianExp X ⁻¹' U → ℂ) x := by
  let lift : ComplexPoint X → Fin (dim X.left) → ℂ := fun y ↦ (surjective_abelianExp X y).choose
  have hlift : ∀ y, abelianExp X (lift y) = y := fun y ↦ (surjective_abelianExp X y).choose_spec
  -- a section of `L(1)` is constant on fibres of `exp`
  have hfib : ∀ (f : sectionsOnX X 1 U) (x y : abelianExp X ⁻¹' U),
      abelianExp X x = abelianExp X y →
        (f : abelianExp X ⁻¹' U → ℂ) y = (f : abelianExp X ⁻¹' U → ℂ) x := by
    intro f x y hxy
    have hl := sub_mem_of_abelianExp_eq X hxy
    have := f.2.2 ⟨_, hl⟩ x
    simp only [Pi.one_apply, one_mul, add_sub_cancel] at this
    exact this
  let liftU : U → abelianExp X ⁻¹' U := fun u ↦ ⟨lift u, by
    change abelianExp X (lift u) ∈ U; rw [hlift]; exact u.2⟩
  have hdesc : ∀ (f : sectionsOnX X 1 U) (x : abelianExp X ⁻¹' U),
      (f : abelianExp X ⁻¹' U → ℂ) (liftU ⟨abelianExp X x, x.2⟩) =
        (f : abelianExp X ⁻¹' U → ℂ) x :=
    fun f x ↦ hfib f x _ (hlift _).symm
  refine ⟨
    { toFun := fun f ↦ ⟨fun u ↦ (f : abelianExp X ⁻¹' U → ℂ) (liftU u), by
        obtain ⟨⟨F, hF, hfF⟩, -⟩ := f.2
        refine ⟨fun y ↦ F (lift y), fun y hy ↦ ?_, fun u ↦ hfF _⟩
        obtain ⟨v, rfl⟩ := surjective_abelianExp X y
        refine (mdifferentiableAt_of_abelianExp X _ F _ (hU.preimage (continuous_abelianExp X))
          hF (fun w hw ↦ ?_) hy).mdifferentiableWithinAt
        rw [← hfF ⟨w, hw⟩, ← hfF (liftU ⟨abelianExp X w, hw⟩)]
        exact hdesc f ⟨w, hw⟩⟩
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl
      invFun := fun g ↦ ⟨fun x ↦ (g : U → ℂ) ⟨abelianExp X x, x.2⟩, by
        obtain ⟨G, hG, hgG⟩ := g.2
        refine ⟨⟨G ∘ abelianExp X, differentiableOn_comp_abelianExp X G U hU hG,
          fun x ↦ hgG _⟩, fun l x ↦ ?_⟩
        simp only [Pi.one_apply, one_mul]
        exact congrArg (g : U → ℂ) (Subtype.ext (abelianExp_add_lattice X x l))⟩
      left_inv := fun f ↦ Subtype.ext (funext fun x ↦ hdesc f x)
      right_inv := fun g ↦ Subtype.ext (funext fun u ↦ by
        change (g : U → ℂ) ⟨abelianExp X (lift u), _⟩ = (g : U → ℂ) u
        exact congrArg (g : U → ℂ) (Subtype.ext (hlift u))) }, fun f x ↦ hdesc f x⟩

theorem abelianExp_sub_mem_of_eq {v w : Fin (dim X.left) → ℂ}
    (h : abelianExp X v = abelianExp X w) : w - v ∈ abelianPeriodLattice X := by
  let : IsCommMonObj X := isCommMonObj_of_complexSelfProductIntegral X
    (complexSelfProductIntegral_of_isIntegral X)
  change complexExponentialHom X (dim X.left) (w - v) = 0
  have h' : complexExponentialHom X (dim X.left) v = complexExponentialHom X (dim X.left) w :=
    congrArg Additive.ofMul h
  rw [map_sub, ← h', sub_self]

theorem spec_preimage_thetaZeroLocusX_aux (H : HermitianForm (V := Fin (dim X.left) → ℂ))
    (E : abelianPeriodLattice X →+ abelianPeriodLattice X →+ ℤ)
    (hE : ∀ l m : abelianPeriodLattice X, (E l m : ℝ) = H.imaginary l m)
    (χ : abelianPeriodLattice X → Circle)
    (hχ : ∀ l m : abelianPeriodLattice X,
      χ (l + m) = χ l * χ m * Circle.exp (Real.pi * H.imaginary l m))
    (θ : (Fin (dim X.left) → ℂ) → ℂ) (hθ : θ ∈ sections (datumOfX X H E hE χ hχ)) :
    abelianExp X ⁻¹' thetaZeroLocusX X θ = {v | θ v = 0} := by
  ext v
  constructor
  · rintro ⟨w, hw, hwv⟩
    have hl := abelianExp_sub_mem_of_eq X hwv
    have hv : v = w + ((⟨v - w, hl⟩ : abelianPeriodLattice X) : Fin (dim X.left) → ℂ) := by
      simp
    change θ v = 0
    rw [hv, hθ.2 ⟨v - w, hl⟩ w]
    exact mul_eq_zero_of_right _ hw
  · intro hv
    exact ⟨v, hv, rfl⟩

theorem spec_isClosed_thetaZeroLocusX_aux (H : HermitianForm (V := Fin (dim X.left) → ℂ))
    (E : abelianPeriodLattice X →+ abelianPeriodLattice X →+ ℤ)
    (hE : ∀ l m : abelianPeriodLattice X, (E l m : ℝ) = H.imaginary l m)
    (χ : abelianPeriodLattice X → Circle)
    (hχ : ∀ l m : abelianPeriodLattice X,
      χ (l + m) = χ l * χ m * Circle.exp (Real.pi * H.imaginary l m))
    (θ : (Fin (dim X.left) → ℂ) → ℂ) (hθ : θ ∈ sections (datumOfX X H E hE χ hχ)) :
    IsClosed (thetaZeroLocusX X θ) := by
  have hc : (thetaZeroLocusX X θ)ᶜ = abelianExp X '' {v | θ v ≠ 0} := by
    ext x
    constructor
    · intro hx
      obtain ⟨v, rfl⟩ := surjective_abelianExp X x
      exact ⟨v, fun hv ↦ hx ⟨v, hv, rfl⟩, rfl⟩
    · rintro ⟨v, hv, rfl⟩ hx
      have hmem : v ∈ abelianExp X ⁻¹' thetaZeroLocusX X θ := hx
      rw [spec_preimage_thetaZeroLocusX_aux X H E hE χ hχ θ hθ] at hmem
      exact hv hmem
  rw [← isOpen_compl_iff, hc]
  exact isOpenMap_abelianExp X _ (isOpen_ne_fun hθ.1.continuous continuous_const)

theorem interior_zeroSet_eq_empty_of_differentiableX {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {f : E → ℂ} (hf : Differentiable ℂ f) (hne : f ≠ 0) :
    interior {x | f x = 0} = ∅ := by
  refine Set.eq_empty_iff_forall_notMem.2 fun x₀ hx₀ ↦ hne (funext fun y ↦ ?_)
  set g : ℂ → ℂ := fun t ↦ f (x₀ + t • (y - x₀))
  have hγ : Continuous fun t : ℂ ↦ x₀ + t • (y - x₀) := by fun_prop
  have hg : Differentiable ℂ g := fun t ↦
    (hf _).comp t ((differentiableAt_id.smul_const (y - x₀)).const_add x₀)
  have hga : AnalyticOnNhd ℂ g Set.univ := fun t _ ↦ hg.analyticAt t
  have hev : g =ᶠ[nhds 0] 0 := by
    have h0 : (fun t : ℂ ↦ x₀ + t • (y - x₀)) 0 = x₀ := by simp
    have hmem : {x | f x = 0} ∈ nhds ((fun t : ℂ ↦ x₀ + t • (y - x₀)) 0) := by
      rw [h0]; exact mem_interior_iff_mem_nhds.1 hx₀
    filter_upwards [hγ.continuousAt.preimage_mem_nhds hmem] with t ht using ht
  have := hga.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ
    (Set.mem_univ 0) hev (Set.mem_univ 1)
  simpa [g] using this

theorem spec_interior_thetaZeroLocusX_aux (H : HermitianForm (V := Fin (dim X.left) → ℂ))
    (E : abelianPeriodLattice X →+ abelianPeriodLattice X →+ ℤ)
    (hE : ∀ l m : abelianPeriodLattice X, (E l m : ℝ) = H.imaginary l m)
    (χ : abelianPeriodLattice X → Circle)
    (hχ : ∀ l m : abelianPeriodLattice X,
      χ (l + m) = χ l * χ m * Circle.exp (Real.pi * H.imaginary l m))
    (θ : (Fin (dim X.left) → ℂ) → ℂ) (hθ : θ ∈ sections (datumOfX X H E hE χ hχ))
    (hne : θ ≠ 0) :
    interior (thetaZeroLocusX X θ) = ∅ := by
  have hsub : abelianExp X ⁻¹' interior (thetaZeroLocusX X θ) ⊆ interior {v | θ v = 0} := by
    apply interior_maximal
    · rw [← spec_preimage_thetaZeroLocusX_aux X H E hE χ hχ θ hθ]
      exact Set.preimage_mono interior_subset
    · exact isOpen_interior.preimage (continuous_abelianExp X)
  rw [interior_zeroSet_eq_empty_of_differentiableX hθ.1 hne] at hsub
  rw [Set.eq_empty_iff_forall_notMem]
  intro x hx
  obtain ⟨v, rfl⟩ := surjective_abelianExp X x
  exact hsub hx

theorem spec_exists_nontrivial_characterX_aux (hg : 0 < dim X.left) :
    ∃ χ : abelianPeriodLattice X → Circle,
      (∀ l m, χ (l + m) = χ l * χ m) ∧ ∃ l, χ l ≠ 1 := by
  have hi : 0 < 2 * dim X.left := by omega
  let i : Fin (2 * dim X.left) := ⟨0, hi⟩
  refine ⟨fun l ↦ Circle.exp (Real.pi * ((abelianLatticeBasis X).repr l i : ℝ)), fun l m ↦ ?_,
    abelianLatticeBasis X i, ?_⟩
  · simp only [map_add, Finsupp.add_apply, Int.cast_add, mul_add, Circle.exp_add]
  · simp only [Module.Basis.repr_self, Finsupp.single_eq_same, Int.cast_one, mul_one]
    intro h
    have h' := congrArg (fun z : Circle ↦ (z : ℂ)) h
    simp only [Circle.coe_exp, Circle.coe_one, Complex.exp_pi_mul_I] at h'
    norm_num at h'

end HodgeLean.Adapters
