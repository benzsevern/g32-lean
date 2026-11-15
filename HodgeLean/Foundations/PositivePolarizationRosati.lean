import HodgeLean.Foundations.PositivePolarizationDefs
import HodgeLean.Adapters.GagaWiring

/-! # Algebra of the Rosati involution (helpers for track P1)

* The adjoint `p1_adjoint ω hω` for the dual form `E_ω` is characterized by
  `E_ω (f x, y) = E_ω (x, f† y)`; it is additive, `ℚ`-linear, unital, reverses composition and is
  involutive (`E_ω` is alternating).
* The image of the action of `End⁰(A)` on `H¹(A; ℚ)` is `hodgeEndH1 A`
  (`gagaw_spec_abelianEnd0Action_range`).
* For `pol ∈ Hdg¹` with nondegenerate 2-vector, the adjoint of a Hodge endomorphism is a Hodge
  endomorphism: `Hol` and `Anti` are isotropic for `E_ω ⊗ ℂ` (`spec_firstRiemannRelation`), they
  span, and `E_ω ⊗ ℂ` is nondegenerate, so each is its own orthogonal.
* A Hodge endomorphism commutes with the canonical real complex structure
  `weightOneComplexStructure`, whose complexification is `-C`.

HC no distance; AV milestone no distance.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace Module
open scoped TensorProduct
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Foundations.Symplectic

namespace HodgeLean.Foundations

section Linear

variable {V : Type*} [AddCommGroup V] [Module ℚ V]

theorem p1r_dualForm_adjoint {ω : ⋀[ℚ]^2 V} (hω : IsNondegenerate ω)
    (f : Module.End ℚ V) (x y : V) :
    dualForm hω (f x) y = dualForm hω x (p1_adjoint ω hω f y) := by
  simp [p1_adjoint, dualForm_apply, LinearMap.dualMap_apply]

/-- The adjoint is the unique map with `E (f x, y) = E (x, g y)`. -/
theorem p1r_adjoint_eq_of {ω : ⋀[ℚ]^2 V} (hω : IsNondegenerate ω)
    (f g : Module.End ℚ V) (h : ∀ x y, dualForm hω (f x) y = dualForm hω x (g y)) :
    p1_adjoint ω hω f = g := by
  ext y
  refine sub_eq_zero.1 ((nondegenerate_dualForm hω).2 _ fun x => ?_)
  rw [map_sub, ← p1r_dualForm_adjoint, h, sub_self]

theorem p1r_adjoint_add {ω : ⋀[ℚ]^2 V} (hω : IsNondegenerate ω) (f g : Module.End ℚ V) :
    p1_adjoint ω hω (f + g) = p1_adjoint ω hω f + p1_adjoint ω hω g :=
  p1r_adjoint_eq_of hω _ _ fun x y => by
    simp only [LinearMap.add_apply, map_add, LinearMap.add_apply, p1r_dualForm_adjoint]

theorem p1r_adjoint_smul {ω : ⋀[ℚ]^2 V} (hω : IsNondegenerate ω) (q : ℚ)
    (f : Module.End ℚ V) : p1_adjoint ω hω (q • f) = q • p1_adjoint ω hω f :=
  p1r_adjoint_eq_of hω _ _ fun x y => by
    simp only [LinearMap.smul_apply, map_smul, LinearMap.smul_apply, p1r_dualForm_adjoint]

theorem p1r_adjoint_one {ω : ⋀[ℚ]^2 V} (hω : IsNondegenerate ω) :
    p1_adjoint ω hω 1 = 1 :=
  p1r_adjoint_eq_of hω _ _ fun _ _ => rfl

theorem p1r_adjoint_mul {ω : ⋀[ℚ]^2 V} (hω : IsNondegenerate ω) (f g : Module.End ℚ V) :
    p1_adjoint ω hω (f * g) = p1_adjoint ω hω g * p1_adjoint ω hω f :=
  p1r_adjoint_eq_of hω _ _ fun x y => by
    simp only [Module.End.mul_apply, p1r_dualForm_adjoint]

theorem p1r_adjoint_adjoint {ω : ⋀[ℚ]^2 V} (hω : IsNondegenerate ω) (f : Module.End ℚ V) :
    p1_adjoint ω hω (p1_adjoint ω hω f) = f := by
  have hskew : ∀ x y, dualForm hω x y = -dualForm hω y x := fun x y =>
    ((isAlt_dualForm hω).neg_eq y x).symm
  refine p1r_adjoint_eq_of hω _ _ fun x y => ?_
  rw [hskew, ← p1r_dualForm_adjoint, hskew, neg_neg]

/-- The `ℂ`-bilinear extension of an adjoint pair is an adjoint pair. -/
theorem p1r_baseChange_adjoint (B : LinearMap.BilinForm ℚ V) (f g : Module.End ℚ V)
    (h : ∀ x y, B (f x) y = B x (g y)) (x y : ℂ ⊗[ℚ] V) :
    B.baseChange ℂ (f.baseChange ℂ x) y = B.baseChange ℂ x (g.baseChange ℂ y) := by
  induction x using TensorProduct.inductionOn with
  | add x x' hx hx' => simp only [map_add, LinearMap.add_apply, hx, hx']
  | tmul a v =>
    induction y using TensorProduct.inductionOn with
    | add y y' hy hy' => simp only [map_add, hy, hy']
    | tmul b w => simp [LinearMap.BilinForm.baseChange_tmul, h]

end Linear

section Isotropic

variable {M : Type*} [AddCommGroup M] [Module ℂ M]

/-- **Adjoints preserve a Lagrangian splitting.** If `M = P ⊔ Q` with `P`, `Q` isotropic for a
nondegenerate `E`, and `F` preserves `P` and `Q`, then the `E`-adjoint `G` of `F` preserves `P`:
for `y ∈ P`, write `G y = p + q`; then `E (·, q)` vanishes on `P` (as `E (x, G y) = E (F x, y)`)
and on `Q`, so `q = 0`.
Source: Bourbaki, *Algèbre*, ch. IX, §4 (totally isotropic subspaces). -/
theorem p1r_map_le_of_isotropic (E : LinearMap.BilinForm ℂ M) (hE : E.Nondegenerate)
    (P Q : Submodule ℂ M) (hPQ : P ⊔ Q = ⊤) (hP : ∀ x ∈ P, ∀ y ∈ P, E x y = 0)
    (hQ : ∀ x ∈ Q, ∀ y ∈ Q, E x y = 0) (F G : Module.End ℂ M)
    (hFG : ∀ x y, E (F x) y = E x (G y)) (hF : P.map F ≤ P) : P.map G ≤ P := by
  rintro _ ⟨y, hy, rfl⟩
  obtain ⟨p, hp, q, hq, hpq⟩ := Submodule.mem_sup.1 (hPQ ▸ Submodule.mem_top : G y ∈ P ⊔ Q)
  have hq0 : q = 0 := by
    refine hE.2 q fun w => ?_
    obtain ⟨w₁, hw₁, w₂, hw₂, rfl⟩ := Submodule.mem_sup.1 (hPQ ▸ Submodule.mem_top : w ∈ P ⊔ Q)
    have h1 : E w₁ q = 0 := by
      have := hFG w₁ y
      rw [hP _ (hF ⟨w₁, hw₁, rfl⟩) _ hy, ← hpq, map_add, hP _ hw₁ _ hp, zero_add] at this
      exact this.symm
    rw [map_add, LinearMap.add_apply, h1, hQ _ hw₂ _ hq, add_zero]
  rw [← hpq, hq0, add_zero]
  exact hp

end Isotropic

section Real

variable {W : Type*} [AddCommGroup W] [Module ℝ W]

/-- Extension of scalars from `ℝ` to `ℂ` is faithful on endomorphisms. -/
theorem p1r_baseChange_injective {F G : Module.End ℝ W}
    (h : F.baseChange ℂ = G.baseChange ℂ) : F = G := by
  ext x
  have hx := LinearMap.congr_fun h ((1 : ℂ) ⊗ₜ x)
  rw [LinearMap.baseChange_tmul, LinearMap.baseChange_tmul] at hx
  have := congrArg (TensorProduct.lid ℝ W ∘ Complex.reLm.rTensor W) hx
  simpa using this

end Real

section Complexify

variable {V : Type*} [AddCommGroup V] [Module ℚ V]

theorem p1r_complexifyRealEnd_injective {F G : Module.End ℝ (ℝ ⊗[ℚ] V)}
    (h : complexifyRealEnd F = complexifyRealEnd G) : F = G := by
  refine p1r_baseChange_injective ?_
  have h' := congrArg (fun H => (TensorProduct.AlgebraTensorModule.cancelBaseChange ℚ ℝ ℂ ℂ
    V).symm.toLinearMap ∘ₗ H ∘ₗ
      (TensorProduct.AlgebraTensorModule.cancelBaseChange ℚ ℝ ℂ ℂ V).toLinearMap) h
  refine LinearMap.ext fun x => ?_
  simpa [complexifyRealEnd] using LinearMap.congr_fun h' x

theorem p1r_complexifyRealEnd_comp (F G : Module.End ℝ (ℝ ⊗[ℚ] V)) :
    complexifyRealEnd (F ∘ₗ G) = complexifyRealEnd F ∘ₗ complexifyRealEnd G := by
  ext x
  simp [complexifyRealEnd, LinearMap.baseChange_comp]

theorem p1r_complexifyRealEnd_baseChange (T : Module.End ℚ V) :
    complexifyRealEnd (T.baseChange ℝ) = T.baseChange ℂ := by
  ext v
  simp [complexifyRealEnd]

end Complexify

section Grading

variable {V : Type*} [AddCommGroup V] [Module ℚ V]

/-- An endomorphism preserving every piece of a Hodge decomposition commutes with its grading
operator. -/
theorem p1r_comp_gradingOperator (H : ℤ × ℤ → Submodule ℂ (ℂ ⊗[ℚ] V))
    (hH : DirectSum.IsInternal H) (T : Module.End ℂ (ℂ ⊗[ℚ] V))
    (hT : ∀ pq, (H pq).map T ≤ H pq) :
    T ∘ₗ gradingOperator H hH = gradingOperator H hH ∘ₗ T := by
  refine linearMap_ext_of_isInternal hH fun pq x hx => ?_
  have hTx : T x ∈ H pq := hT pq ⟨x, hx, rfl⟩
  rw [LinearMap.comp_apply, LinearMap.comp_apply, gradingOperator_apply_of_mem H hH hx,
    gradingOperator_apply_of_mem H hH hTx, map_smul]

end Grading

section Abelian

variable (A : Over (Spec ↧ℂ)) [GrpObj A] [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]

/-- A Hodge endomorphism of `H¹` preserves every weight-one Hodge piece. -/
theorem p1r_map_cohomologyHodgePiece_le {T : Module.End ℚ (HQ A 1)} (hT : T ∈ hodgeEndH1 A)
    (pq : ℤ × ℤ) :
    (cohomologyHodgePiece A 1 pq).map (T.baseChange ℂ) ≤ cohomologyHodgePiece A 1 pq := by
  rw [spec_g4_cohomologyHodgePiece_one_eq]
  unfold latticeHodgePieces
  split_ifs
  · exact hT.1
  · exact hT.2
  · rw [Submodule.map_bot]

/-- **A Hodge endomorphism commutes with the canonical real complex structure.** The
complexification of `I = weightOneComplexStructure A …` is `-C` for the grading operator `C` of
the weight-one Hodge structure, which acts by a scalar on each Hodge piece; a Hodge endomorphism
preserves the pieces, so it commutes with `C`, hence with `I`.
Source: Deligne, *Théorie de Hodge II*, §2.1; `spec_weightOneComplexStructure`. -/
theorem p1r_baseChange_comp_weightOneComplexStructure {T : Module.End ℚ (HQ A 1)}
    (hT : T ∈ hodgeEndH1 A) :
    T.baseChange ℝ ∘ₗ
        weightOneComplexStructure A (finiteBetti_abelian A) (spec_bettiDeRhamIso_abelian A) =
      weightOneComplexStructure A (finiteBetti_abelian A) (spec_bettiDeRhamIso_abelian A) ∘ₗ
        T.baseChange ℝ := by
  have hI := (spec_weightOneComplexStructure A (finiteBetti_abelian A)
    (spec_bettiDeRhamIso_abelian A)).2.1
  refine p1r_complexifyRealEnd_injective ?_
  rw [p1r_complexifyRealEnd_comp, p1r_complexifyRealEnd_comp, hI,
    p1r_complexifyRealEnd_baseChange]
  rw [LinearMap.comp_neg, LinearMap.neg_comp, neg_inj]
  exact p1r_comp_gradingOperator _ _ _ (p1r_map_cohomologyHodgePiece_le A hT)

/-- **The adjoint of a Hodge endomorphism is a Hodge endomorphism.** For `pol ∈ Hdg¹` with
nondegenerate 2-vector `ω`, the summands `Hol` and `Anti` of `ℂ ⊗ H¹` are isotropic for
`E_ω ⊗ ℂ` (`spec_firstRiemannRelation`), they span (`spec_complexH1_split`) and `E_ω ⊗ ℂ` is
nondegenerate, so the `E_ω`-adjoint of an endomorphism preserving both preserves both.
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., §5.1 (the Rosati involution
preserves `End_HS`); `spec_firstRiemannRelation`, `p1r_map_le_of_isotropic`. -/
theorem p1r_adjoint_mem_hodgeEndH1 {pol : HQ A 2}
    (hη : IsNondegenerate (polarizationVec (torusCohomology_cupProductOf A) pol))
    (hH : (pol : H^(2 * 1)(A; ℚ)) ∈ Hdg^1(A; ℚ)) {T : Module.End ℚ (HQ A 1)}
    (hT : T ∈ hodgeEndH1 A) :
    letI := (torusCohomology_cupProductOf A).finite
    p1_adjoint _ hη T ∈ hodgeEndH1 A := by
  let _ := (torusCohomology_cupProductOf A).finite
  obtain ⟨⟨h10, h01⟩, -⟩ := (spec_firstRiemannRelation A (finiteBetti_abelian A)
    (spec_bettiDeRhamIso_abelian A) hη).1 hH
  have e10 : complexHolomorphicH1 A = cohomologyHodgePiece A 1 (1, 0) := by
    rw [spec_g4_cohomologyHodgePiece_one_eq]
    simp [latticeHodgePieces]
  have e01 : complexAntiholomorphicH1 A = cohomologyHodgePiece A 1 (0, 1) := by
    rw [spec_g4_cohomologyHodgePiece_one_eq]
    simp [latticeHodgePieces]
  have i10 : ∀ x ∈ complexHolomorphicH1 A, ∀ y ∈ complexHolomorphicH1 A,
      (polarizationForm (torusCohomology_cupProductOf A) hη).baseChange ℂ x y = 0 := by
    rw [e10]
    exact h10
  have i01 : ∀ x ∈ complexAntiholomorphicH1 A, ∀ y ∈ complexAntiholomorphicH1 A,
      (polarizationForm (torusCohomology_cupProductOf A) hη).baseChange ℂ x y = 0 := by
    rw [e01]
    exact h01
  have hE := WeilPower.nondegenerate_baseChange _
    (nondegenerate_polarizationForm (torusCohomology_cupProductOf A) hη)
  have hadj := p1r_baseChange_adjoint (polarizationForm (torusCohomology_cupProductOf A) hη) T
    (p1_adjoint _ hη T) (p1r_dualForm_adjoint hη T)
  have hsplit := (spec_complexH1_split A).1
  exact ⟨p1r_map_le_of_isotropic _ hE _ _ hsplit i10 i01 _ _ hadj hT.1,
    p1r_map_le_of_isotropic _ hE _ _ (by rw [sup_comm]; exact hsplit) i01 i10 _ _ hadj hT.2⟩

variable [IsCommMonObj A]

/-- **The image of `End⁰(A)` in `End(H¹)` is `hodgeEndH1 A`.** The action
`abelianEnd0Action` agrees with the map of `gagaw_spec_abelianEnd0Action_range` on the generators
`1 ⊗ f`, hence everywhere.
Source: Mumford, *Abelian Varieties*, §19; `gagaw_spec_abelianEnd0Action_range`,
`spec_g4_abelianEnd0Action_tmul`, `spec_g4_abelianEnd0Action_mem_hodgeEndH1`. -/
theorem p1r_mem_range_iff (T : Module.End ℚ (HQ A 1)) :
    T ∈ Set.range (fun ψ : AbelianEnd0 A => (abelianEnd0Action A ψ).unop) ↔
      T ∈ hodgeEndH1 A := by
  obtain ⟨ρ, hρ, -, hrange⟩ := gagaw_spec_abelianEnd0Action_range A
  have h : ∀ x, ρ x = abelianEnd0Action A x := by
    intro x
    induction x using TensorProduct.inductionOn with
    | tmul q f =>
      have hq : q ⊗ₜ[ℤ] f = q • ((1 : ℚ) ⊗ₜ[ℤ] f) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [hq, map_smul, map_smul, hρ, spec_g4_abelianEnd0Action_tmul, one_smul]
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  constructor
  · rintro ⟨ψ, rfl⟩
    exact spec_g4_abelianEnd0Action_mem_hodgeEndH1 A ψ
  · intro hT
    have hmem : MulOpposite.op T ∈ ρ.range := by
      rw [hrange]
      exact hT
    obtain ⟨ψ, hψ⟩ := hmem
    refine ⟨ψ, ?_⟩
    change (abelianEnd0Action A ψ).unop = T
    rw [← h]
    exact congrArg MulOpposite.unop hψ

/-- The action of `End⁰(A)` on `H¹`, read in `Module.End`, is injective. -/
theorem p1r_unop_abelianEnd0Action_injective :
    Function.Injective fun ψ : AbelianEnd0 A => (abelianEnd0Action A ψ).unop :=
  MulOpposite.unop_injective.comp (spec_g4_abelianEnd0Action_injective A)

section Rosati

variable {A} {pol : HQ A 2}
  (hη : IsNondegenerate (polarizationVec (torusCohomology_cupProductOf A) pol))
  (hR : ∀ φ : AbelianEnd0 A,
    letI := (torusCohomology_cupProductOf A).finite
    p1_adjoint _ hη (abelianEnd0Action A φ).unop ∈
      Set.range fun ψ : AbelianEnd0 A => (abelianEnd0Action A ψ).unop)

include hR

/-- The action of `p1_rosati A pol hη hR φ` is the adjoint of the action of `φ`. -/
theorem p1r_abelianEnd0Action_rosati (φ : AbelianEnd0 A) :
    (abelianEnd0Action A (p1_rosati A pol hη hR φ)).unop =
      p1_adjoint _ hη (abelianEnd0Action A φ).unop :=
  Equiv.apply_ofInjective_symm
    (f := fun ψ : AbelianEnd0 A => (abelianEnd0Action A ψ).unop) _ ⟨_, hR φ⟩

theorem p1r_rosati_add (φ ψ : AbelianEnd0 A) :
    p1_rosati A pol hη hR (φ + ψ) = p1_rosati A pol hη hR φ + p1_rosati A pol hη hR ψ :=
  p1r_unop_abelianEnd0Action_injective A (by
    simp only [map_add, MulOpposite.unop_add, p1r_abelianEnd0Action_rosati, p1r_adjoint_add])

theorem p1r_rosati_smul (q : ℚ) (φ : AbelianEnd0 A) :
    p1_rosati A pol hη hR (q • φ) = q • p1_rosati A pol hη hR φ :=
  p1r_unop_abelianEnd0Action_injective A (by
    simp only [map_smul, MulOpposite.unop_smul, p1r_abelianEnd0Action_rosati, p1r_adjoint_smul])

theorem p1r_rosati_one : p1_rosati A pol hη hR 1 = 1 :=
  p1r_unop_abelianEnd0Action_injective A (by
    simp only [map_one, MulOpposite.unop_one, p1r_abelianEnd0Action_rosati, p1r_adjoint_one])

theorem p1r_rosati_mul (φ ψ : AbelianEnd0 A) :
    p1_rosati A pol hη hR (φ * ψ) = p1_rosati A pol hη hR ψ * p1_rosati A pol hη hR φ :=
  p1r_unop_abelianEnd0Action_injective A (by
    simp only [map_mul, MulOpposite.unop_mul, p1r_abelianEnd0Action_rosati, p1r_adjoint_mul])

theorem p1r_rosati_rosati (φ : AbelianEnd0 A) :
    p1_rosati A pol hη hR (p1_rosati A pol hη hR φ) = φ :=
  p1r_unop_abelianEnd0Action_injective A (by
    simp only [p1r_abelianEnd0Action_rosati, p1r_adjoint_adjoint])

end Rosati

end Abelian

end HodgeLean.Foundations
