import Mathlib.RingTheory.Grassmannian
import HodgeLean.Foundations.Analytic.AnalytificationDefs

/-! # Grassmannians over the integers: definitions

The Grassmannian `f5_grassmannian k n` is constructed as `Proj` of its Plücker coordinate ring.
The Plücker coordinates `p_I`, indexed by the `k`-subsets `I` of `Fin n`, are sent to
`t · Δ_I`, where `Δ_I` is the `k × k` minor on the columns `I` of the generic `k × n` matrix
`(x_{ij})` and `t` is one further variable. The image `f5_PluckerRing k n` of this map is graded
by the images of the homogeneous polynomials of each degree (`f5_pluckerGrading`); the image of
degree `d` lies in total degree `(k + 1) d`, which makes the grading a direct sum. The extra
variable `t` keeps the grades apart also when `k = 0`, where every minor is `1`. Over
`Spec ℤ`, the structure morphism is `Proj → Spec (degree zero)` followed by the map induced by
`ℤ → degree zero`.

Its Plücker morphism `f5_plucker k n` into the projective space on the Plücker indices is
`Proj` of the surjection from the polynomial ring in the `p_I`; its standard charts
`f5_chart k n I` are the basic opens of the Plücker coordinates. `f5_grassmannianOver k n S s`
is its base change along `s : S ⟶ Spec ℤ`, and `f5_complexChart` the base change of a chart to
`Spec ℂ`.

For the functor-of-points statements, `f5_pointsFunctor G` sends a `ℤ`-algebra `A` to the
morphisms `Spec A ⟶ G` over `Spec ℤ`. For the sheaf-level statements, `f5_IsLocallyFreeOfRank`
says that a sheaf of modules is locally isomorphic to the free sheaf of rank `r`, and
`f5_IsUniversalQuotient` that a quotient of the free sheaf of rank `n` is locally free of rank
`k` and represents such quotients on every scheme over `Spec ℤ` by pullback.

Every definition here is a construction; the properties of the construction are stated in the
frozen file. HC no distance; AV milestone no distance.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial

namespace HodgeLean.Foundations.Algebraic

/-! ### Affine test schemes and the functor of points -/

/-- The affine scheme over `Spec ℤ` attached to a commutative `ℤ`-algebra.
Source: EGA I, §1.6 (the contravariant spectrum functor). -/
def f5_affineOver (A : CommAlgCat ℤ) : Over (Spec (CommRingCat.of ℤ)) :=
  Over.mk (Scheme.Spec.map (CommRingCat.ofHom (algebraMap ℤ A)).op)

example (A : CommAlgCat ℤ) : (f5_affineOver A).left = Spec (CommRingCat.of A) := rfl

/-- The map of affine test schemes induced contravariantly by a map of `ℤ`-algebras.
Source: EGA I, §1.6 (functoriality of affine spectra). -/
def f5_affineMap {A B : CommAlgCat ℤ} (f : A ⟶ B) : f5_affineOver B ⟶ f5_affineOver A :=
  Over.homMk (Scheme.Spec.map (CommRingCat.ofHom f.hom).op) (by
    have h : CommRingCat.ofHom (algebraMap ℤ A) ≫ CommRingCat.ofHom f.hom =
        CommRingCat.ofHom (algebraMap ℤ B) := by
      ext z
      simp
    change Scheme.Spec.map (CommRingCat.ofHom f.hom).op ≫
      Scheme.Spec.map (CommRingCat.ofHom (algebraMap ℤ A)).op =
        Scheme.Spec.map (CommRingCat.ofHom (algebraMap ℤ B)).op
    rw [← Scheme.Spec.map_comp]
    exact congrArg Scheme.Spec.map (congrArg Opposite.op h))

example {A B : CommAlgCat ℤ} (f : A ⟶ B) :
    (f5_affineMap f).left = Scheme.Spec.map (CommRingCat.ofHom f.hom).op := rfl

theorem f5_affineMap_id (A : CommAlgCat ℤ) : f5_affineMap (𝟙 A) = 𝟙 (f5_affineOver A) := by
  ext : 1
  simp [f5_affineMap]
  rfl

theorem f5_affineMap_comp {A B C : CommAlgCat ℤ} (f : A ⟶ B) (g : B ⟶ C) :
    f5_affineMap (f ≫ g) = f5_affineMap g ≫ f5_affineMap f := by
  ext : 1
  change Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp]
  rfl

/-- The functor of affine points of a scheme over `Spec ℤ`: a `ℤ`-algebra `A` goes to the
morphisms `Spec A ⟶ G` over `Spec ℤ`, and a map of algebras acts by precomposition.
Source: EGA I, §0.1.1 and §1.6 (functor of points); Stacks Project, Tag 01JF. -/
def f5_pointsFunctor (G : Over (Spec (CommRingCat.of ℤ))) : CommAlgCat.{0} ℤ ⥤ Type where
  obj A := f5_affineOver A ⟶ G
  map f := TypeCat.ofHom fun x => f5_affineMap f ≫ x
  map_id A := by ext x; simp [f5_affineMap_id]
  map_comp f g := by ext x; simp [f5_affineMap_comp]

example (G : Over (Spec (CommRingCat.of ℤ))) (A : CommAlgCat ℤ) :
    (f5_pointsFunctor G).obj A = (f5_affineOver A ⟶ G) := rfl

/-- The standard affine dimension of a quotient-convention Grassmannian chart.
Source: EGA I, §9.7.3. -/
def f5_chartDimension (k n : ℕ) : ℕ := k * (n - k)

example (n : ℕ) : f5_chartDimension 1 n = n - 1 := by simp [f5_chartDimension]

/-! ### The Plücker coordinate ring -/

/-- The Plücker indices: the `k`-element subsets of `Fin n`.
Source: EGA I, §9.8.1; Stacks Project, Tag 089T. -/
abbrev f5_PluckerIndex (k n : ℕ) : Type := {I : Finset (Fin n) // I.card = k}

example : Fintype.card (f5_PluckerIndex 1 2) = 2 := by decide

/-- The ambient polynomial ring: the entries `x_{ij}` (`some (i, j)`) of the generic `k × n`
matrix and one further variable `t` (`none`), with coefficients in `ULift ℤ`, the coefficient
ring of `ProjectiveSpace`.
Source: Stacks Project, Tag 089T (the generic matrix of a chart). -/
abbrev f5_MatrixRing (k n : ℕ) : Type := MvPolynomial (Option (Fin k × Fin n)) (ULift.{0} ℤ)

example (k n : ℕ) : (X none : f5_MatrixRing k n).IsHomogeneous 1 := isHomogeneous_X _ _

/-- The minor of the generic `k × n` matrix on the columns `I`, taken in increasing order.
Source: EGA I, §9.8.1 (Plücker coordinates as maximal minors). -/
def f5_minor (k n : ℕ) (I : f5_PluckerIndex k n) : f5_MatrixRing k n :=
  (Matrix.of fun i j : Fin k => (X (some (i, I.1.orderEmbOfFin I.2 j)) : f5_MatrixRing k n)).det

example (n : ℕ) : f5_minor 0 n ⟨∅, rfl⟩ = 1 := Matrix.det_isEmpty

theorem f5_minor_isHomogeneous (k n : ℕ) (I : f5_PluckerIndex k n) :
    (f5_minor k n I).IsHomogeneous k := by
  rw [f5_minor, Matrix.det_apply]
  refine IsHomogeneous.sum _ _ _ fun σ _ => ?_
  rw [Units.smul_def, ← mem_homogeneousSubmodule]
  refine Submodule.smul_of_tower_mem _ _ ?_
  rw [mem_homogeneousSubmodule]
  simpa using IsHomogeneous.prod (Finset.univ : Finset (Fin k)) _ (fun _ => 1)
    fun i _ => isHomogeneous_X _ _

/-- The Plücker map `p_I ↦ t · Δ_I` from the polynomial ring in the Plücker coordinates.
Source: EGA I, §9.8.1; Hodge--Pedoe, *Methods of Algebraic Geometry* II, Ch. XIV. -/
def f5_pluckerHom (k n : ℕ) :
    MvPolynomial (f5_PluckerIndex k n) (ULift.{0} ℤ) →ₐ[ULift.{0} ℤ] f5_MatrixRing k n :=
  aeval fun I => X none * f5_minor k n I

example (k n : ℕ) (I : f5_PluckerIndex k n) :
    f5_pluckerHom k n (X I) = X none * f5_minor k n I := aeval_X _ _

theorem f5_pluckerHom_isHomogeneous (k n : ℕ)
    {p : MvPolynomial (f5_PluckerIndex k n) (ULift.{0} ℤ)} {d : ℕ} (hp : p.IsHomogeneous d) :
    (f5_pluckerHom k n p).IsHomogeneous ((k + 1) * d) :=
  hp.aeval _ fun I => by
    rw [add_comm]; exact (isHomogeneous_X _ _).mul (f5_minor_isHomogeneous k n I)

/-- The Plücker coordinate ring: the image of the Plücker map, the homogeneous coordinate ring
of the Grassmannian in its Plücker embedding.
Source: EGA I, §9.8; Stacks Project, Tag 089V. -/
abbrev f5_PluckerRing (k n : ℕ) : Type := (f5_pluckerHom k n).range

example (k n : ℕ) : (1 : f5_PluckerRing k n).1 = 1 := rfl

/-- The Plücker map onto its image.
Source: EGA I, §9.8. -/
def f5_pluckerSurj (k n : ℕ) :
    MvPolynomial (f5_PluckerIndex k n) (ULift.{0} ℤ) →ₐ[ULift.{0} ℤ] f5_PluckerRing k n :=
  (f5_pluckerHom k n).rangeRestrict

example (k n : ℕ) : Function.Surjective (f5_pluckerSurj k n) :=
  AlgHom.rangeRestrict_surjective _

/-- The grading of the Plücker coordinate ring: degree `d` is the image of the homogeneous
polynomials of degree `d` in the Plücker coordinates.
Source: EGA II, §2.1 (graded rings); EGA I, §9.8. -/
def f5_pluckerGrading (k n : ℕ) (d : ℕ) : Submodule (ULift.{0} ℤ) (f5_PluckerRing k n) :=
  (homogeneousSubmodule (f5_PluckerIndex k n) (ULift.{0} ℤ) d).map
    (f5_pluckerSurj k n).toLinearMap

attribute [local instance] MvPolynomial.gradedAlgebra

instance f5_pluckerGrading_gradedMonoid (k n : ℕ) :
    SetLike.GradedMonoid (f5_pluckerGrading k n) where
  one_mem := ⟨1, isHomogeneous_one _ _, map_one (f5_pluckerSurj k n)⟩
  mul_mem := by
    rintro i j _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    exact ⟨a * b, IsHomogeneous.mul ha hb, map_mul (f5_pluckerSurj k n) _ _⟩

theorem f5_pluckerGrading_isInternal (k n : ℕ) :
    DirectSum.IsInternal (f5_pluckerGrading k n) := by
  rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]
  constructor
  · let ι := (f5_pluckerHom k n).range.val.toLinearMap
    have hB := (MvPolynomial.gradedAlgebra (σ := Option (Fin k × Fin n))
      (R := ULift.{0} ℤ)).isInternal.submodule_iSupIndep
    have hle : ∀ d, (f5_pluckerGrading k n d).map ι ≤
        homogeneousSubmodule (Option (Fin k × Fin n)) (ULift.{0} ℤ) ((k + 1) * d) := by
      rintro d _ ⟨_, ⟨p, hp, rfl⟩, rfl⟩
      exact f5_pluckerHom_isHomogeneous k n hp
    intro d
    rw [Submodule.disjoint_def]
    intro x hx hx'
    have h1 : ι x ∈
        homogeneousSubmodule (Option (Fin k × Fin n)) (ULift.{0} ℤ) ((k + 1) * d) :=
      hle d ⟨x, hx, rfl⟩
    have h2 : ι x ∈ ⨆ (m : ℕ) (_ : m ≠ (k + 1) * d),
        homogeneousSubmodule (Option (Fin k × Fin n)) (ULift.{0} ℤ) m := by
      have : ι x ∈ (⨆ (j : ℕ) (_ : j ≠ d), f5_pluckerGrading k n j).map ι := ⟨x, hx', rfl⟩
      refine (Submodule.map_le_iff_le_comap.mpr ?_) this
      refine iSup₂_le fun j hj => Submodule.map_le_iff_le_comap.mp ?_
      refine (hle j).trans ?_
      exact le_iSup₂_of_le ((k + 1) * j) (fun h => hj (by simpa using h)) le_rfl
    have : ι x = 0 := (Submodule.disjoint_def.mp (hB ((k + 1) * d))) _ h1 h2
    exact Subtype.ext this
  · change (⨆ d, (homogeneousSubmodule (f5_PluckerIndex k n) (ULift.{0} ℤ) d).map
      (f5_pluckerSurj k n).toLinearMap) = ⊤
    rw [← Submodule.map_iSup, ((MvPolynomial.gradedAlgebra (σ := f5_PluckerIndex k n)
      (R := ULift.{0} ℤ)).isInternal).submodule_iSup_eq_top, Submodule.map_top,
      LinearMap.range_eq_top]
    exact AlgHom.rangeRestrict_surjective _

/-- The Plücker coordinate ring as a graded algebra.
Source: EGA II, §2.1; EGA I, §9.8. -/
instance f5_pluckerGradedAlgebra (k n : ℕ) : GradedAlgebra (f5_pluckerGrading k n) where
  toDecomposition := (f5_pluckerGrading_isInternal k n).chooseDecomposition
  toGradedMonoid := inferInstance

example (k n : ℕ) : (1 : f5_PluckerRing k n) ∈ f5_pluckerGrading k n 0 :=
  SetLike.GradedOne.one_mem

/-! ### The Grassmannian, its Plücker morphism and its charts -/

/-- The Grassmannian of rank-`k` quotients of `ℤⁿ`, as `Proj` of the Plücker coordinate ring,
over `Spec ℤ`.
Source: EGA I, §9.7--9.8 (the Grassmannian and its Plücker embedding); Stacks Project,
Tags 089R, 089T and 089V. -/
def f5_grassmannian (k n : ℕ) : Over (Spec (CommRingCat.of ℤ)) :=
  Over.mk (Proj.toSpecZero (f5_pluckerGrading k n) ≫
    Spec.map (CommRingCat.ofHom (Int.castRingHom (f5_pluckerGrading k n 0))))

example (k n : ℕ) : (f5_grassmannian k n).left = Proj (f5_pluckerGrading k n) := rfl

/-- The Plücker map as a graded ring map from the homogeneous coordinate ring of projective
space.
Source: EGA I, §9.8.1. -/
def f5_pluckerGradedHom (k n : ℕ) :
    homogeneousSubmodule (f5_PluckerIndex k n) (ULift.{0} ℤ) →+*ᵍ f5_pluckerGrading k n where
  toRingHom := (f5_pluckerSurj k n).toRingHom
  map_mem hx := ⟨_, hx, rfl⟩

example (k n : ℕ) (I : f5_PluckerIndex k n) :
    f5_pluckerGradedHom k n (X I) = f5_pluckerSurj k n (X I) := rfl

theorem f5_irrelevant_le (k n : ℕ) :
    HomogeneousIdeal.irrelevant (f5_pluckerGrading k n) ≤
      (HomogeneousIdeal.irrelevant
        (homogeneousSubmodule (f5_PluckerIndex k n) (ULift.{0} ℤ))).map
        (f5_pluckerGradedHom k n) := by
  rw [HomogeneousIdeal.irrelevant_le]
  rintro i hi _ ⟨p, hp, rfl⟩
  exact Ideal.mem_map_of_mem _ (HomogeneousIdeal.mem_irrelevant_of_mem _ hi hp)

/-- The Plücker morphism from the Grassmannian to the projective space whose homogeneous
coordinates are the Plücker indices, over `Spec ℤ`.
Source: EGA I, §9.8.1; Stacks Project, Tag 089V. -/
def f5_plucker (k n : ℕ) :
    (f5_grassmannian k n).left ⟶
      ProjectiveSpace (f5_PluckerIndex k n) (Spec (CommRingCat.of ℤ)) :=
  pullback.lift (f5_grassmannian k n).hom
    (Proj.map (f5_pluckerGradedHom k n) (f5_irrelevant_le k n)) (terminal.hom_ext _ _)

example (k n : ℕ) : f5_plucker k n ≫ ProjectiveSpace.toBase _ _ = (f5_grassmannian k n).hom :=
  pullback.lift_fst _ _ _

/-- The Plücker coordinate `p_I` in the Plücker coordinate ring.
Source: EGA I, §9.8.1. -/
def f5_pluckerCoord (k n : ℕ) (I : f5_PluckerIndex k n) : f5_PluckerRing k n :=
  f5_pluckerSurj k n (X I)

example (k n : ℕ) (I : f5_PluckerIndex k n) :
    (f5_pluckerCoord k n I).1 = X none * f5_minor k n I := aeval_X _ _

/-- The standard chart of index `I`: the open subscheme where the Plücker coordinate `p_I` does
not vanish.
Source: EGA I, §9.7.3; Stacks Project, Tag 089T. -/
def f5_chart (k n : ℕ) (I : f5_PluckerIndex k n) : (f5_grassmannian k n).left.Opens :=
  Proj.basicOpen (f5_pluckerGrading k n) (f5_pluckerCoord k n I)

example (k n : ℕ) (I : f5_PluckerIndex k n) :
    f5_chart k n I = Proj.basicOpen (f5_pluckerGrading k n) (f5_pluckerCoord k n I) := rfl

/-! ### Base change -/

/-- The Grassmannian over a scheme `S`, the base change of `f5_grassmannian k n` along
`s : S ⟶ Spec ℤ`.
Source: EGA I, §9.7.5 (base change of the Grassmannian). -/
def f5_grassmannianOver (k n : ℕ) (S : Scheme.{0}) (s : S ⟶ Spec (CommRingCat.of ℤ)) :
    Over S :=
  Over.mk (pullback.fst s (f5_grassmannian k n).hom)

example (k n : ℕ) (S : Scheme.{0}) (s : S ⟶ Spec (CommRingCat.of ℤ)) :
    (f5_grassmannianOver k n S s).left = pullback s (f5_grassmannian k n).hom := rfl

/-- The structure morphism `Spec ℂ ⟶ Spec ℤ`.
Source: EGA I, §1.6. -/
def f5_complexStructure : Spec ↧ℂ ⟶ Spec (CommRingCat.of ℤ) :=
  Spec.map (CommRingCat.ofHom (Int.castRingHom ℂ))

example : f5_complexStructure = Spec.map (CommRingCat.ofHom (Int.castRingHom ℂ)) := rfl

/-- The standard chart of index `I` of the complex Grassmannian, the preimage of `f5_chart`.
Source: EGA I, §9.7.3 and §9.7.5. -/
def f5_complexChart (k n : ℕ) (I : f5_PluckerIndex k n) :
    (f5_grassmannianOver k n (Spec ↧ℂ) f5_complexStructure).left.Opens :=
  pullback.snd f5_complexStructure (f5_grassmannian k n).hom ⁻¹ᵁ f5_chart k n I

example (k n : ℕ) (I : f5_PluckerIndex k n)
    (z : ComplexPoint (f5_grassmannianOver k n (Spec ↧ℂ) f5_complexStructure)) :
    z ∈ Point.overOpen (f5_complexChart k n I) ↔ z.underlying ∈ f5_complexChart k n I :=
  Iff.rfl

/-! ### Locally free quotients -/

/-- The pullback of the free sheaf of modules on `I` is the free sheaf on `I`.
Source: Mathlib `SheafOfModules.pullbackObjFreeIso`; EGA 0_I, §4.3.2. -/
def f5_pullbackFreeIso {X Y : Scheme.{0}} (f : X ⟶ Y) (I : Type) :
    (Scheme.Modules.pullback f).obj (SheafOfModules.free I) ≅ SheafOfModules.free I :=
  haveI : (SheafOfModules.pushforward f.toRingCatSheafHom).IsRightAdjoint :=
    (inferInstance : (Scheme.Modules.pushforward f).IsRightAdjoint)
  SheafOfModules.pullbackObjFreeIso _ I

example {X Y : Scheme.{0}} (f : X ⟶ Y) (I : Type) :
    (f5_pullbackFreeIso f I).hom ≫ (f5_pullbackFreeIso f I).inv = 𝟙 _ :=
  Iso.hom_inv_id _

/-- A sheaf of modules on a scheme is locally free of rank `r`: every point has an open
neighbourhood on which it is isomorphic to the free sheaf of rank `r`.
Source: EGA 0_I, §5.4.1; Stacks Project, Tag 01C5. -/
def f5_IsLocallyFreeOfRank {X : Scheme.{0}} (r : ℕ) (F : X.Modules) : Prop :=
  ∀ x : X, ∃ U : X.Opens, x ∈ U ∧ Nonempty (F.restrict U.ι ≅ SheafOfModules.free (Fin r))

example {X : Scheme.{0}} (r : ℕ) (F : X.Modules) :
    f5_IsLocallyFreeOfRank r F ↔ ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
      Nonempty (F.restrict U.ι ≅ SheafOfModules.free (Fin r)) := Iff.rfl

/-- A quotient `π` of the free sheaf of rank `n` on a scheme `G` over `Spec ℤ` is universal of
rank `k`: it is an epimorphism onto a sheaf `Q` locally free of rank `k`, and for every scheme
`T` over `Spec ℤ` and every such quotient `q` on `T` there is exactly one morphism `g : T ⟶ G`
over `Spec ℤ` along which `π` pulls back to `q`, up to isomorphism of quotients.
Source: EGA I, §9.7.4 (universal property of the Grassmannian); Stacks Project, Tag 089R. -/
def f5_IsUniversalQuotient (k n : ℕ) {G : Over (Spec (CommRingCat.of ℤ))}
    (Q : G.left.Modules) (π : SheafOfModules.free (Fin n) ⟶ Q) : Prop :=
  Epi π ∧ f5_IsLocallyFreeOfRank k Q ∧
    ∀ (T : Over (Spec (CommRingCat.of ℤ))) (F : T.left.Modules)
      (q : SheafOfModules.free (Fin n) ⟶ F), Epi q → f5_IsLocallyFreeOfRank k F →
      ∃! g : T ⟶ G, ∃ e : (Scheme.Modules.pullback g.left).obj Q ≅ F,
        (f5_pullbackFreeIso g.left (Fin n)).inv ≫ (Scheme.Modules.pullback g.left).map π ≫
          e.hom = q

example (k n : ℕ) {G : Over (Spec (CommRingCat.of ℤ))} (Q : G.left.Modules)
    (π : SheafOfModules.free (Fin n) ⟶ Q) (h : f5_IsUniversalQuotient k n Q π) : Epi π :=
  h.1

end HodgeLean.Foundations.Algebraic
