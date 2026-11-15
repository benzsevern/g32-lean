import HodgeLean.Foundations.Curves.SymmetricCharts.StageTwo.Checks
import HodgeLean.Foundations.Curves.SymmetricCharts.StageTwo.Proofs

/-! # Symmetric curve stage two interfaces

Retained projections, branch ideals and relative dimensions keep their scheme types.
HC no distance; AV milestone no distance.
-/
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open HodgeLean.Adapters HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.Curves.SymmetricCharts.StageTwo
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 400000
variable (C : Over (Spec ↧ℂ)) [IsIntegral C.left] [Smooth C.hom] [IsProjective C.hom]
/-- The specified categorical quotient has a unique projection-preserving comparison.
Source: SGA 1, Exposé V, §1.
HC no distance; AV milestone no distance.
-/
theorem retained_comparison (n : ℕ) (Q : Over (Spec ↧ℂ)) (q : g3_power C n ⟶ Q)
    (hinv : ∀ σ, s2_permute C n σ ≫ q = q)
    (huniv : ∀ (T : Over (Spec ↧ℂ)) (f : g3_power C n ⟶ T),
      (∀ σ, s2_permute C n σ ≫ f = f) → ∃! d : Q ⟶ T, q ≫ d = f) :
    ∃! e : symmetricPower C n ≅ Q, projection C n ≫ e.hom = q :=
  retained_comparison_aux C n Q q hinv huniv

/-- The curve quotient is smooth of relative dimension n, also in degree zero.
Source: Milne, Jacobian Varieties, §3.
HC no distance; AV milestone no distance.
-/
theorem smooth_dimension [SmoothOfRelativeDimension 1 C.hom] (n : ℕ) :
    SmoothOfRelativeDimension n (symmetricPower C n).hom ∧
      topologicalKrullDim (symmetricPower C n).left = n :=
  smooth_dimension_aux C n

/-- The empty symmetric power is the base with its actual projection.
Source: Milne, Jacobian Varieties, §3, empty effective divisor.
HC no distance; AV milestone no distance.
-/
theorem degree_zero : ∃ e : symmetricPower C 0 ≅ Over.mk (𝟙 (Spec ↧ℂ)),
    projection C 0 ≫ e.hom = 𝟙 _ :=
  degree_zero_aux C

/-- Distinct branch divisors have independent etale parameters at every divisor, including repeated support.
Source: Milne, Jacobian Varieties, §3; Hartshorne, Algebraic Geometry, II.8.
HC no distance; AV milestone no distance.
-/
theorem branch_coordinates [SmoothOfRelativeDimension 1 C.hom] (h k : ℕ) (hk : k ≤ h+1)
    (b : Fin k → ComplexPoint C) (hb : Function.Injective b)
    (x : ComplexPoint (symmetricPower C (h+1)))
    (hx : ∀ i, x.left (default : Spec ↧ℂ) ∈ (branchIdeal C h (b i)).support) :
    ∃ (V : (symmetricPower C (h+1)).left.Opens)
      (t : V.toScheme ⟶ (affine (h+1)).left),
      x.left (default : Spec ↧ℂ) ∈ V ∧ Etale t ∧
      t ≫ (affine (h+1)).hom = V.ι ≫ (symmetricPower C (h+1)).hom ∧
      ∀ i : Fin k, (branchIdeal C h (b i)).comap V.ι =
        (coordinateIdeal (h+1) ⟨i.val, lt_of_lt_of_le i.isLt hk⟩).comap t :=
  branch_coordinates_aux C h k hk b hb x hx

/-- Point insertion descends with the actual scheme kernel.
Source: Milne, Jacobian Varieties, §3; Schoen (1988), Lemma 2.2, p. 13.
HC no distance; AV milestone no distance.
-/
theorem point_addition [SmoothOfRelativeDimension 1 C.hom] (h : ℕ) (b : ComplexPoint C) :
    ∃! a : symmetricPower C h ⟶ symmetricPower C (h+1),
      projection C h ≫ a = s2c_branchInsertion C h b ≫ projection C (h+1) ∧
      IsClosedImmersion a.left ∧ a.left.ker = branchIdeal C h b :=
  point_addition_aux C h b

/-- Distinct point branches intersect scheme-theoretically with the specified conormal rank.
Source: Schoen (1988), Lemma 2.2, pp. 13–14; Hartshorne, Algebraic Geometry, II.8.
HC no distance; AV milestone no distance.
-/
theorem branch_intersections [SmoothOfRelativeDimension 1 C.hom] (h k : ℕ) (hk : k ≤ h+1)
    (b : Fin k → ComplexPoint C) (hb : Function.Injective b) :
    (∃ e : symmetricPower C (h+1-k) ≅ branchIntersection C h k b,
      projection C (h+1-k) ≫ e.hom ≫
        s2c_subschemeι (symmetricPower C (h+1)) (intersectionIdeal C h k b) =
        multipleInsertion C h k hk b ≫ projection C (h+1)) ∧
      SmoothOfRelativeDimension (h+1-k) (branchIntersection C h k b).hom ∧
      (∀ x : (branchIntersection C h k b).left,
        ∃ U : (branchIntersection C h k b).left.Opens, x ∈ U ∧
          Nonempty ((Scheme.Modules.pullback U.ι).obj
            (s2c_conormal (intersectionIdeal C h k b).subschemeι) ≅
            SheafOfModules.free (R := U.toScheme.ringCatSheaf) (Fin k))) :=
  branch_intersections_aux C h k hk b hb

/-- More distinct point branches than the degree have empty scheme intersection.
Source: Milne, Jacobian Varieties, §3, effective divisors.
HC no distance; AV milestone no distance.
-/
theorem excess_branches [SmoothOfRelativeDimension 1 C.hom] (h k : ℕ) (hk : h+1 < k)
    (b : Fin k → ComplexPoint C) (hb : Function.Injective b) :
    IsEmpty (branchIntersection C h k b).left :=
  excess_branches_aux C h k hk b hb

/-- Curve parameters descend to elementary symmetric coordinates with the actual projection and reflected stabilizers.
Source: Milne, Jacobian Varieties, §3; SGA 1, Exposé V, §1.
HC no distance; AV milestone no distance.
-/
theorem curve_coordinate_transport [SmoothOfRelativeDimension 1 C.hom] (n : ℕ) (z : Fin n → ComplexPoint C) :
    ∃ (U : C.left.Opens) (t : U.toScheme ⟶ (affine 1).left)
      (u : Fin n → (Spec ↧ℂ ⟶ U.toScheme))
      (V : (symmetricPower C n).left.Opens)
      (v : Spec ↧ℂ ⟶ V.toScheme) (c : V.toScheme ⟶ (affine n).left),
      IsAffineOpen U ∧ Etale t ∧ Etale c ∧
      t ≫ (affine 1).hom = U.ι ≫ C.hom ∧
      c ≫ (affine n).hom = V.ι ≫ (symmetricPower C n).hom ∧
      (∀ i, u i ≫ U.ι = (z i).left) ∧
      v ≫ V.ι = (s2_lift n z ≫ projection C n).left ∧
      (∀ i j, u i ≫ t = u j ≫ t ↔ z i = z j) ∧
      ∀ (y : Fin n → ComplexPoint C) (uy : Fin n → (Spec ↧ℂ ⟶ U.toScheme))
        (w : Spec ↧ℂ ⟶ V.toScheme),
        (∀ i, uy i ≫ U.ι = (y i).left) →
        w ≫ V.ι = (s2_lift n y ≫ projection C n).left →
        ∀ j : Fin n,
          (Scheme.ΓSpecIso ↧ℂ).hom
            ((w ≫ c).appTop ((Scheme.ΓSpecIso ↧(MvPolynomial (Fin n) ℂ)).inv
              (MvPolynomial.X j))) =
          MvPolynomial.eval (fun i => (Scheme.ΓSpecIso ↧ℂ).hom
            ((uy i ≫ t).appTop ((Scheme.ΓSpecIso ↧(MvPolynomial (Fin 1) ℂ)).inv
              (MvPolynomial.X (0 : Fin 1)))))
            (MvPolynomial.esymm (Fin n) ℂ (j.val+1)) :=
  curve_coordinate_transport_aux C n z

-- Concrete independent example for `retained_comparison`.
example : Nonempty (g3_power E 1 ≅ symmetricPower E 1) := retained_comparison_example

-- Concrete independent example for `smooth_dimension`.
example : topologicalKrullDim (symmetricPower E 1).left = 1 := smooth_dimension_example

-- Concrete independent example for `degree_zero`.
example : Nonempty (g3_power E 0 ≅ symmetricPower E 0) := degree_zero_example

-- Concrete independent example for `branch_coordinates`.
example : coordinateIdeal 2 (0 : Fin 2) ≠ coordinateIdeal 2 (1 : Fin 2) := branch_coordinates_example

-- Concrete independent example for `point_addition`.
example : ∀ b : ComplexPoint (affine 1), s2c_branchInsertion (affine 1) 1 b ≫ g3_proj (affine 1) 2 (1 : Fin 2) = g3_proj (affine 1) 1 (0 : Fin 1) := point_addition_example

-- Concrete independent example for `branch_intersections`.
example : coordinateIdeal 2 (0 : Fin 2) ⊔ coordinateIdeal 2 (0 : Fin 2) ≠ coordinateIdeal 2 (0 : Fin 2) ⊔ coordinateIdeal 2 (1 : Fin 2) := branch_intersections_example

-- Concrete independent example for `excess_branches`.
example : Nonempty (branchIntersection E 0 2 (fun _ => Over.homMk finitePoint finitePoint_over)).left := excess_branches_example

-- Concrete independent example for `curve_coordinate_transport`.
example : ∃ z : Fin 2 → ComplexPoint (affine 1), z ∘ Equiv.swap (0 : Fin 2) 1 = z ∧ Equiv.swap (0 : Fin 2) 1 ≠ Equiv.refl _ := curve_coordinate_transport_example

end HodgeLean.Foundations.Curves.SymmetricCharts.StageTwo
