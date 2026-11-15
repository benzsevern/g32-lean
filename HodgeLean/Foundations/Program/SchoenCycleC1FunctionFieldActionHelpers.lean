import HodgeLean.Foundations.Program.SchoenCycleStep1Field

/-! # The retained scheme action on rational functions -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry TopologicalSpace
namespace HodgeLean.Foundations.Program

/-- The scheme identity induces the identity on the generic stalk. -/
theorem s2e_c1_fieldPullback_id (X : Scheme) [IsIntegral X] :
    s2e_step1_fieldPullback X (𝟙 X) = RingHom.id X.functionField := by
  simp [s2e_step1_fieldPullback, TopCat.Presheaf.stalkCongr]

/-- Rational-function pullback reverses the scheme composition order. -/
theorem s2e_c1_fieldPullback_comp (X : Scheme) [IsIntegral X]
    (u v : X ⟶ X) [IsIso u] [IsIso v] :
    s2e_step1_fieldPullback X (u ≫ v) =
      (s2e_step1_fieldPullback X u).comp (s2e_step1_fieldPullback X v) := by
  have h : CommRingCat.ofHom (s2e_step1_fieldPullback X (u ≫ v)) =
      CommRingCat.ofHom (s2e_step1_fieldPullback X v) ≫
        CommRingCat.ofHom (s2e_step1_fieldPullback X u) := by
    apply Spec.map_injective
    rw [← cancel_mono (X.fromSpecStalk (genericPoint X))]
    calc
      Spec.map (CommRingCat.ofHom (s2e_step1_fieldPullback X (u ≫ v))) ≫
          X.fromSpecStalk (genericPoint X) = X.fromSpecStalk (genericPoint X) ≫ (u ≫ v) :=
        s2e_step1_fieldPullback_generic X (u ≫ v)
      _ = (Spec.map (CommRingCat.ofHom (s2e_step1_fieldPullback X u)) ≫
          X.fromSpecStalk (genericPoint X)) ≫ v := by
        rw [s2e_step1_fieldPullback_generic, Category.assoc]
      _ = Spec.map (CommRingCat.ofHom (s2e_step1_fieldPullback X u)) ≫
          (Spec.map (CommRingCat.ofHom (s2e_step1_fieldPullback X v)) ≫
            X.fromSpecStalk (genericPoint X)) := by
        rw [Category.assoc]
        exact congrArg (fun k =>
          Spec.map (CommRingCat.ofHom (s2e_step1_fieldPullback X u)) ≫ k)
          (s2e_step1_fieldPullback_generic X v).symm
      _ = _ := by rw [Spec.map_comp, Category.assoc]

  exact congrArg CommRingCat.Hom.hom h

/-- Two automorphisms over a separated base that agree on rational
functions agree as scheme morphisms. -/
theorem s2e_c1_fieldPullback_faithful
    {X T : Scheme} [IsIntegral X] (s : X ⟶ T) [IsSeparated s]
    (u v : X ⟶ X) [IsIso u] [IsIso v] (hbase : u ≫ s = v ≫ s)
    (h : s2e_step1_fieldPullback X u = s2e_step1_fieldPullback X v) : u = v := by
  haveI := s2e_step1_generic_dominant X
  apply ext_of_isDominant_of_isSeparated s hbase (X.fromSpecStalk (genericPoint X))
  rw [← s2e_step1_fieldPullback_generic, ← s2e_step1_fieldPullback_generic, h]

/-- An invertible scheme map induces an invertible rational-function map,
with inverse given by pullback along its scheme inverse. -/
def s2e_c1_fieldPullbackEquiv (X : Scheme) [IsIntegral X]
    (u : X ⟶ X) [IsIso u] : X.functionField ≃+* X.functionField where
  toFun := s2e_step1_fieldPullback X u
  invFun := s2e_step1_fieldPullback X (inv u)
  left_inv x := by
    have h := s2e_c1_fieldPullback_comp X (inv u) u
    simp only [IsIso.inv_hom_id, s2e_c1_fieldPullback_id] at h
    exact congrArg (fun f : X.functionField →+* X.functionField => f x) h.symm
  right_inv x := by
    have h := s2e_c1_fieldPullback_comp X u (inv u)
    simp only [IsIso.hom_inv_id, s2e_c1_fieldPullback_id] at h
    exact congrArg (fun f : X.functionField →+* X.functionField => f x) h.symm
  map_mul' := (s2e_step1_fieldPullback X u).map_mul
  map_add' := (s2e_step1_fieldPullback X u).map_add

/-- A deck automorphism fixes the actual embedded base function field
whenever the embedding retains its generic-point square. -/
theorem s2e_c1_fieldPullback_fixes_base
    {X Y : Scheme} [IsIntegral X] [IsIntegral Y] (f : X ⟶ Y)
    (φ : Y.functionField →+* X.functionField)
    (hφ : Spec.map (CommRingCat.ofHom φ) ≫ Y.fromSpecStalk (genericPoint Y) =
      X.fromSpecStalk (genericPoint X) ≫ f)
    (u : X ⟶ X) [IsIso u] (hu : u ≫ f = f) :
    (s2e_step1_fieldPullback X u).comp φ = φ := by
  have h : CommRingCat.ofHom φ ≫ CommRingCat.ofHom (s2e_step1_fieldPullback X u) =
      CommRingCat.ofHom φ := by
    apply Spec.map_injective
    rw [← cancel_mono (Y.fromSpecStalk (genericPoint Y))]
    calc
      Spec.map (CommRingCat.ofHom φ ≫
          CommRingCat.ofHom (s2e_step1_fieldPullback X u)) ≫
          Y.fromSpecStalk (genericPoint Y) =
          Spec.map (CommRingCat.ofHom (s2e_step1_fieldPullback X u)) ≫
            (Spec.map (CommRingCat.ofHom φ) ≫ Y.fromSpecStalk (genericPoint Y)) := by
        rw [Spec.map_comp, Category.assoc]
      _ = Spec.map (CommRingCat.ofHom (s2e_step1_fieldPullback X u)) ≫
          (X.fromSpecStalk (genericPoint X) ≫ f) := by rw [hφ]
      _ = (Spec.map (CommRingCat.ofHom (s2e_step1_fieldPullback X u)) ≫
          X.fromSpecStalk (genericPoint X)) ≫ f := (Category.assoc _ _ _).symm
      _ = (X.fromSpecStalk (genericPoint X) ≫ u) ≫ f := by
        rw [s2e_step1_fieldPullback_generic]
      _ = X.fromSpecStalk (genericPoint X) ≫ f := by rw [Category.assoc, hu]
      _ = Spec.map (CommRingCat.ofHom φ) ≫ Y.fromSpecStalk (genericPoint Y) := hφ.symm
  exact congrArg CommRingCat.Hom.hom h

/-- The rational-function equivalence of a deck map is linear over the
embedded function field of the base. -/
def s2e_c1_deckFunctionFieldEquiv
    {X Y : Scheme} [IsIntegral X] [IsIntegral Y] (f : X ⟶ Y)
    (φ : Y.functionField →+* X.functionField)
    (hφ : Spec.map (CommRingCat.ofHom φ) ≫ Y.fromSpecStalk (genericPoint Y) =
      X.fromSpecStalk (genericPoint X) ≫ f)
    (u : X ⟶ X) [IsIso u] (hu : u ≫ f = f) :
    letI := φ.toAlgebra
    X.functionField ≃ₐ[Y.functionField] X.functionField := by
  letI := φ.toAlgebra
  exact { s2e_c1_fieldPullbackEquiv X u with
    commutes' := fun r => congrArg
      (fun k : Y.functionField →+* X.functionField => k r)
      (s2e_c1_fieldPullback_fixes_base f φ hφ u hu) }

/-- Inverse pullback gives a group homomorphism from the actual automorphism
group over the base to its function-field algebra automorphism group. -/
def s2e_c1_deckFunctionFieldHom
    {X Y : Scheme} [IsIntegral X] [IsIntegral Y] (f : X ⟶ Y)
    (φ : Y.functionField →+* X.functionField)
    (hφ : Spec.map (CommRingCat.ofHom φ) ≫ Y.fromSpecStalk (genericPoint Y) =
      X.fromSpecStalk (genericPoint X) ≫ f) :
    letI := φ.toAlgebra
    Aut (Over.mk f) →* (X.functionField ≃ₐ[Y.functionField] X.functionField) := by
  letI := φ.toAlgebra
  exact {
    toFun := fun u => s2e_c1_deckFunctionFieldEquiv f φ hφ u.asIso.inv.left (Over.w _)
    map_one' := by
      ext r
      change s2e_step1_fieldPullback X (𝟙 X) r = r
      rw [s2e_c1_fieldPullback_id]
      rfl
    map_mul' := fun u v => by
      ext r
      change s2e_step1_fieldPullback X (u.asIso.inv.left ≫ v.asIso.inv.left) r =
        s2e_step1_fieldPullback X u.asIso.inv.left
          (s2e_step1_fieldPullback X v.asIso.inv.left r)
      rw [s2e_c1_fieldPullback_comp]
      rfl }

/-- The function-field action of the actual automorphism group over a
separated base is faithful. -/
theorem s2e_c1_deckFunctionFieldHom_injective
    {X Y : Scheme} [IsIntegral X] [IsIntegral Y] (f : X ⟶ Y) [IsSeparated f]
    (φ : Y.functionField →+* X.functionField)
    (hφ : Spec.map (CommRingCat.ofHom φ) ≫ Y.fromSpecStalk (genericPoint Y) =
      X.fromSpecStalk (genericPoint X) ≫ f) :
    Function.Injective (s2e_c1_deckFunctionFieldHom f φ hφ) := by
  letI := φ.toAlgebra
  intro u v h
  have hfield : s2e_step1_fieldPullback X u.asIso.inv.left =
      s2e_step1_fieldPullback X v.asIso.inv.left := by
    exact congrArg (fun e : X.functionField ≃ₐ[Y.functionField] X.functionField =>
      e.toRingEquiv.toRingHom) h
  have hinv : u.asIso.inv.left = v.asIso.inv.left :=
    s2e_c1_fieldPullback_faithful f _ _ ((Over.w _).trans (Over.w _).symm) hfield
  apply Aut.ext
  apply Iso.ext_inv
  exact Over.OverMorphism.ext hinv

end HodgeLean.Foundations.Program
