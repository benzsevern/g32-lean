import HodgeLean.Foundations.Program.G32Native.CanonicalAbelCore

/-! # Canonical normal producer and the U11 transport adapter -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint Bundle
namespace HodgeLean.Foundations.Program.G32Native

/-- Fibre-linear normal identification with both actual total-space continuity statements.
Source: Voisin, Hodge Theory and Complex Algebraic Geometry I, 7.1, normal bundle comparison. -/
structure CanonicalNormalIdentification (G : CanonicalAbelGeometry) where
  normalVector : ∀ x : ComplexPoint G.Q,
    canonicalNormalFibre G x ≃ₗ[ℂ] canonicalNormalComplement G x
  local_equation : ∀ (x : ComplexPoint G.Q) (ν : canonicalNormalFibre G x)
    (U : G.W.left.Opens)
    (s : SheafOfModules.unit U.toScheme.ringCatSheaf ⟶
      (Scheme.Modules.pullback U.ι).obj (Conormal.idealModule G.ι.left))
    (hx : Point.map G.ι x ∈ Point.overOpen U),
    ν (conormalLocalClass G.ι U s x hx) =
      conormalLocalDerivative G.ι (G.k + G.k) U s x (normalVector x ν).val
  lift : ComplexPoint G.Q → (Fin (G.k + G.k) → ℂ) → (Fin (G.k + 1) → ℂ)
  fibre : ∀ x : ComplexPoint G.Q, canonicalNormalFibre G x ≃ₗ[ℂ]
    (g32n_homogeneousLine G.k G.eQ x).submodule.dualAnnihilator
  coefficient_equation : ∀ (x : ComplexPoint G.Q) (ν : canonicalNormalFibre G x),
    (fibre x ν).val = canonicalAbelDifferential G lift x (normalVector x ν).val
  continuous_forward : @Continuous
    (TotalSpace (Fin G.k → ℂ) (canonicalNormalFibre G))
    (TotalSpace (Fin G.k → ℂ)
      (fun x => (g32n_homogeneousLine G.k G.eQ x).submodule.dualAnnihilator))
    (normalEvaluationTopology (Conormal.sheaf G.ι.left) G.k) (coefficientTotalTopology G)
    (fun z => ⟨z.proj, fibre z.proj z.2⟩)
  continuous_inverse : @Continuous
    (TotalSpace (Fin G.k → ℂ)
      (fun x => (g32n_homogeneousLine G.k G.eQ x).submodule.dualAnnihilator))
    (TotalSpace (Fin G.k → ℂ) (canonicalNormalFibre G))
    (coefficientTotalTopology G) (normalEvaluationTopology (Conormal.sheaf G.ι.left) G.k)
    (fun z => ⟨z.proj, (fibre z.proj).symm z.2⟩)

/-- Assemble the three geometric steps on the original canonical fibre.
Source: ACGH, Geometry of Algebraic Curves I, IV.1–IV.3; Voisin I, 7.1. -/
def canonicalNormalIdentification (G : CanonicalAbelGeometry) : CanonicalNormalIdentification G := by
  let p : ComplexPoint G.Z := Classical.choice (inferInstance : Nonempty (ComplexPoint G.Z))
  let lifts := canonical_abel_lifts_aux G p
  let F := Classical.choose lifts
  have hF := Classical.choose_spec lifts
  have hgeom := canonical_abel_equations_aux G p F hF
  let comparison := canonical_conormal_comparison_aux G p F hF hgeom
  let e := Classical.choose comparison
  have hc := Classical.choose_spec comparison
  exact {
    normalVector := e
    local_equation := hc.1
    lift := F
    fibre := fun x => (e x).trans
      (g32n_normalCoefficientEquiv G.W G.Q G.ι G.k G.eQ x
        (canonicalAbelDifferential G F x) (hgeom x).1.le (hgeom x).2)
    coefficient_equation := fun x ν => g32n_normalCoefficientEquiv_apply
      G.W G.Q G.ι G.k G.eQ x (canonicalAbelDifferential G F x)
        (hgeom x).1.le (hgeom x).2 (e x ν)
    continuous_forward := hc.2.1
    continuous_inverse := hc.2.2 }

/-- A fibre-linear identification gives the homeomorphism accepted by U11.
Source: Voisin I, 7.1, analytic normal bundle. -/
def CanonicalNormalIdentification.toHomeomorph {G : CanonicalAbelGeometry}
    (N : CanonicalNormalIdentification G) :
    @Homeomorph (TotalSpace (Fin G.k → ℂ) (canonicalNormalFibre G))
      (TotalSpace (Fin G.k → ℂ)
        (fun x => (g32n_homogeneousLine G.k G.eQ x).submodule.dualAnnihilator))
      (normalEvaluationTopology (Conormal.sheaf G.ι.left) G.k) (coefficientTotalTopology G) := by
  letI := normalEvaluationTopology (Conormal.sheaf G.ι.left) G.k
  letI := coefficientTotalTopology G
  exact {
    toFun z := ⟨z.proj, N.fibre z.proj z.2⟩
    invFun z := ⟨z.proj, (N.fibre z.proj).symm z.2⟩
    left_inv z := by
      apply TotalSpace.ext
      · rfl
      · exact heq_of_eq ((N.fibre z.proj).symm_apply_apply z.2)
    right_inv z := by
      apply TotalSpace.ext
      · rfl
      · exact heq_of_eq ((N.fibre z.proj).apply_symm_apply z.2)
    continuous_toFun := N.continuous_forward
    continuous_invFun := N.continuous_inverse
  }

/-- U10's total-space producer uses the original dual conormal and coefficient kernel.
Source: ACGH I, IV.1–IV.3; Voisin I, 7.1. -/
def canonicalNormalProducer (G : CanonicalAbelGeometry) :=
  (canonicalNormalIdentification G).toHomeomorph

/-- Feed U10's producer to the exact continuous identification transport utility of U11.
Source: Hartshorne, Algebraic Geometry, II.5 and II.8, functoriality of dual conormal fibres. -/
def transportCanonicalNormalProducer (G : CanonicalAbelGeometry)
    {M : G.Q.left.Modules} (E : M ≅ Conormal.sheaf G.ι.left) :
    @Homeomorph (TotalSpace (Fin G.k → ℂ) (normalFibreOfModule M))
      (TotalSpace (Fin G.k → ℂ)
        (fun x => (g32n_homogeneousLine G.k G.eQ x).submodule.dualAnnihilator))
      (normalEvaluationTopology M G.k) (coefficientTotalTopology G) := by
  letI := coefficientTotalTopology G
  exact transportNormalIdentification E G.k (canonicalNormalProducer G)

/-- Both the producer and its U11 adapter retain the original component point. -/
theorem transportCanonicalNormalProducer_proj (G : CanonicalAbelGeometry)
    {M : G.Q.left.Modules} (E : M ≅ Conormal.sheaf G.ι.left)
    (z : TotalSpace (Fin G.k → ℂ) (normalFibreOfModule M)) :
    (transportCanonicalNormalProducer G E z).proj = z.proj := rfl

/-- The U11 adapter retains evaluation against the inverse image of the actual local class.
Source: Hartshorne, Algebraic Geometry, II.8; Griffiths–Harris, ch. 3.4, normal-conormal pairing. -/
theorem transportCanonicalNormalProducer_local_equation (G : CanonicalAbelGeometry)
    {M : G.Q.left.Modules} (E : M ≅ Conormal.sheaf G.ι.left)
    (x : ComplexPoint G.Q) (ν : normalFibreOfModule M x) (U : G.W.left.Opens)
    (s : SheafOfModules.unit U.toScheme.ringCatSheaf ⟶
      (Scheme.Modules.pullback U.ι).obj (Conormal.idealModule G.ι.left))
    (hx : Point.map G.ι x ∈ Point.overOpen U) :
    ν (((Scheme.Modules.pullback x.left ⋙ moduleSpecΓFunctor).map E.inv)
      (conormalLocalClass G.ι U s x hx)) =
      conormalLocalDerivative G.ι (G.k + G.k) U s x
        ((canonicalNormalIdentification G).normalVector x (normalFibreTransport E x ν)).val :=
  (canonicalNormalIdentification G).local_equation x (normalFibreTransport E x ν) U s hx

/-- The vector in the U11 evaluation formula is the vector used by its coefficient output.
Source: ACGH, Geometry of Algebraic Curves I, IV.1–IV.3, Abel differential. -/
theorem transportCanonicalNormalProducer_coefficient_equation (G : CanonicalAbelGeometry)
    {M : G.Q.left.Modules} (E : M ≅ Conormal.sheaf G.ι.left)
    (x : ComplexPoint G.Q) (ν : normalFibreOfModule M x) :
    (transportCanonicalNormalProducer G E ⟨x, ν⟩).2.val =
      canonicalAbelDifferential G (canonicalNormalIdentification G).lift x
        ((canonicalNormalIdentification G).normalVector x (normalFibreTransport E x ν)).val :=
  (canonicalNormalIdentification G).coefficient_equation x (normalFibreTransport E x ν)

#print axioms transportCanonicalNormalProducer_local_equation
#print axioms transportCanonicalNormalProducer_coefficient_equation
#print axioms canonicalNormalIdentification
#print axioms CanonicalNormalIdentification.toHomeomorph
#print axioms canonicalNormalProducer
#print axioms transportCanonicalNormalProducer
#print axioms transportCanonicalNormalProducer_proj
end HodgeLean.Foundations.Program.G32Native
