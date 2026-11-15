import HodgeLean.Foundations.Program.SchoenTowerN2bLocalProjectiveImmersion
import HodgeLean.Foundations.Program.SchoenTowerN2bFiniteProjectiveIndex
import HodgeLean.Foundations.Program.SchoenTowerN2bRegularizedMapCharts
import HodgeLean.Foundations.Program.SchoenTowerN2bGeometryHelpers
import HodgeLean.Foundations.Program.SchoenTowerN2bProjectiveHelpers
import HodgeLean.Foundations.Program.SchoenTowerN2bFiniteChartEmbeddings
import HodgeLean.Foundations.Program.SchoenTowerN2bSourceRegularization
import HodgeLean.Foundations.Program.SchoenTowerN2bRegularizedTransitions
import HodgeLean.Foundations.Program.SchoenTowerN2bSourceCover

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ProjectiveSpace
namespace HodgeLean.Foundations.Program
attribute [local instance] MvPolynomial.gradedAlgebra

theorem n2b_projective_of_projective_immersion
    (X : Over (Spec ↧ℂ)) [IsProper X.hom] (n : ℕ)
    (j : X.left ⟶ ℙ(Fin (n + 1); Spec ↧ℂ)) [IsImmersion j]
    (hj : j ≫ toBase (Fin (n + 1)) (Spec ↧ℂ) = X.hom) :
    IsProjective X.hom := by
  haveI : IsProper (j ≫ toBase (Fin (n + 1)) (Spec ↧ℂ)) := by
    rw [hj]
    infer_instance
  haveI : IsProper j := IsProper.of_comp j (toBase (Fin (n + 1)) (Spec ↧ℂ))
  haveI : IsClosedImmersion j :=
    IsClosedImmersion.of_isPreimmersion j j.isClosedMap.isClosed_range
  exact ⟨⟨⟨n, j, hj⟩⟩⟩

/-- An integral finite source over a projective complex base has a projective-space immersion.
Source: Hartshorne, Algebraic Geometry, II.5.17 and II.7.6. -/
theorem n2b_finite_source_projective_immersion
    {W B : Over (Spec ↧ℂ)} [IsIntegral W.left] [IsProjective B.hom]
    (β : W ⟶ B) [IsFinite β.left] :
    ∃ (n : ℕ) (j : W.left ⟶ ℙ(Fin (n + 1); Spec ↧ℂ)),
      IsImmersion j ∧ j ≫ toBase (Fin (n + 1)) (Spec ↧ℂ) = W.hom := by
  classical
  obtain ⟨n, ψ, hψ, hgen⟩ := n2b_finite_source_chart_embeddings β
  haveI : IsAffineHom ψ := hψ
  choose m v hv using hgen
  let I := {i : Fin (n + 1) // Nonempty (n2b_pullbackChart ψ i)}
  letI : Fintype I := Fintype.ofFinite I
  letI : ∀ i : I, Nonempty (n2b_pullbackChart ψ i.val) := fun i => i.prop
  let 𝒰 := n2b_pullbackChartCover ψ
  have hI : Nonempty I := by
    let i : Fin (n + 1) := 𝒰.idx (genericPoint W.left)
    obtain ⟨x, _⟩ := 𝒰.covers (genericPoint W.left)
    exact ⟨⟨i, ⟨x⟩⟩⟩
  let K := (Σ i : I, Fin (m i.val)) ⊕ I
  let c : K → I := Sum.elim Sigma.fst id
  let z : ∀ k : K, Γ(n2b_pullbackChart ψ (c k).val, ⊤) := fun k =>
    match k with
    | .inl ⟨i, a⟩ => v i.val a
    | .inr _ => 1
  obtain ⟨N, hN, hrep⟩ :=
    n2b_uniform_pullbackChart_representatives ψ (fun i : I => i.val) c z
  choose a ha using hrep
  have haself (k : K) : a k (c k) = z k :=
    n2b_regularized_chart_coefficient_self ψ (fun i : I => i.val) c z N a ha k
  have hapure (i b : I) : a (.inr i) b =
      n2b_pullbackChartCoord ψ b.val i.val ^ N :=
    n2b_regularized_pure_coefficient ψ i.val b.val N (a (.inr i) b) (ha (.inr i) b)
  have haone (i : I) : a (.inr i) i = 1 := by
    exact haself (.inr i)
  have hagen (i : I) (t : Fin (m i.val)) : a (.inl ⟨i, t⟩) i = v i.val t := by
    exact haself (.inl ⟨i, t⟩)
  let q : ∀ i : I, ULift.{0} ℤ →+* Γ(n2b_pullbackChart ψ i.val, ⊤) := fun _ =>
    (Int.castRingHom _).comp ULift.ringEquiv.toRingHom
  obtain ⟨g, hg⟩ := n2b_regularized_global_map ψ c z N a ha q Sum.inr haone
  have hpre (i : I) := n2b_regularized_map_preimage_chart ψ g
    (fun i k => a k i) q Sum.inr haone hg N hN hapure i
  let j : W.left ⟶ ProjectiveSpace K (Spec ↧ℂ) :=
    pullback.lift W.hom g (Subsingleton.elim _ _)
  let 𝒱 := n2b_nonemptyPullbackChartCover ψ
  let V : I → (ProjectiveSpace K (Spec ↧ℂ)).Opens := fun i =>
    pullback.snd (terminal.from (Spec ↧ℂ))
      (terminal.from (Proj (MvPolynomial.homogeneousSubmodule K (ULift.{0} ℤ)))) ⁻¹ᵁ
        Proj.basicOpen (MvPolynomial.homogeneousSubmodule K (ULift.{0} ℤ))
          (MvPolynomial.X (.inr i))
  have hjpre (i : I) : (n2b_pullbackChartι ψ i.val).opensRange = j ⁻¹ᵁ V i := by
    have hjg : j ≫ pullback.snd (terminal.from (Spec ↧ℂ))
        (terminal.from (Proj (MvPolynomial.homogeneousSubmodule K (ULift.{0} ℤ)))) = g :=
      pullback.lift_snd _ _ _
    have he := congrArg (fun f : W.left ⟶ Proj
        (MvPolynomial.homogeneousSubmodule K (ULift.{0} ℤ)) => f ⁻¹ᵁ
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule K (ULift.{0} ℤ))
        (MvPolynomial.X (.inr i))) hjg
    rw [Scheme.Hom.comp_preimage] at he
    exact (hpre i).trans he.symm
  haveI hlocal (i : I) : IsImmersion (n2b_pullbackChartι ψ i.val ≫ j) := by
    let s := n2b_pullbackChartι ψ i.val ≫ W.hom
    have heq : n2b_pullbackChartι ψ i.val ≫ j =
        pullback.lift s
          (Proj.fromOfGlobalSections (X := n2b_pullbackChart ψ i.val)
            (MvPolynomial.homogeneousSubmodule K (ULift.{0} ℤ))
            (MvPolynomial.eval₂Hom (q i) (fun k => a k i))
            (n2b_polynomial_evaluation_irrelevant (q i) (fun k => a k i) (.inr i) (haone i)))
          (Subsingleton.elim _ _) := by
      apply pullback.hom_ext
      · simp only [j, Category.assoc, pullback.lift_fst]
        rfl
      · simp only [j, Category.assoc, pullback.lift_snd]
        exact hg i
    rw [heq]
    haveI : IsClosedImmersion (AffineSpace.homOfVector s (v i.val)) := hv i.val
    exact n2b_local_projective_immersion s (q i) (fun k => a k i) (.inr i) (haone i)
      (m i.val) (v i.val) (fun t => .inl ⟨i, t⟩) (hagen i)
  haveI : ∀ i : 𝒱.I₀, IsImmersion (𝒱.f i ≫ j) := hlocal
  haveI : IsImmersion j := n2b_immersion_of_matching_charts j 𝒱 V hjpre
  letI : Nonempty K := hI.map Sum.inr
  obtain ⟨l, j', hj', hbase⟩ := n2b_finite_projective_index (κ := K) (Spec ↧ℂ)
  haveI : IsClosedImmersion j' := hj'
  refine ⟨l, j ≫ j', inferInstance, ?_⟩
  rw [Category.assoc, hbase]
  exact pullback.lift_fst _ _ _

theorem n2b_projective_of_finite_over_projective_base
    {W B : Over (Spec ↧ℂ)} [IsIntegral W.left] [IsProjective B.hom]
    (β : W ⟶ B) [IsFinite β.left] : IsProjective W.hom := by
  haveI : IsProper W.hom := n2b_proper_over_projective_base β
  obtain ⟨n, j, hj, hbase⟩ := n2b_finite_source_projective_immersion β
  haveI : IsImmersion j := hj
  exact n2b_projective_of_projective_immersion W n j hbase

end HodgeLean.Foundations.Program
