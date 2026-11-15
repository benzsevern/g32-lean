import HodgeLean.Foundations.Program.ComponentTransportChainStages
import HodgeLean.Foundations.Program.ComponentTransportNormalizedPath
import HodgeLean.Foundations.Program.ComponentTransportUnlabelled

/-! # Proofs for the restored certified unlabelled chain
HC no distance; AV milestone no distance.
-/

noncomputable section
open Set Manifold Filter Topology HodgeLean.Papers
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint HodgeLean.RealDefs
open HodgeLean.Foundations HodgeLean.Foundations.Symplectic HodgeLean.Adapters TopologicalSpace
open scoped ContDiff TensorProduct
namespace HodgeLean.Foundations.Program
attribute [local instance] b4cov_sphChartedSpace b4cov_sph_isManifold
attribute [local instance] b65z_SharedFamily.topC b65z_SharedFamily.chartC
  b65z_SharedFamily.manC b65z_SharedFamily.t2C b65z_SharedFamily.compactC
  b65z_SharedFamily.connectedC b65z_SharedFamily.actionC b65z_SharedFamily.totalChart
  b65z_SharedFamily.totalMan b65z_SharedFamily.fibreChart b65z_SharedFamily.fibreMan
  b65z_SharedFamily.fibreT2 b65z_SharedFamily.fibreCompact b65z_SharedFamily.fibreConnected
  b65z_SharedFamily.fibreFaithful

attribute [local instance] rf8_SharedFamily.topC rf8_SharedFamily.chartC
  rf8_SharedFamily.manC rf8_SharedFamily.t2C rf8_SharedFamily.compactC
  rf8_SharedFamily.connectedC rf8_SharedFamily.actionC rf8_SharedFamily.totalChart
  rf8_SharedFamily.totalMan rf8_SharedFamily.fibreChart rf8_SharedFamily.fibreMan
  rf8_SharedFamily.fibreT2 rf8_SharedFamily.fibreCompact rf8_SharedFamily.fibreConnected
  rf8_SharedFamily.fibreFaithful

/-- Retained reference family with the named root monodromy.
Source: `rf8_shared_root`; `mr_loop_existsUnique`. -/
theorem b65y_reference_root : ∃ (R : rf8_SharedFamily)
    (v₀ : R.atlas.π ⁻¹' {b63gP_basePoint}),
    ∀ i, R.atlas.hπ.fundamentalGroupToMulOpposite v₀ (b63gP_loops i) =
      MulOpposite.op (b4b_root i) := by
  obtain ⟨R, y₀, γ, v₀, hγ, hroot⟩ := rf8_shared_root
  have hy : y₀ = b63gP_basePoint := by
    apply Subtype.ext
    obtain ⟨q, hq, -⟩ := hγ 12
    calc
      (y₀ : OnePoint ℂ) = mr_curve 12 0 := by simpa using hq 0
      _ = (b63gP_basePoint : OnePoint ℂ) := by
        change mr_curve 12 0 = ((mr_basePoint : ℂ) : OnePoint ℂ)
        simp [mr_curve, mr_outer, mr_basePoint]
  subst y₀
  have hγeq : γ = b63gP_loops := by
    funext i
    exact (mr_loop_existsUnique mr_base b63gP_s₀.property b63gP_basePoint rfl i).unique
      (hγ i) (mr_loop_existsUnique mr_base b63gP_s₀.property b63gP_basePoint rfl i).exists.choose_spec
  subst γ
  exact ⟨R, v₀, hroot⟩

set_option maxHeartbeats 400000 in
theorem b65y_certified_chain_unlabelled_aux (p : Fin 12 → ℂ)
    (hp : ∀ k : Fin 12,
      |(p (b65b_boxIndex k)).re - ((b65b_boxCentre k).1 : ℝ)| < (1/10000 : ℝ) ∧
      |(p (b65b_boxIndex k)).im - ((b65b_boxCentre k).2 : ℝ)| < (1/10000 : ℝ) ∧
      b65r_P (b65b_boxFibre k) (p (b65b_boxIndex k)) = 0)
    (g : Fin 13 → b4b_Group) (D : b65z_SharedFamily (b65z_centre p) g)
    (e : b65s_sphere ≃ₜ b6t_punctured (b65z_centre p))
    (he : ∀ z, (e z : OnePoint ℂ) = b65p_mobius (p 10) (p 11) z)
    (x : b65s_regular) (u₀ : D.atlas.π ⁻¹' {e (b65s_inclusion x)})
    (δ : Fin 13 → Path x x)
    (hδ : ∀ i s, (δ i s).val = b65b_inverseNormalization (b65b_lasso (b65x_slot i) s))
    (hmono : ∀ i, ((D.atlas.hπ.fundamentalGroupToMulOpposite u₀).comp
        (FundamentalGroup.map ((⟨e, e.continuous⟩ : C(b65s_sphere, b6t_punctured (b65z_centre p))).comp b65s_inclusion) x))
          (FundamentalGroup.fromPath ⟦δ i⟧) = MulOpposite.op (b65b_initial i)⁻¹)
    (C : ((Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ))ˣ)
    (hT : ∀ η : Path x x,
      b65f_transport (Fin 4 → ℂ) b65r_pullback (fun t ↦ (η.extend t).val) =
        C.val * (b65s_column ((D.atlas.hπ.fundamentalGroupToMulOpposite u₀).comp
          (FundamentalGroup.map ((⟨e, e.continuous⟩ : C(b65s_sphere, b6t_punctured (b65z_centre p))).comp b65s_inclusion) x))
            (FundamentalGroup.fromPath ⟦η⟧)).val * (C⁻¹).val)
    (R : rf8_SharedFamily)
    (v₀ : R.atlas.π ⁻¹' {b63gP_basePoint})
    (hroot : ∀ i, R.atlas.hπ.fundamentalGroupToMulOpposite v₀ (b63gP_loops i) =
      MulOpposite.op (b4b_root i)) :
    ∃ H : b65y_UnlabelledHurwitzChain,
      H.chart 0 = (⟨mr_base, b4b_root, b65z_ofRetained R⟩ : b65y_Chart) ∧ H.chart (Fin.last H.n) = (⟨b65z_centre p, g, D⟩ : b65y_Chart) :=
  b65v_chain_of_normalized_path p g D e x u₀ δ hmono R v₀ hroot
    (b65v_normalized_path p hp e he x δ hδ)

set_option maxHeartbeats 400000 in
theorem b65y_rational_composition_u_aux (p : Fin 12 → ℂ)
    (hp : ∀ k : Fin 12,
      |(p (b65b_boxIndex k)).re - ((b65b_boxCentre k).1 : ℝ)| < (1/10000 : ℝ) ∧
      |(p (b65b_boxIndex k)).im - ((b65b_boxCentre k).2 : ℝ)| < (1/10000 : ℝ) ∧
      b65r_P (b65b_boxFibre k) (p (b65b_boxIndex k)) = 0)
    (g : Fin 13 → b4b_Group) (D : b65z_SharedFamily (b65z_centre p) g)
    (e : b65s_sphere ≃ₜ b6t_punctured (b65z_centre p))
    (he : ∀ z, (e z : OnePoint ℂ) = b65p_mobius (p 10) (p 11) z)
    (x : b65s_regular) (u₀ : D.atlas.π ⁻¹' {e (b65s_inclusion x)})
    (δ : Fin 13 → Path x x)
    (hδ : ∀ i s, (δ i s).val = b65b_inverseNormalization (b65b_lasso (b65x_slot i) s))
    (hmono : ∀ i, ((D.atlas.hπ.fundamentalGroupToMulOpposite u₀).comp
        (FundamentalGroup.map ((⟨e, e.continuous⟩ : C(b65s_sphere, b6t_punctured (b65z_centre p))).comp b65s_inclusion) x))
          (FundamentalGroup.fromPath ⟦δ i⟧) = MulOpposite.op (b65b_initial i)⁻¹)
    (C : ((Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ))ˣ)
    (hT : ∀ η : Path x x,
      b65f_transport (Fin 4 → ℂ) b65r_pullback (fun t ↦ (η.extend t).val) =
        C.val * (b65s_column ((D.atlas.hπ.fundamentalGroupToMulOpposite u₀).comp
          (FundamentalGroup.map ((⟨e, e.continuous⟩ : C(b65s_sphere, b6t_punctured (b65z_centre p))).comp b65s_inclusion) x))
            (FundamentalGroup.fromPath ⟦η⟧)).val * (C⁻¹).val)
    (R : rf8_SharedFamily)
    (v₀ : R.atlas.π ⁻¹' {b63gP_basePoint})
    (hroot : ∀ i, R.atlas.hπ.fundamentalGroupToMulOpposite v₀ (b63gP_loops i) =
      MulOpposite.op (b4b_root i)) :
    ∃ e : b65y_lattice (⟨b65z_centre p, g, D⟩ : b65y_Chart) ≃ₗ[ℤ] b65y_lattice (⟨mr_base, b4b_root, b65z_ofRetained R⟩ : b65y_Chart),
      (∀ x, e (D.A (b65z_s₀ (b65z_centre p)) x) = R.A b63gP_s₀ (e x)) ∧
      (∀ x y, b65y_pairing (⟨mr_base, b4b_root, b65z_ofRetained R⟩ : b65y_Chart) (e x) (e y) = b65y_pairing (⟨b65z_centre p, g, D⟩ : b65y_Chart) x y) ∧
      ∀ x y, b60_E.baseChange ℚ
        (b63gW_marking R v₀ hroot (e.baseChange ℤ ℚ _ _ x))
        (b63gW_marking R v₀ hroot (e.baseChange ℤ ℚ _ _ y)) =
        (b65y_pairing (⟨b65z_centre p, g, D⟩ : b65y_Chart)).baseChange ℚ x y := by
  obtain ⟨H, hH⟩ := b65y_certified_chain_unlabelled_aux p hp g D e he x u₀ δ hδ hmono C hT R v₀ hroot
  exact b65y_rational_composition_of_chain_u p g D R v₀ hroot H hH

set_option maxHeartbeats 400000 in
theorem b65y_marking_u_aux (p : Fin 12 → ℂ)
    (hp : ∀ k : Fin 12,
      |(p (b65b_boxIndex k)).re - ((b65b_boxCentre k).1 : ℝ)| < (1/10000 : ℝ) ∧
      |(p (b65b_boxIndex k)).im - ((b65b_boxCentre k).2 : ℝ)| < (1/10000 : ℝ) ∧
      b65r_P (b65b_boxFibre k) (p (b65b_boxIndex k)) = 0)
    (g : Fin 13 → b4b_Group) (D : b65z_SharedFamily (b65z_centre p) g)
    (e : b65s_sphere ≃ₜ b6t_punctured (b65z_centre p))
    (he : ∀ z, (e z : OnePoint ℂ) = b65p_mobius (p 10) (p 11) z)
    (x : b65s_regular) (u₀ : D.atlas.π ⁻¹' {e (b65s_inclusion x)})
    (δ : Fin 13 → Path x x)
    (hδ : ∀ i s, (δ i s).val = b65b_inverseNormalization (b65b_lasso (b65x_slot i) s))
    (hmono : ∀ i, ((D.atlas.hπ.fundamentalGroupToMulOpposite u₀).comp
        (FundamentalGroup.map ((⟨e, e.continuous⟩ : C(b65s_sphere, b6t_punctured (b65z_centre p))).comp b65s_inclusion) x))
          (FundamentalGroup.fromPath ⟦δ i⟧) = MulOpposite.op (b65b_initial i)⁻¹)
    (C : ((Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ))ˣ)
    (hT : ∀ η : Path x x,
      b65f_transport (Fin 4 → ℂ) b65r_pullback (fun t ↦ (η.extend t).val) =
        C.val * (b65s_column ((D.atlas.hπ.fundamentalGroupToMulOpposite u₀).comp
          (FundamentalGroup.map ((⟨e, e.continuous⟩ : C(b65s_sphere, b6t_punctured (b65z_centre p))).comp b65s_inclusion) x))
            (FundamentalGroup.fromPath ⟦η⟧)).val * (C⁻¹).val) :
    ∃ m : (ℚ ⊗[ℤ] b63l_parameterLattice (b65z_centre p) D.C D.hC (b6t_polydisc (b65z_centre p)) (Subset.refl _) (b65z_s₀ (b65z_centre p))) ≃ₗ[ℚ] (ℚ ⊗[ℤ] b60_Lattice),
      (∀ y, m ((D.A (b65z_s₀ (b65z_centre p))).baseChange ℚ y) = b60_omega.baseChange ℚ (m y)) ∧
      ∀ y z, b60_E.baseChange ℚ (m y) (m z) =
        (b63e_singularQ (b65z_centre p) D.C D.hC (b6t_polydisc (b65z_centre p)) (Subset.refl _)
          (b65z_s₀ (b65z_centre p)) (D.P (b65z_s₀ (b65z_centre p)))
          (D.Q (b65z_s₀ (b65z_centre p)))).baseChange ℚ y z := by
  obtain ⟨R, v₀, hroot⟩ := b65y_reference_root
  obtain ⟨H, hH⟩ := b65y_certified_chain_unlabelled_aux p hp g D e he x u₀ δ hδ hmono C hT R v₀ hroot
  exact b65y_marking_of_chain_u p g D R v₀ hroot H hH

set_option maxHeartbeats 400000 in
theorem b65y_polarization_u_aux (p : Fin 12 → ℂ)
    (hp : ∀ k : Fin 12,
      |(p (b65b_boxIndex k)).re - ((b65b_boxCentre k).1 : ℝ)| < (1/10000 : ℝ) ∧
      |(p (b65b_boxIndex k)).im - ((b65b_boxCentre k).2 : ℝ)| < (1/10000 : ℝ) ∧
      b65r_P (b65b_boxFibre k) (p (b65b_boxIndex k)) = 0)
    (g : Fin 13 → b4b_Group) (D : b65z_SharedFamily (b65z_centre p) g)
    (e : b65s_sphere ≃ₜ b6t_punctured (b65z_centre p))
    (he : ∀ z, (e z : OnePoint ℂ) = b65p_mobius (p 10) (p 11) z)
    (x : b65s_regular) (u₀ : D.atlas.π ⁻¹' {e (b65s_inclusion x)})
    (δ : Fin 13 → Path x x)
    (hδ : ∀ i s, (δ i s).val = b65b_inverseNormalization (b65b_lasso (b65x_slot i) s))
    (hmono : ∀ i, ((D.atlas.hπ.fundamentalGroupToMulOpposite u₀).comp
        (FundamentalGroup.map ((⟨e, e.continuous⟩ : C(b65s_sphere, b6t_punctured (b65z_centre p))).comp b65s_inclusion) x))
          (FundamentalGroup.fromPath ⟦δ i⟧) = MulOpposite.op (b65b_initial i)⁻¹)
    (C : ((Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ))ˣ)
    (hT : ∀ η : Path x x,
      b65f_transport (Fin 4 → ℂ) b65r_pullback (fun t ↦ (η.extend t).val) =
        C.val * (b65s_column ((D.atlas.hπ.fundamentalGroupToMulOpposite u₀).comp
          (FundamentalGroup.map ((⟨e, e.continuous⟩ : C(b65s_sphere, b6t_punctured (b65z_centre p))).comp b65s_inclusion) x))
            (FundamentalGroup.fromPath ⟦η⟧)).val * (C⁻¹).val)
    (B : Module.Basis (Fin 12) ℤ (b63l_parameterLattice (b65z_centre p) D.C D.hC (b6t_polydisc (b65z_centre p)) (Subset.refl _) (b65z_s₀ (b65z_centre p))))
    (P : g32h_PrymFamily) (j : b6t_polydisc (b65z_centre p) ≃ P.S)
    (hj : ∀ t, P.tuple (j t) = (fun i ↦ b4b_toMatrix (g i)) ∧ P.fiber (j t) = b65z_fiber D B t) :
    (∀ t : b6t_polydisc (b65z_centre p),
      let Λ := b63l_parameterLattice (b65z_centre p) D.C D.hC (b6t_polydisc (b65z_centre p)) (Subset.refl _) t
      let E := b63e_singularQ (b65z_centre p) D.C D.hC (b6t_polydisc (b65z_centre p)) (Subset.refl _) t
        (D.P t) (D.Q t)
      let X := (P.fiber (j t)).X
      let h := g32h_fiber_polarized P (j t)
      letI := (torusCohomology_cupProductOf X).finite
      ∃ ε : (ℚ ⊗[ℤ] Λ) ≃ₗ[ℚ] HQ X 1,
        (∀ y, ε ((D.A t).baseChange ℚ y) = -(P.fiber (j t)).W.J (ε y)) ∧
        ∃ r : ℚ, r = 1 ∧ 0 < r ∧
          ∀ y z, polarizationForm (torusCohomology_cupProductOf X) h.nondegenerate
            (ε y) (ε z) = r * E.baseChange ℚ y z) ∧
    ∀ s, g32d_ParabolicPolarization (g32h_fiber_polarized P s) := by
  obtain ⟨R, v₀, hroot⟩ := b65y_reference_root
  obtain ⟨H, hH⟩ := b65y_certified_chain_unlabelled_aux p hp g D e he x u₀ δ hδ hmono C hT R v₀ hroot
  exact b65y_polarization_of_chain_u p g D R v₀ hroot H hH B P j hj

set_option maxHeartbeats 400000 in
theorem b65z_marking_u_aux (p : Fin 12 → ℂ)
    (hp : ∀ k : Fin 12,
      |(p (b65b_boxIndex k)).re - ((b65b_boxCentre k).1 : ℝ)| < (1/10000 : ℝ) ∧
      |(p (b65b_boxIndex k)).im - ((b65b_boxCentre k).2 : ℝ)| < (1/10000 : ℝ) ∧
      b65r_P (b65b_boxFibre k) (p (b65b_boxIndex k)) = 0)
    (g : Fin 13 → b4b_Group) (D : b65z_SharedFamily (b65z_centre p) g)
    (e : b65s_sphere ≃ₜ b6t_punctured (b65z_centre p))
    (he : ∀ z, (e z : OnePoint ℂ) = b65p_mobius (p 10) (p 11) z)
    (x : b65s_regular) (u₀ : D.atlas.π ⁻¹' {e (b65s_inclusion x)})
    (δ : Fin 13 → Path x x)
    (hδ : ∀ i s, (δ i s).val = b65b_inverseNormalization (b65b_lasso (b65x_slot i) s))
    (hmono : ∀ i, ((D.atlas.hπ.fundamentalGroupToMulOpposite u₀).comp
        (FundamentalGroup.map ((⟨e, e.continuous⟩ : C(b65s_sphere, b6t_punctured (b65z_centre p))).comp b65s_inclusion) x))
          (FundamentalGroup.fromPath ⟦δ i⟧) = MulOpposite.op (b65b_initial i)⁻¹)
    (C : ((Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ))ˣ)
    (hT : ∀ η : Path x x,
      b65f_transport (Fin 4 → ℂ) b65r_pullback (fun t ↦ (η.extend t).val) =
        C.val * (b65s_column ((D.atlas.hπ.fundamentalGroupToMulOpposite u₀).comp
          (FundamentalGroup.map ((⟨e, e.continuous⟩ : C(b65s_sphere, b6t_punctured (b65z_centre p))).comp b65s_inclusion) x))
            (FundamentalGroup.fromPath ⟦η⟧)).val * (C⁻¹).val) :
    ∃ m : (ℚ ⊗[ℤ] b63l_parameterLattice (b65z_centre p) D.C D.hC (b6t_polydisc (b65z_centre p)) (Subset.refl _) (b65z_s₀ (b65z_centre p))) ≃ₗ[ℚ] (ℚ ⊗[ℤ] b60_Lattice),
      (∀ y, m ((D.A (b65z_s₀ (b65z_centre p))).baseChange ℚ y) = b60_omega.baseChange ℚ (m y)) ∧
      ∀ y z, b60_E.baseChange ℚ (m y) (m z) =
        (b63e_singularQ (b65z_centre p) D.C D.hC (b6t_polydisc (b65z_centre p)) (Subset.refl _)
          (b65z_s₀ (b65z_centre p)) (D.P (b65z_s₀ (b65z_centre p)))
          (D.Q (b65z_s₀ (b65z_centre p)))).baseChange ℚ y z := by
  obtain ⟨R, v₀, hroot⟩ := b65y_reference_root
  obtain ⟨H, hH⟩ := b65y_certified_chain_unlabelled_aux p hp g D e he x u₀ δ hδ hmono C hT R v₀ hroot
  exact b65z_marking_of_chain_u p g D R v₀ hroot H hH

set_option maxHeartbeats 400000 in
theorem b65z_polarization_u_aux (p : Fin 12 → ℂ)
    (hp : ∀ k : Fin 12,
      |(p (b65b_boxIndex k)).re - ((b65b_boxCentre k).1 : ℝ)| < (1/10000 : ℝ) ∧
      |(p (b65b_boxIndex k)).im - ((b65b_boxCentre k).2 : ℝ)| < (1/10000 : ℝ) ∧
      b65r_P (b65b_boxFibre k) (p (b65b_boxIndex k)) = 0)
    (g : Fin 13 → b4b_Group) (D : b65z_SharedFamily (b65z_centre p) g)
    (e : b65s_sphere ≃ₜ b6t_punctured (b65z_centre p))
    (he : ∀ z, (e z : OnePoint ℂ) = b65p_mobius (p 10) (p 11) z)
    (x : b65s_regular) (u₀ : D.atlas.π ⁻¹' {e (b65s_inclusion x)})
    (δ : Fin 13 → Path x x)
    (hδ : ∀ i s, (δ i s).val = b65b_inverseNormalization (b65b_lasso (b65x_slot i) s))
    (hmono : ∀ i, ((D.atlas.hπ.fundamentalGroupToMulOpposite u₀).comp
        (FundamentalGroup.map ((⟨e, e.continuous⟩ : C(b65s_sphere, b6t_punctured (b65z_centre p))).comp b65s_inclusion) x))
          (FundamentalGroup.fromPath ⟦δ i⟧) = MulOpposite.op (b65b_initial i)⁻¹)
    (C : ((Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ))ˣ)
    (hT : ∀ η : Path x x,
      b65f_transport (Fin 4 → ℂ) b65r_pullback (fun t ↦ (η.extend t).val) =
        C.val * (b65s_column ((D.atlas.hπ.fundamentalGroupToMulOpposite u₀).comp
          (FundamentalGroup.map ((⟨e, e.continuous⟩ : C(b65s_sphere, b6t_punctured (b65z_centre p))).comp b65s_inclusion) x))
            (FundamentalGroup.fromPath ⟦η⟧)).val * (C⁻¹).val)
    (B : Module.Basis (Fin 12) ℤ (b63l_parameterLattice (b65z_centre p) D.C D.hC (b6t_polydisc (b65z_centre p)) (Subset.refl _) (b65z_s₀ (b65z_centre p))))
    (P : g32h_PrymFamily) (j : b6t_polydisc (b65z_centre p) ≃ P.S)
    (hj : ∀ t, P.tuple (j t) = (fun i ↦ b4b_toMatrix (g i)) ∧ P.fiber (j t) = b65z_fiber D B t) :
    (∀ t : b6t_polydisc (b65z_centre p),
      let Λ := b63l_parameterLattice (b65z_centre p) D.C D.hC (b6t_polydisc (b65z_centre p)) (Subset.refl _) t
      let E := b63e_singularQ (b65z_centre p) D.C D.hC (b6t_polydisc (b65z_centre p)) (Subset.refl _) t
        (D.P t) (D.Q t)
      let X := (P.fiber (j t)).X
      let h := g32h_fiber_polarized P (j t)
      letI := (torusCohomology_cupProductOf X).finite
      ∃ ε : (ℚ ⊗[ℤ] Λ) ≃ₗ[ℚ] HQ X 1,
        (∀ y, ε ((D.A t).baseChange ℚ y) = -(P.fiber (j t)).W.J (ε y)) ∧
        ∃ r : ℚ, r = 1 ∧ 0 < r ∧
          ∀ y z, polarizationForm (torusCohomology_cupProductOf X) h.nondegenerate
            (ε y) (ε z) = r * E.baseChange ℚ y z) ∧
    ∀ s, g32d_ParabolicPolarization (g32h_fiber_polarized P s) := by
  obtain ⟨R, v₀, hroot⟩ := b65y_reference_root
  obtain ⟨H, hH⟩ := b65y_certified_chain_unlabelled_aux p hp g D e he x u₀ δ hδ hmono C hT R v₀ hroot
  exact b65z_polarization_of_chain_u p g D R v₀ hroot H hH B P j hj

end HodgeLean.Foundations.Program
