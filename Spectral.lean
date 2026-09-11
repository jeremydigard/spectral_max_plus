/-
Copyright (c) 2026 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad
-/


module

public import Mathlib.Tropical.MaxPlus.Walk

/-!
# The max-plus spectral theorem

For an irreducible finite max-plus matrix, the maximum mean of its simple cycles is an
eigenvalue.  The eigenvector is the maximal normalized weight of a simple path from a critical
cycle.
-/

@[expose] public section

open WeightedDigraph

namespace List

theorem exists_eq_append_cons_of_mem {ι : Type*} {i : ι} {l : List ι} (hi : i ∈ l) :
    ∃ pre post, l = pre ++ i :: post := by
  induction l with
  | nil => simp at hi
  | cons x l ih =>
      simp only [mem_cons] at hi
      rcases hi with (rfl | hi)
      · exact ⟨[], l, rfl⟩
      · obtain ⟨pre, post, rfl⟩ := ih hi
        exact ⟨x :: pre, post, by simp⟩

end List

namespace WeightedDigraph

variable {ι : Type*} {G : WeightedDigraph ι} {r j i : ι}

/-- Extending a simple path either remains simple or deletes a nonpositive cycle. -/
theorem exists_simplePath_weight_ge_append (p : G.SimplePath r j) (hji : G.Edge j i)
    (lam : ℝ) (hcycles : ∀ c : G.SimpleCycle, c.normalizedWeight lam ≤ 0) :
    ∃ q : G.SimplePath r i,
      p.normalizedWeight lam + G.normalizedEdgeWeight lam j i ≤ q.normalizedWeight lam := by
  classical
  by_cases hi : i ∈ p.vertices
  · obtain ⟨pre, post, hp⟩ := List.exists_eq_append_cons_of_mem hi
    have hdecomp : p.vertices = (pre ++ [i]) ++ post := by
      rw [hp]
      simp [List.append_assoc]
    let q : G.SimplePath r i := {
      vertices := pre ++ [i]
      nonempty := by simp
      head_eq := by
        cases pre <;> simpa [hp] using p.head_eq
      last_eq := by simp
      chain := by
        have hall : List.IsChain G.Edge ((pre ++ [i]) ++ post) := by
          rw [← hdecomp]
          exact p.chain
        exact hall.left_of_append
      nodup := by
        have hall : ((pre ++ [i]) ++ post).Nodup := by
          rw [← hdecomp]
          exact p.nodup
        exact hall.of_append_left }
    have hright : p.vertices = pre ++ (i :: post) := hp
    let c : G.SimpleCycle := {
      vertices := i :: post
      nonempty := by simp
      nodup := by
        have hall : (pre ++ (i :: post)).Nodup := by
          rw [← hright]
          exact p.nodup
        exact hall.of_append_right
      chain := by
        have hall : List.IsChain G.Edge (pre ++ (i :: post)) := by
          rw [← hright]
          exact p.chain
        exact hall.right_of_append
      closing := by
        have hb : (i :: post).getLast (by simp) = j := by
          have hp_last : (pre ++ i :: post).getLast (by simp) = j := by
            simpa only [hp] using p.last_eq
          rw [← hp_last]
          exact (List.getLast_append_of_right_ne_nil pre (i :: post) (by simp)).symm
        change G.Edge ((i :: post).getLast (by simp)) i
        rw [hb]
        exact hji }
    have hweight : p.weight + G.weight j i = q.weight + c.weight := by
      rw [← p.chainWeight_append_singleton]
      have hover := G.chainWeight_overlap pre (post ++ [i]) i
      rw [hp]
      simpa only [q, c, SimplePath.weight, SimpleCycle.weight, List.append_assoc,
        List.singleton_append, List.cons_append, SimpleCycle.root, List.head_cons] using hover
    have hlength : p.length + 1 = q.length + c.length := by
      have plen : p.vertices.length = pre.length + 1 + post.length := by
        simp only [hp, List.length_append, List.length_cons]
        omega
      have plen' : p.length = pre.length + post.length := by
        unfold SimplePath.length
        rw [plen]
        omega
      have qlen : q.length = pre.length := by
        dsimp only [q, SimplePath.length]
        simp
      have clen : c.length = post.length + 1 := by
        dsimp only [c, SimpleCycle.length]
        simp
      rw [plen', qlen, clen]
      omega
    have hlengthR : (p.length : ℝ) + 1 = (q.length : ℝ) + c.length := by
      exact_mod_cast hlength
    have hid : p.normalizedWeight lam + G.normalizedEdgeWeight lam j i =
        q.normalizedWeight lam + c.normalizedWeight lam := by
      simp only [SimplePath.normalizedWeight, SimpleCycle.normalizedWeight,
        normalizedEdgeWeight]
      have hmul := congrArg (fun x : ℝ ↦ x * lam) hlengthR
      nlinarith [hweight, hmul]
    refine ⟨q, ?_⟩
    rw [hid]
    linarith [hcycles c]
  · let q := p.appendEdge hji hi
    refine ⟨q, ?_⟩
    rw [p.normalizedWeight_appendEdge hji hi]

/-- Sum an edgewise potential inequality along a nonempty directed list. -/
theorem chainWeight_add_head_le (u : ι → ℝ) (mu : ℝ)
    (hedge : ∀ {j i : ι}, G.Edge j i → G.weight j i + u j ≤ mu + u i)
    (l : List ι) (hne : l ≠ []) (hchain : l.IsChain G.Edge) :
    G.chainWeight l + u (l.head hne) ≤
      ((l.length - 1 : ℕ) : ℝ) * mu + u (l.getLast hne) := by
  induction l with
  | nil => exact (hne rfl).elim
  | cons x l ih =>
      cases l with
      | nil => simp
      | cons y l =>
          have hxy := hedge hchain.rel
          have htail := ih (by simp) hchain.tail
          have hlen : (((x :: y :: l).length - 1 : ℕ) : ℝ) =
              1 + (((y :: l).length - 1 : ℕ) : ℝ) := by
            norm_num
            ring
          simp only [List.head_cons] at htail
          simp only [chainWeight_cons_cons, List.head_cons]
          rw [List.getLast_cons (by simp : y :: l ≠ [])]
          rw [hlen]
          linarith

end WeightedDigraph

namespace Matrix

variable {ι : Type*} [Fintype ι] [Nonempty ι]
variable (A : Matrix ι ι RMax) (hA : A.IsMaxPlusIrreducible)

/-- Maximum mean weight among simple cycles. -/
noncomputable def maxCycleMean : ℝ :=
  by
    classical
    exact Finset.univ.sup'
      ⟨Classical.choice (IsMaxPlusIrreducible.exists_simpleCycle hA), Finset.mem_univ _⟩
      WeightedDigraph.SimpleCycle.meanWeight

theorem simpleCycle_mean_le_maxCycleMean (c : A.toWeightedDigraph.SimpleCycle) :
    c.meanWeight ≤ maxCycleMean A hA := by
  exact Finset.le_sup' _ (Finset.mem_univ c)

theorem exists_critical_simpleCycle :
    ∃ c : A.toWeightedDigraph.SimpleCycle, c.meanWeight = maxCycleMean A hA := by
  classical
  obtain ⟨c, -, hc⟩ := Finset.exists_mem_eq_sup'
    (show (Finset.univ : Finset A.toWeightedDigraph.SimpleCycle).Nonempty from
      ⟨Classical.choice (IsMaxPlusIrreducible.exists_simpleCycle hA), Finset.mem_univ _⟩)
    WeightedDigraph.SimpleCycle.meanWeight
  exact ⟨c, hc.symm⟩

/-- A chosen simple cycle of maximum mean. -/
noncomputable def criticalCycle : A.toWeightedDigraph.SimpleCycle :=
  Classical.choose (exists_critical_simpleCycle A hA)

@[simp] theorem criticalCycle_meanWeight :
    (criticalCycle A hA).meanWeight = maxCycleMean A hA :=
  Classical.choose_spec (exists_critical_simpleCycle A hA)

theorem simpleCycle_normalizedWeight_nonpos (c : A.toWeightedDigraph.SimpleCycle) :
    c.normalizedWeight (maxCycleMean A hA) ≤ 0 := by
  rw [c.normalizedWeight_eq_length_mul]
  exact mul_nonpos_of_nonneg_of_nonpos (by positivity)
    (sub_nonpos.mpr (simpleCycle_mean_le_maxCycleMean A hA c))

@[simp] theorem criticalCycle_normalizedWeight :
    (criticalCycle A hA).normalizedWeight (maxCycleMean A hA) = 0 := by
  rw [(criticalCycle A hA).normalizedWeight_eq_length_mul,
    criticalCycle_meanWeight A hA, sub_self, mul_zero]

/-- Root vertex of the chosen critical cycle. -/
noncomputable def criticalRoot : ι := (criticalCycle A hA).root

/-- Maximal normalized weight of a simple path from the critical root. -/
noncomputable def eigenPotential (i : ι) : ℝ :=
  Finset.univ.sup' (by
    classical
    exact ⟨Classical.choice (hA.simplePath (criticalRoot A hA) i), Finset.mem_univ _⟩)
    fun p : A.toWeightedDigraph.SimplePath (criticalRoot A hA) i ↦
      p.normalizedWeight (maxCycleMean A hA)

theorem simplePath_normalizedWeight_le_eigenPotential
    {i : ι} (p : A.toWeightedDigraph.SimplePath (criticalRoot A hA) i) :
    p.normalizedWeight (maxCycleMean A hA) ≤ eigenPotential A hA i := by
  exact Finset.le_sup'
    (fun q : A.toWeightedDigraph.SimplePath (criticalRoot A hA) i ↦
      q.normalizedWeight (maxCycleMean A hA)) (Finset.mem_univ p)

theorem exists_maximizing_simplePath (i : ι) :
    ∃ p : A.toWeightedDigraph.SimplePath (criticalRoot A hA) i,
      p.normalizedWeight (maxCycleMean A hA) = eigenPotential A hA i := by
  classical
  obtain ⟨p, -, hp⟩ := Finset.exists_mem_eq_sup'
    (show (Finset.univ : Finset
      (A.toWeightedDigraph.SimplePath (criticalRoot A hA) i)).Nonempty from
      ⟨Classical.choice (hA.simplePath (criticalRoot A hA) i), Finset.mem_univ _⟩)
    fun p : A.toWeightedDigraph.SimplePath (criticalRoot A hA) i ↦
      p.normalizedWeight (maxCycleMean A hA)
  exact ⟨p, hp.symm⟩

@[simp] theorem eigenPotential_root :
    eigenPotential A hA (criticalRoot A hA) = 0 := by
  apply le_antisymm
  · apply Finset.sup'_le
    intro p _
    rw [p.eq_refl]
    simp
  · simpa using (simplePath_normalizedWeight_le_eigenPotential A hA
      (WeightedDigraph.SimplePath.refl (criticalRoot A hA)))

theorem normalizedEdge_add_potential_le {j i : ι} (hji : A.HasEdge j i) :
    A.toWeightedDigraph.normalizedEdgeWeight (maxCycleMean A hA) j i +
        eigenPotential A hA j ≤ eigenPotential A hA i := by
  obtain ⟨p, hp⟩ := exists_maximizing_simplePath A hA j
  obtain ⟨q, hq⟩ := WeightedDigraph.exists_simplePath_weight_ge_append p hji
    (maxCycleMean A hA)
    (simpleCycle_normalizedWeight_nonpos A hA)
  rw [← hp]
  rw [add_comm]
  exact hq.trans (simplePath_normalizedWeight_le_eigenPotential A hA q)

theorem exists_saturated_incoming_edge (i : ι) :
    ∃ j, ∃ hji : A.HasEdge j i,
      A.toWeightedDigraph.normalizedEdgeWeight (maxCycleMean A hA) j i +
          eigenPotential A hA j = eigenPotential A hA i := by
  by_cases hir : i = criticalRoot A hA
  · subst i
    let c := criticalCycle A hA
    let j := c.vertices.getLast c.nonempty
    have hji : A.HasEdge j (criticalRoot A hA) := c.closing
    have hcycle : c.asPathToLast.normalizedWeight (maxCycleMean A hA) +
        A.toWeightedDigraph.normalizedEdgeWeight (maxCycleMean A hA) j
          (criticalRoot A hA) = 0 := by
      dsimp only [j]
      change c.asPathToLast.normalizedWeight (maxCycleMean A hA) +
          A.toWeightedDigraph.normalizedEdgeWeight (maxCycleMean A hA)
            (c.vertices.getLast c.nonempty) c.root = 0
      rw [← c.normalizedWeight_eq_path_add_closing]
      exact criticalCycle_normalizedWeight A hA
    have hpath := simplePath_normalizedWeight_le_eigenPotential A hA c.asPathToLast
    have hbellman := normalizedEdge_add_potential_le A hA hji
    rw [eigenPotential_root A hA] at hbellman
    refine ⟨j, hji, ?_⟩
    rw [eigenPotential_root A hA]
    dsimp only [j] at hcycle hbellman ⊢
    apply le_antisymm hbellman
    rw [← hcycle]
    calc
      c.asPathToLast.normalizedWeight (maxCycleMean A hA) +
          A.toWeightedDigraph.normalizedEdgeWeight (maxCycleMean A hA)
            (c.vertices.getLast c.nonempty) (criticalRoot A hA) ≤
        eigenPotential A hA (c.vertices.getLast c.nonempty) +
          A.toWeightedDigraph.normalizedEdgeWeight (maxCycleMean A hA)
            (c.vertices.getLast c.nonempty) (criticalRoot A hA) :=
        add_le_add_left hpath _
      _ = A.toWeightedDigraph.normalizedEdgeWeight (maxCycleMean A hA)
            (c.vertices.getLast c.nonempty) (criticalRoot A hA) +
          eigenPotential A hA (c.vertices.getLast c.nonempty) := add_comm _ _
  · obtain ⟨p, hp⟩ := exists_maximizing_simplePath A hA i
    have hdrop : p.vertices.dropLast ≠ [] := by
      obtain ⟨x, l, hl⟩ := List.exists_cons_of_ne_nil p.nonempty
      cases l with
      | nil =>
          exfalso
          have hhead : x = criticalRoot A hA := by simpa [hl] using p.head_eq
          have hlast : x = i := by simpa [hl] using p.last_eq
          exact hir (hlast.symm.trans hhead)
      | cons y l => simp [hl]
    let j := p.vertices.dropLast.getLast hdrop
    have hji : A.HasEdge j i := by
      have hedge := p.chain.rel_getLast_dropLast hdrop
      have hedge' : A.toWeightedDigraph.Edge (p.vertices.dropLast.getLast hdrop) i := by
        simpa only [p.last_eq] using hedge
      exact hedge'
    have hjiG : A.toWeightedDigraph.Edge j i := hji
    let q : A.toWeightedDigraph.SimplePath (criticalRoot A hA) j := {
      vertices := p.vertices.dropLast
      nonempty := hdrop
      head_eq := by
        rw [List.head_dropLast]
        exact p.head_eq
      last_eq := rfl
      chain := p.chain.dropLast
      nodup := by
        have hall : (p.vertices.dropLast ++ [p.vertices.getLast p.nonempty]).Nodup := by
          rw [List.dropLast_append_getLast p.nonempty]
          exact p.nodup
        exact hall.of_append_left }
    have hvertices : p.vertices = q.vertices ++ [i] := by
      calc
        p.vertices = p.vertices.dropLast ++ [p.vertices.getLast p.nonempty] :=
          (List.dropLast_append_getLast p.nonempty).symm
        _ = q.vertices ++ [i] := by simp only [q, p.last_eq]
    have hinot : i ∉ q.vertices := by
      have hn : (q.vertices ++ [i]).Nodup := by rw [← hvertices]; exact p.nodup
      have hd := (List.nodup_append'.mp hn).2.2
      simpa using hd
    have hqp : q.appendEdge hjiG hinot = p := by
      apply WeightedDigraph.SimplePath.ext
      change q.vertices ++ [i] = p.vertices
      exact hvertices.symm
    have hpweight : p.normalizedWeight (maxCycleMean A hA) =
        q.normalizedWeight (maxCycleMean A hA) +
          A.toWeightedDigraph.normalizedEdgeWeight (maxCycleMean A hA) j i := by
      rw [← hqp, q.normalizedWeight_appendEdge hjiG hinot]
    have hqle := simplePath_normalizedWeight_le_eigenPotential A hA q
    have hbellman := normalizedEdge_add_potential_le A hA hji
    refine ⟨j, hji, ?_⟩
    rw [← hp, hpweight]
    linarith

theorem eigenPotential_isMaxPlusRealEigenpair :
    A.IsMaxPlusRealEigenpair hA.hasNonzeroRows (maxCycleMean A hA)
      (eigenPotential A hA) := by
  funext i
  apply le_antisymm
  · apply A.maxPlusMulVecReal_le hA.hasNonzeroRows
    intro j hji
    have h := normalizedEdge_add_potential_le A hA hji
    rw [normalizedEdgeWeight, A.toWeightedDigraph_weight_of_edge hji] at h
    linarith
  · obtain ⟨j, hji, hsaturated⟩ := exists_saturated_incoming_edge A hA i
    have hmax := A.le_maxPlusMulVecReal hA.hasNonzeroRows (eigenPotential A hA) hji
    rw [normalizedEdgeWeight, A.toWeightedDigraph_weight_of_edge hji] at hsaturated
    linarith

/-- Every edge satisfies the potential inequality induced by a real eigenpair. -/
theorem edge_add_le_of_isMaxPlusRealEigenpair {hrow : A.HasNonzeroRows}
    {mu : ℝ} {u : ι → ℝ} (hmu : A.IsMaxPlusRealEigenpair hrow mu u)
    {j i : ι} (hji : A.HasEdge j i) :
    A.toWeightedDigraph.weight j i + u j ≤ mu + u i := by
  rw [A.toWeightedDigraph_weight_of_edge hji]
  calc
    (A i j).toReal hji + u j ≤ A.maxPlusMulVecReal hrow u i :=
      A.le_maxPlusMulVecReal hrow u hji
    _ = mu + u i := congrFun hmu i

/-- The mean weight of every finite closed walk is bounded by a real eigenvalue. -/
theorem closedWalk_mean_le_of_isMaxPlusRealEigenpair {hrow : A.HasNonzeroRows}
    {mu : ℝ} {u : ι → ℝ} (hmu : A.IsMaxPlusRealEigenpair hrow mu u)
    (c : A.toWeightedDigraph.ClosedWalk) : c.meanWeight ≤ mu := by
  have hsum := A.toWeightedDigraph.chainWeight_add_head_le u mu
    (fun _hji ↦ A.edge_add_le_of_isMaxPlusRealEigenpair hmu _hji)
    (c.vertices ++ [c.root]) (by simp) c.isChain_append_root
  have hbound : c.weight ≤ (c.length : ℝ) * mu := by
    have hlen : (c.vertices ++ [c.root]).length - 1 = c.length := by
      simp [WeightedDigraph.ClosedWalk.length]
    have hhead : (c.vertices ++ [c.root]).head (by simp) = c.root := by
      rw [List.head_append_of_ne_nil c.nonempty]
      simp [WeightedDigraph.ClosedWalk.root]
    have hlast : (c.vertices ++ [c.root]).getLast (by simp) = c.root := by simp
    rw [hlen, hhead, hlast] at hsum
    exact le_of_add_le_add_right hsum
  rw [WeightedDigraph.ClosedWalk.meanWeight]
  apply (div_le_iff₀ (by exact_mod_cast c.length_pos)).2
  simpa [mul_comm] using hbound

/-- The maximum simple-cycle mean also bounds every closed walk. -/
theorem closedWalk_mean_le_maxCycleMean (c : A.toWeightedDigraph.ClosedWalk) :
    c.meanWeight ≤ maxCycleMean A hA :=
  A.closedWalk_mean_le_of_isMaxPlusRealEigenpair
    (eigenPotential_isMaxPlusRealEigenpair A hA) c

/-- Characterization of the eigenvalue as the greatest mean of all finite closed walks. -/
theorem maxCycleMean_isGreatest_closedWalkMean :
    IsGreatest (Set.range fun c : A.toWeightedDigraph.ClosedWalk ↦ c.meanWeight)
      (maxCycleMean A hA) := by
  refine ⟨?_, ?_⟩
  · refine ⟨(criticalCycle A hA).toClosedWalk, ?_⟩
    simp
  · rintro _ ⟨c, rfl⟩
    exact closedWalk_mean_le_maxCycleMean A hA c

/-- A tropical eigenvalue has a nonzero eigenvector. -/
def IsMaxPlusEigenvalue (mu : RMax) : Prop :=
  ∃ v : ι → RMax, v ≠ 0 ∧ A *ᵥ v = fun i ↦ mu * v i

theorem mulVec_apply_ne_zero_of_edge {v : ι → RMax} {j i : ι}
    (hji : A.HasEdge j i) (hvj : v j ≠ 0) : (A *ᵥ v) i ≠ 0 := by
  intro hzero
  have hle : (A i j * v j).toWithBot ≤ ((A *ᵥ v) i).toWithBot := by
    change (A i j * v j).toWithBot ≤ RMax.toWithBot (∑ k, A i k * v k)
    rw [RMax.toWithBot_sum]
    exact Finset.le_sup (s := Finset.univ)
      (f := fun k ↦ (A i k * v k).toWithBot) (Finset.mem_univ j)
  rw [hzero, RMax.toWithBot_zero] at hle
  have hprod : A i j * v j ≠ 0 := by
    rw [RMax.ne_zero_iff_toWithBot_ne_bot, RMax.toWithBot_mul, WithBot.add_ne_bot]
    exact ⟨(RMax.ne_zero_iff_toWithBot_ne_bot _).mp hji,
      (RMax.ne_zero_iff_toWithBot_ne_bot _).mp hvj⟩
  exact (RMax.ne_zero_iff_toWithBot_ne_bot _).mp hprod (bot_unique hle)

theorem eigenvalue_ne_zero (hA : A.IsMaxPlusIrreducible) {mu : RMax}
    (hmu : A.IsMaxPlusEigenvalue mu) : mu ≠ 0 := by
  obtain ⟨v, hv, heig⟩ := hmu
  obtain ⟨j, hvj⟩ : ∃ j, v j ≠ 0 := by
    by_contra h
    push_neg at h
    apply hv
    funext i
    exact h i
  obtain ⟨i, hji⟩ := hA.hasNonzeroColumns j
  have hleft := A.mulVec_apply_ne_zero_of_edge hji hvj
  intro hzero
  apply hleft
  rw [congrFun heig i, hzero, zero_mul]

theorem eigenvector_apply_ne_zero (hA : A.IsMaxPlusIrreducible)
    {mu : RMax} {v : ι → RMax} (hv : v ≠ 0)
    (heig : A *ᵥ v = fun i ↦ mu * v i) (hmu : mu ≠ 0) : ∀ i, v i ≠ 0 := by
  obtain ⟨k, hvk⟩ : ∃ k, v k ≠ 0 := by
    by_contra h
    push_neg at h
    apply hv
    funext i
    exact h i
  intro i
  let p := Classical.choice (hA.simplePath k i)
  have hstep : ∀ ⦃x y : ι⦄, A.toWeightedDigraph.Edge x y → v x ≠ 0 → v y ≠ 0 := by
    intro x y hxy hvx hvy
    have hleft := A.mulVec_apply_ne_zero_of_edge hxy hvx
    apply hleft
    rw [congrFun heig y, hvy, mul_zero]
  have hall := p.chain.induction (fun x ↦ v x ≠ 0) p.vertices hstep (fun _ ↦ by
    simpa only [p.head_eq] using hvk)
  apply hall i
  simpa only [p.last_eq] using List.getLast_mem p.nonempty

theorem exists_real_eigenpair_of_maxPlusEigenpair (hA : A.IsMaxPlusIrreducible)
    {mu : RMax} {v : ι → RMax}
    (hv : v ≠ 0) (heig : A *ᵥ v = fun i ↦ mu * v i) :
    ∃ mur : ℝ, ∃ vr : ι → ℝ,
      mu = RMax.ofReal mur ∧ v = (fun i ↦ RMax.ofReal (vr i)) ∧
        A.IsMaxPlusRealEigenpair hA.hasNonzeroRows mur vr := by
  have hmune : mu ≠ 0 := A.eigenvalue_ne_zero hA ⟨v, hv, heig⟩
  have hvne := A.eigenvector_apply_ne_zero hA hv heig hmune
  let mur := mu.toReal hmune
  let vr : ι → ℝ := fun i ↦ (v i).toReal (hvne i)
  refine ⟨mur, vr, ?_, ?_, ?_⟩
  · exact (RMax.ofReal_toReal mu hmune).symm
  · funext i
    exact (RMax.ofReal_toReal (v i) (hvne i)).symm
  · funext i
    apply RMax.ofReal_injective
    have hi := congrFun heig i
    rw [show mu = RMax.ofReal mur by exact (RMax.ofReal_toReal mu hmune).symm,
      show v = (fun k ↦ RMax.ofReal (vr k)) by
        funext k; exact (RMax.ofReal_toReal (v k) (hvne k)).symm] at hi
    rw [A.mulVec_ofReal hA.hasNonzeroRows vr] at hi
    simpa only [RMax.ofReal_add, RMax.ofReal_inj] using hi

theorem existsUnique_realEigenvalue :
    ∃! mu : ℝ, ∃ v : ι → ℝ, A.IsMaxPlusRealEigenpair hA.hasNonzeroRows mu v := by
  refine ⟨maxCycleMean A hA, ⟨eigenPotential A hA,
    eigenPotential_isMaxPlusRealEigenpair A hA⟩, ?_⟩
  intro mu hmu
  obtain ⟨v, hv⟩ := hmu
  exact A.realEigenvalue_unique hA.hasNonzeroRows hv
    (eigenPotential_isMaxPlusRealEigenpair A hA)

/-- The max-plus spectral theorem for irreducible finite matrices. -/
theorem existsUnique_maxPlusEigenvalue (hA : A.IsMaxPlusIrreducible) :
    ∃! mu : RMax, A.IsMaxPlusEigenvalue mu := by
  let mu := RMax.ofReal (maxCycleMean A hA)
  let v : ι → RMax := fun i ↦ RMax.ofReal (eigenPotential A hA i)
  have hv : v ≠ 0 := by
    intro hz
    let i : ι := Classical.choice ‹Nonempty ι›
    have hi := congrFun hz i
    exact RMax.ofReal_ne_zero _ hi
  have heig : A *ᵥ v = fun i ↦ mu * v i :=
    A.isMaxPlusEigenpair_of_isMaxPlusRealEigenpair hA.hasNonzeroRows
      (eigenPotential_isMaxPlusRealEigenpair A hA)
  refine ⟨mu, ⟨v, hv, heig⟩, ?_⟩
  intro nu hnu
  obtain ⟨w, hw, heigw⟩ := hnu
  obtain ⟨nur, wr, hnuReal, -, hpair⟩ :=
    A.exists_real_eigenpair_of_maxPlusEigenpair hA hw heigw
  rw [hnuReal]
  change RMax.ofReal nur = RMax.ofReal (maxCycleMean A hA)
  exact congrArg RMax.ofReal (A.realEigenvalue_unique hA.hasNonzeroRows hpair
    (eigenPotential_isMaxPlusRealEigenpair A hA))

theorem unique_maxPlusEigenvalue_eq_maxCycleMean {mu : RMax} --est ce que l'on ne ne prouvrerait pas avant le spectral et on a juste le sprectral en interface avec le ∃! 
    (hA : A.IsMaxPlusIrreducible) (hmu : A.IsMaxPlusEigenvalue mu) :
    mu = RMax.ofReal (maxCycleMean A hA) := by
  let v : ι → RMax := fun i ↦ RMax.ofReal (eigenPotential A hA i)
  have hv : v ≠ 0 := by
    intro hz
    let i : ι := Classical.choice ‹Nonempty ι›
    have hi := congrFun hz i
    exact RMax.ofReal_ne_zero _ hi
  have hcanonical : A.IsMaxPlusEigenvalue (RMax.ofReal (maxCycleMean A hA)) := by
    refine ⟨v, hv, ?_⟩
    exact A.isMaxPlusEigenpair_of_isMaxPlusRealEigenpair hA.hasNonzeroRows
      (eigenPotential_isMaxPlusRealEigenpair A hA)
  exact (existsUnique_maxPlusEigenvalue A hA).unique hmu hcanonical

end Matrix
