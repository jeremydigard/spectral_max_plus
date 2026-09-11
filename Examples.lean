


module

public import Mathlib.Tropical.MaxPlus.Spectral
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum

/-!
# Examples for the max-plus spectral theorem

These examples validate the scalar conventions, the orientation of matrix edges, and the
three-by-three matrix from Example 2.2.3 of *Max Plus at Work*.
-/

@[expose] public section

namespace MaxPlusExamples

example : RMax.ofReal 2 + RMax.ofReal 5 = RMax.ofReal 5 := by
  apply RMax.toWithBot_injective
  simp only [RMax.toWithBot_add, RMax.toWithBot_ofReal]
  exact max_eq_right (by exact_mod_cast (show (2 : ℝ) ≤ 5 by norm_num))

example : RMax.ofReal 2 * RMax.ofReal 5 = RMax.ofReal 7 := by
  apply RMax.toWithBot_injective
  norm_num

example : (0 : RMax) + RMax.ofReal 3 = RMax.ofReal 3 := by simp

/-- The support convention is `j → i` exactly when the `(i,j)` coefficient is finite. -/
example {A : Matrix (Fin 2) (Fin 2) RMax} (i j : Fin 2) :
    A.HasEdge j i ↔ A i j ≠ 0 := Iff.rfl

def singletonMatrix (a : ℝ) : Matrix (Fin 1) (Fin 1) RMax := fun _ _ ↦ RMax.ofReal a

theorem singletonMatrix_irreducible (a : ℝ) : (singletonMatrix a).IsMaxPlusIrreducible := by
  refine ⟨?_, ?_⟩
  · intro i
    exact ⟨0, RMax.ofReal_ne_zero a⟩
  · intro i j hij
    exact (hij (Subsingleton.elim i j)).elim

theorem singletonMatrix_eigenvalue (a : ℝ) :
    (singletonMatrix a).IsMaxPlusEigenvalue (RMax.ofReal a) := by
  let v : Fin 1 → RMax := fun _ ↦ 1
  refine ⟨v, ?_, ?_⟩
  · intro hv
    have h := congrFun hv 0
    have h' : (0 : WithBot ℝ) = ⊥ := congrArg RMax.toWithBot h
    exact WithBot.coe_ne_bot h'
  · funext i
    fin_cases i
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, singletonMatrix, v]

example : ¬ (0 : Matrix (Fin 1) (Fin 1) RMax).IsMaxPlusIrreducible := by
  intro h
  obtain ⟨j, hj⟩ := h.hasNonzeroRows 0
  fin_cases j
  exact hj rfl

/-- The matrix from Example 2.1.1 / 2.2.3 of *Max Plus at Work*. -/
def bookMatrix : Matrix (Fin 3) (Fin 3) RMax :=
  ![![0, RMax.ofReal 15, 0],
    ![0, 0, RMax.ofReal 14],
    ![RMax.ofReal 10, 0, RMax.ofReal 12]]

def bookVector : Fin 3 → ℝ := ![3, 1, 0]

private theorem bookEdge02 : bookMatrix.HasEdge 0 2 := by
  change RMax.ofReal 10 ≠ 0
  exact RMax.ofReal_ne_zero 10

private theorem bookEdge21 : bookMatrix.HasEdge 2 1 := by
  change RMax.ofReal 14 ≠ 0
  exact RMax.ofReal_ne_zero 14

private theorem bookEdge10 : bookMatrix.HasEdge 1 0 := by
  change RMax.ofReal 15 ≠ 0
  exact RMax.ofReal_ne_zero 15

private theorem bookGraphEdge02 : bookMatrix.toWeightedDigraph.Edge 0 2 := bookEdge02
private theorem bookGraphEdge21 : bookMatrix.toWeightedDigraph.Edge 2 1 := bookEdge21
private theorem bookGraphEdge10 : bookMatrix.toWeightedDigraph.Edge 1 0 := bookEdge10

theorem bookMatrix_hasNonzeroRows : bookMatrix.HasNonzeroRows := by
  intro i
  fin_cases i
  · exact ⟨1, bookEdge10⟩
  · exact ⟨2, bookEdge21⟩
  · exact ⟨0, bookEdge02⟩

private def bookPath01 : bookMatrix.toWeightedDigraph.SimplePath 0 1 where
  vertices := [0, 2, 1]
  nonempty := by simp
  head_eq := rfl
  last_eq := rfl
  chain := List.isChain_cons_cons.mpr
    ⟨bookGraphEdge02, List.isChain_cons_cons.mpr
      ⟨bookGraphEdge21, List.isChain_singleton 1⟩⟩
  nodup := by decide

private def bookPath02 : bookMatrix.toWeightedDigraph.SimplePath 0 2 where
  vertices := [0, 2]
  nonempty := by simp
  head_eq := rfl
  last_eq := rfl
  chain := List.isChain_cons_cons.mpr ⟨bookGraphEdge02, List.isChain_singleton 2⟩
  nodup := by decide

private def bookPath10 : bookMatrix.toWeightedDigraph.SimplePath 1 0 where
  vertices := [1, 0]
  nonempty := by simp
  head_eq := rfl
  last_eq := rfl
  chain := List.isChain_cons_cons.mpr ⟨bookGraphEdge10, List.isChain_singleton 0⟩
  nodup := by decide

private def bookPath12 : bookMatrix.toWeightedDigraph.SimplePath 1 2 where
  vertices := [1, 0, 2]
  nonempty := by simp
  head_eq := rfl
  last_eq := rfl
  chain := List.isChain_cons_cons.mpr
    ⟨bookGraphEdge10, List.isChain_cons_cons.mpr
      ⟨bookGraphEdge02, List.isChain_singleton 2⟩⟩
  nodup := by decide

private def bookPath20 : bookMatrix.toWeightedDigraph.SimplePath 2 0 where
  vertices := [2, 1, 0]
  nonempty := by simp
  head_eq := rfl
  last_eq := rfl
  chain := List.isChain_cons_cons.mpr
    ⟨bookGraphEdge21, List.isChain_cons_cons.mpr
      ⟨bookGraphEdge10, List.isChain_singleton 0⟩⟩
  nodup := by decide

private def bookPath21 : bookMatrix.toWeightedDigraph.SimplePath 2 1 where
  vertices := [2, 1]
  nonempty := by simp
  head_eq := rfl
  last_eq := rfl
  chain := List.isChain_cons_cons.mpr ⟨bookGraphEdge21, List.isChain_singleton 1⟩
  nodup := by decide

theorem bookMatrix_irreducible : bookMatrix.IsMaxPlusIrreducible := by
  refine ⟨bookMatrix_hasNonzeroRows, ?_⟩
  intro a b hab
  fin_cases a <;> fin_cases b
  · exact (hab rfl).elim
  · exact ⟨bookPath01⟩
  · exact ⟨bookPath02⟩
  · exact ⟨bookPath10⟩
  · exact (hab rfl).elim
  · exact ⟨bookPath12⟩
  · exact ⟨bookPath20⟩
  · exact ⟨bookPath21⟩
  · exact (hab rfl).elim

theorem bookMatrix_tropicalEigenpair :
    Matrix.mulVec bookMatrix (fun i ↦ RMax.ofReal (bookVector i)) =
      fun i ↦ RMax.ofReal 13 * RMax.ofReal (bookVector i) := by
  have h12 : (12 : WithBot ℝ) < 13 := by
    exact_mod_cast (show (12 : ℝ) < 13 by norm_num)
  funext i
  fin_cases i <;>
    apply RMax.toWithBot_injective <;>
    norm_num [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, bookMatrix, bookVector,
      max_def, h12]

theorem bookMatrix_realEigenpair :
    bookMatrix.IsMaxPlusRealEigenpair bookMatrix_hasNonzeroRows 13 bookVector := by
  have h := bookMatrix_tropicalEigenpair
  rw [bookMatrix.mulVec_ofReal bookMatrix_hasNonzeroRows bookVector] at h
  funext i
  apply RMax.ofReal_injective
  have hi := congrFun h i
  simpa only [RMax.ofReal_add] using hi

/-- The two simple-cycle means are `13` and `12`, so the spectral value is `13`. -/
theorem bookMatrix_maxCycleMean :
    Matrix.maxCycleMean bookMatrix bookMatrix_irreducible = 13 := by
  exact bookMatrix.realEigenvalue_unique bookMatrix_hasNonzeroRows
    (Matrix.eigenPotential_isMaxPlusRealEigenpair bookMatrix bookMatrix_irreducible)
    bookMatrix_realEigenpair

/-- Translating a real eigenvector does not change its eigenvalue. -/
example {n : Type*} [Fintype n] (A : Matrix n n RMax) (hrow : A.HasNonzeroRows)
    {mu : ℝ} {v : n → ℝ} (h : A.IsMaxPlusRealEigenpair hrow mu v) (c : ℝ) :
    A.IsMaxPlusRealEigenpair hrow mu (fun i ↦ v i + c) := by
  rw [Matrix.IsMaxPlusRealEigenpair, A.maxPlusMulVecReal_add_const, h]
  funext i
  ring

end MaxPlusExamples
