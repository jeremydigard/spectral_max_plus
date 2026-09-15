
module
public import Mathlib.Tropical.MaxPlus.Basic
public import Mathlib.Data.Fintype.List
public import Mathlib.Data.List.Chain
public import Mathlib.Tactic.Ring
public meta import Lean.Elab.Tactic.Omega -- c quoi meta

/-!
# Weighted directed paths for max-plus algebra

The support of a max-plus matrix is a thin weighted directed graph.  Paths and cycles are stored
as nonempty, duplicate-free lists of vertices.  A one-vertex cycle is therefore a loop.
-/

@[expose] public section

/-- A directed graph with real edge weights.  Values of `weight` off the edge relation are ignored. -/
structure WeightedDigraph (ι : Type*) where
  Edge : ι → ι → Prop
  weight : ι → ι → ℝ
-- c quoi une structure ? c quoi la diff avec un type ?

namespace WeightedDigraph -- ca veut dire quoi ca ?

variable {ι : Type*} (G : WeightedDigraph ι)

def HasIncomingEdges : Prop := ∀ i, ∃ j, G.Edge j i -- pq on a pas besoin de préciser sur quoi on itere 'i'

/-- Sum the weights of consecutive pairs in a list. -/
def chainWeight (G : WeightedDigraph ι) : List ι → ℝ
  | [] | [_] => 0
  | j :: i :: l => G.weight j i + chainWeight G (i :: l)

@[simp] theorem chainWeight_nil : G.chainWeight [] = 0 := rfl
@[simp] theorem chainWeight_singleton (i : ι) : G.chainWeight [i] = 0 := rfl
@[simp] theorem chainWeight_cons_cons (j i : ι) (l : List ι) :
    G.chainWeight (j :: i :: l) = G.weight j i + G.chainWeight (i :: l) := rfl

theorem chainWeight_overlap (l₁ l₂ : List ι) (i : ι) :
    G.chainWeight (l₁ ++ i :: l₂) =
      G.chainWeight (l₁ ++ [i]) + G.chainWeight (i :: l₂) := by
  induction l₁ with
  | nil => simp
  | cons j l₁ ih =>
      cases l₁ with
      | nil => simp [chainWeight]
      | cons k l₁ =>
          simp only [List.cons_append, chainWeight_cons_cons]
          have ih' : G.chainWeight (k :: (l₁ ++ i :: l₂)) =
              G.chainWeight (k :: (l₁ ++ [i])) + G.chainWeight (i :: l₂) := by
            simpa only [List.cons_append] using ih
          rw [ih', add_assoc]

/-- Weight of an edge after subtracting a proposed eigenvalue. -/
def normalizedEdgeWeight (lam : ℝ) (j i : ι) : ℝ := G.weight j i - lam

/-- A simple directed path, including the length-zero path `[a]`. -/
structure SimplePath (a b : ι) where
  vertices : List ι
  nonempty : vertices ≠ []
  head_eq : vertices.head nonempty = a
  last_eq : vertices.getLast nonempty = b
  chain : vertices.IsChain G.Edge
  nodup : vertices.Nodup

/-- A simple directed cycle.  Its closing edge is stored separately. -/
structure SimpleCycle where
  vertices : List ι
  nonempty : vertices ≠ []
  nodup : vertices.Nodup
  chain : vertices.IsChain G.Edge
  closing : G.Edge (vertices.getLast nonempty) (vertices.head nonempty)

/-- A nonempty closed walk.  Unlike a `SimpleCycle`, vertices may be repeated. -/
structure ClosedWalk where
  vertices : List ι
  nonempty : vertices ≠ []
  chain : vertices.IsChain G.Edge
  closing : G.Edge (vertices.getLast nonempty) (vertices.head nonempty)

namespace SimplePath

variable {G} {a b c : ι}

@[ext] theorem ext {p q : G.SimplePath a b} (h : p.vertices = q.vertices) : p = q := by
  cases p
  cases q
  simp_all

/-- The trivial simple path. -/
def refl (a : ι) : G.SimplePath a a where
  vertices := [a]
  nonempty := by simp
  head_eq := rfl
  last_eq := rfl
  chain := List.isChain_singleton a
  nodup := by simp

@[simp] theorem vertices_refl (a : ι) : (refl (G := G) a).vertices = [a] := rfl

/-- Number of edges in a simple path. -/
def length (p : G.SimplePath a b) : ℕ := p.vertices.length - 1

/-- Weight of a simple path. -/
def weight (p : G.SimplePath a b) : ℝ := G.chainWeight p.vertices

/-- Weight after subtracting `lam` from every edge. -/
def normalizedWeight (p : G.SimplePath a b) (lam : ℝ) : ℝ :=
  p.weight - (p.length : ℝ) * lam

@[simp] theorem length_refl (a : ι) : (refl (G := G) a).length = 0 := by simp [length]

@[simp] theorem weight_refl (a : ι) : (refl (G := G) a).weight = 0 := rfl

@[simp] theorem normalizedWeight_refl (a : ι) (lam : ℝ) :
    (refl (G := G) a).normalizedWeight lam = 0 := by simp [normalizedWeight]

theorem eq_refl (p : G.SimplePath a a) : p = refl a := by
  apply ext
  obtain ⟨x, l, hl⟩ := List.exists_cons_of_ne_nil p.nonempty
  rw [hl]
  have hx : x = a := by simpa [hl] using p.head_eq
  subst x
  cases l with
  | nil => rfl
  | cons y l =>
      exfalso
      have hmem : (a :: y :: l).getLast (by simp) ∈ y :: l := by
        simpa using List.getLast_mem (y :: l) (by simp)
      have hlast : (a :: y :: l).getLast (by simp) = a := by simpa [hl] using p.last_eq
      rw [hlast] at hmem
      have hn : a ∉ y :: l ∧ (y :: l).Nodup := by simpa [hl] using p.nodup
      exact hn.1 hmem

/-- Extend a simple path by an edge to a vertex not already visited. -/
def appendEdge (p : G.SimplePath a b) (hbc : G.Edge b c) (hc : c ∉ p.vertices) :
    G.SimplePath a c where
  vertices := p.vertices ++ [c]
  nonempty := List.append_ne_nil_of_left_ne_nil p.nonempty [c]
  head_eq := by
    rw [List.head_append_of_ne_nil p.nonempty]
    exact p.head_eq
  last_eq := by simp only [List.getLast_append_singleton]
  chain := by
    rw [List.isChain_append]
    refine ⟨p.chain, List.isChain_singleton c, ?_⟩
    intro x hx y hy
    simp only [List.head?_singleton, Option.mem_def, Option.some.injEq] at hy
    subst y
    obtain ⟨hne, rfl⟩ := List.mem_getLast?_eq_getLast hx
    simpa only [p.last_eq] using hbc
  nodup := p.nodup.append (by simp) (by simpa using hc)

@[simp] theorem vertices_appendEdge (p : G.SimplePath a b) (hbc : G.Edge b c)
    (hc : c ∉ p.vertices) : (p.appendEdge hbc hc).vertices = p.vertices ++ [c] := rfl

theorem chainWeight_append_singleton (p : G.SimplePath a b) (c : ι) :
    G.chainWeight (p.vertices ++ [c]) = p.weight + G.weight b c := by
  have hw := G.chainWeight_overlap p.vertices.dropLast [c]
    (p.vertices.getLast p.nonempty)
  unfold weight
  rw [← List.dropLast_append_getLast p.nonempty]
  simpa only [List.append_assoc, List.singleton_append, chainWeight_cons_cons,
    chainWeight_singleton, add_zero, p.last_eq] using hw

theorem length_appendEdge (p : G.SimplePath a b) (hbc : G.Edge b c)
    (hc : c ∉ p.vertices) : (p.appendEdge hbc hc).length = p.length + 1 := by
  simp only [length, vertices_appendEdge, List.length_append, List.length_singleton]
  have := List.length_pos_of_ne_nil p.nonempty
  omega

theorem normalizedWeight_appendEdge (p : G.SimplePath a b) (hbc : G.Edge b c)
    (hc : c ∉ p.vertices) (lam : ℝ) :
    (p.appendEdge hbc hc).normalizedWeight lam =
      p.normalizedWeight lam + G.normalizedEdgeWeight lam b c := by
  rw [normalizedWeight, normalizedWeight, normalizedEdgeWeight, length_appendEdge]
  change G.chainWeight (p.vertices ++ [c]) - ↑(p.length + 1) * lam =
    p.weight - ↑p.length * lam + (G.weight b c - lam)
  rw [chainWeight_append_singleton]
  push_cast
  ring

end SimplePath

namespace ClosedWalk

variable {G}

/-- The distinguished first vertex of a closed walk. -/
def root (c : G.ClosedWalk) : ι := c.vertices.head c.nonempty

/-- Number of edges in a closed walk, including the closing edge. -/
def length (c : G.ClosedWalk) : ℕ := c.vertices.length

/-- Total weight of a closed walk, including the closing edge. -/
def weight (c : G.ClosedWalk) : ℝ := G.chainWeight (c.vertices ++ [c.root])

/-- Mean edge weight of a closed walk. -/
noncomputable def meanWeight (c : G.ClosedWalk) : ℝ := c.weight / c.length

theorem length_pos (c : G.ClosedWalk) : 0 < c.length :=
  List.length_pos_of_ne_nil c.nonempty

/-- The vertex list with its root appended contains every edge of the closed walk. -/
theorem isChain_append_root (c : G.ClosedWalk) :
    (c.vertices ++ [c.root]).IsChain G.Edge := by
  rw [List.isChain_append]
  refine ⟨c.chain, List.isChain_singleton c.root, ?_⟩
  intro x hx y hy
  simp only [List.head?_singleton, Option.mem_def, Option.some.injEq] at hy
  subst y
  obtain ⟨hne, rfl⟩ := List.mem_getLast?_eq_getLast hx
  exact c.closing

end ClosedWalk

namespace SimpleCycle

variable {G}

@[ext] theorem ext {c d : G.SimpleCycle} (h : c.vertices = d.vertices) : c = d := by
  cases c
  cases d
  simp_all

/-- The first vertex of a simple cycle. -/
def root (c : G.SimpleCycle) : ι := c.vertices.head c.nonempty

/-- Number of edges in a simple cycle. -/
def length (c : G.SimpleCycle) : ℕ := c.vertices.length

/-- Total cycle weight, including its closing edge. -/
def weight (c : G.SimpleCycle) : ℝ :=
  G.chainWeight (c.vertices ++ [c.root])

noncomputable def meanWeight (c : G.SimpleCycle) : ℝ := c.weight / c.length

def normalizedWeight (c : G.SimpleCycle) (lam : ℝ) : ℝ :=
  c.weight - (c.length : ℝ) * lam

/-- Forget that a simple cycle has no repeated vertices. -/
def toClosedWalk (c : G.SimpleCycle) : G.ClosedWalk where
  vertices := c.vertices
  nonempty := c.nonempty
  chain := c.chain
  closing := c.closing

@[simp] theorem toClosedWalk_weight (c : G.SimpleCycle) : c.toClosedWalk.weight = c.weight := rfl

@[simp] theorem toClosedWalk_length (c : G.SimpleCycle) : c.toClosedWalk.length = c.length := rfl

@[simp] theorem toClosedWalk_meanWeight (c : G.SimpleCycle) :
    c.toClosedWalk.meanWeight = c.meanWeight := rfl

/-- Delete the closing edge of a cycle. -/
def asPathToLast (c : G.SimpleCycle) : G.SimplePath c.root (c.vertices.getLast c.nonempty) where
  vertices := c.vertices
  nonempty := c.nonempty
  head_eq := rfl
  last_eq := rfl
  chain := c.chain
  nodup := c.nodup

@[simp] theorem asPathToLast_vertices (c : G.SimpleCycle) : c.asPathToLast.vertices = c.vertices :=
  rfl

theorem normalizedWeight_eq_path_add_closing (c : G.SimpleCycle) (lam : ℝ) :
    c.normalizedWeight lam = c.asPathToLast.normalizedWeight lam +
      G.normalizedEdgeWeight lam (c.vertices.getLast c.nonempty) c.root := by
  rw [normalizedWeight, SimplePath.normalizedWeight, normalizedEdgeWeight, weight,
    SimplePath.weight, SimplePath.length, length]
  have hlen := List.length_pos_of_ne_nil c.nonempty
  have hw := c.asPathToLast.chainWeight_append_singleton c.root
  simp only [asPathToLast_vertices] at hw
  rw [hw]
  change c.asPathToLast.weight + G.weight (c.vertices.getLast c.nonempty) c.root -
      (c.vertices.length : ℝ) * lam =
    c.asPathToLast.weight - ((c.vertices.length - 1 : ℕ) : ℝ) * lam +
      (G.weight (c.vertices.getLast c.nonempty) c.root - lam)
  rw [Nat.cast_sub (by omega : 1 ≤ c.vertices.length)]
  push_cast
  ring

theorem length_pos (c : G.SimpleCycle) : 0 < c.length := by
  exact List.length_pos_of_ne_nil c.nonempty

theorem normalizedWeight_eq_length_mul (c : G.SimpleCycle) (lam : ℝ) :
    c.normalizedWeight lam = (c.length : ℝ) * (c.meanWeight - lam) := by
  have hn : (c.length : ℝ) ≠ 0 := by exact_mod_cast c.length_pos.ne'
  have hw : (c.length : ℝ) * (c.weight / (c.length : ℝ)) = c.weight := by
    rw [mul_comm, div_mul_cancel₀ _ hn]
  rw [normalizedWeight, meanWeight, mul_sub, hw]

end SimpleCycle

section Finite

variable [Fintype ι]

noncomputable instance finiteSimplePath (a b : ι) : Finite (G.SimplePath a b) :=
  Finite.of_injective (fun p ↦ (⟨p.vertices, p.nodup⟩ : {l : List ι // l.Nodup}))
    fun _ _ h ↦ SimplePath.ext (Subtype.ext_iff.mp h)

noncomputable instance fintypeSimplePath (a b : ι) : Fintype (G.SimplePath a b) :=
  Fintype.ofFinite _

noncomputable instance finiteSimpleCycle : Finite G.SimpleCycle :=
  Finite.of_injective (fun c ↦ (⟨c.vertices, c.nodup⟩ : {l : List ι // l.Nodup}))
    fun _ _ h ↦ SimpleCycle.ext (Subtype.ext_iff.mp h)

noncomputable instance fintypeSimpleCycle : Fintype G.SimpleCycle :=
  Fintype.ofFinite _

end Finite

end WeightedDigraph

namespace Matrix

variable {ι : Type*} [Fintype ι]

/-- The real weighted support graph of a max-plus matrix. -/
noncomputable def toWeightedDigraph (A : Matrix ι ι RMax) : WeightedDigraph ι where
  Edge := A.HasEdge
  weight := A.edgeWeight

@[simp] theorem toWeightedDigraph_edge (A : Matrix ι ι RMax) (j i : ι) :
    A.toWeightedDigraph.Edge j i ↔ A.HasEdge j i := Iff.rfl

theorem toWeightedDigraph_weight_of_edge (A : Matrix ι ι RMax) {j i : ι}
    (hji : A.HasEdge j i) :
    A.toWeightedDigraph.weight j i = (A i j).toReal hji := by
  exact A.edgeWeight_of_edge hji

/-- Positive strong connectivity, in a simple-path form convenient for the spectral proof.

For distinct vertices this asks for a simple path; incoming edges provide a positive closed walk
at every vertex, including on singleton index types.
-/
def IsMaxPlusIrreducible (A : Matrix ι ι RMax) : Prop :=
  A.HasNonzeroRows ∧ ∀ a b, a ≠ b → Nonempty (A.toWeightedDigraph.SimplePath a b)

namespace IsMaxPlusIrreducible

variable {A : Matrix ι ι RMax}

theorem hasNonzeroRows (hA : A.IsMaxPlusIrreducible) : A.HasNonzeroRows := hA.1

theorem hasNonzeroColumns (hA : A.IsMaxPlusIrreducible) :
    ∀ j, ∃ i, A.HasEdge j i := by
  intro j
  by_cases hsingle : ∀ i : ι, i = j
  · obtain ⟨i, hi⟩ := hA.hasNonzeroRows j
    exact ⟨j, by simpa [hsingle i] using hi⟩
  · push_neg at hsingle
    obtain ⟨i, hij⟩ := hsingle
    let p := Classical.choice (hA.2 j i (Ne.symm hij))
    obtain ⟨x, l, hl⟩ := List.exists_cons_of_ne_nil p.nonempty
    have hx : x = j := by simpa [hl] using p.head_eq
    subst x
    cases l with
    | nil =>
        exfalso
        exact hij (by simpa [hl] using p.last_eq.symm)
    | cons y l =>
        have hchain : List.IsChain A.toWeightedDigraph.Edge (j :: y :: l) := by
          rw [← hl]
          exact p.chain
        have hedge : A.toWeightedDigraph.Edge j y := hchain.rel
        exact ⟨y, hedge⟩

theorem simplePath_of_ne (hA : A.IsMaxPlusIrreducible) {a b : ι} (hab : a ≠ b) :
    Nonempty (A.toWeightedDigraph.SimplePath a b) := hA.2 a b hab

theorem simplePath (hA : A.IsMaxPlusIrreducible) (a b : ι) :
    Nonempty (A.toWeightedDigraph.SimplePath a b) := by
  by_cases hab : a = b
  · subst b
    exact ⟨WeightedDigraph.SimplePath.refl a⟩
  · exact hA.simplePath_of_ne hab

theorem exists_simpleCycle (hA : A.IsMaxPlusIrreducible) [Nonempty ι] :
    Nonempty A.toWeightedDigraph.SimpleCycle := by
  let i : ι := Classical.choice ‹Nonempty ι›
  obtain ⟨j, hji⟩ := hA.hasNonzeroRows i
  by_cases h : j = i
  · subst j
    exact ⟨{
      vertices := [i]
      nonempty := by simp
      nodup := by simp
      chain := List.isChain_singleton i
      closing := hji }⟩
  · let p := Classical.choice (hA.simplePath_of_ne (Ne.symm h))
    exact ⟨{
      vertices := p.vertices
      nonempty := p.nonempty
      nodup := p.nodup
      chain := p.chain
      closing := by simpa [p.last_eq, p.head_eq] using hji }⟩

end IsMaxPlusIrreducible

end Matrix
