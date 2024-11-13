namespace GraphTheory


-- Node ---------------------------------

abbrev Node := Nat

@[simp]
def unique [BEq a] (as : List a) := (as ≠ []) → ∀ a ∈ as, (as.filter (. == a)).length = 1

-- Edge ---------------------------------

structure Edge where
  id: Nat
  i: Nat
  j: Nat
deriving DecidableEq, Inhabited

-- https://math.stackexchange.com/questions/3902966/notation-for-graph-adjacency
instance : Repr Edge where reprPrec e _ := f!"v{e.i}~v{e.j}"

def Edge.incident (e : Edge) (n : Node) := e.i = n ∨ e.j = n

-- Graph ---------------------------------

structure Graph where
  N : List Node
  E : List Edge
  ok : (∀ e, e ∈ E → (e.i ∈ N ∧ e.j ∈ N))
       ∧ unique N
       ∧ unique E

instance : Inhabited Graph where
  default := Graph.mk [] [] (by simp [unique])

instance : Repr Graph where
  reprPrec g _ :=
    let formatNode := fun n => (f!"v{n}")
    f!"(N={List.map formatNode g.N}, E={repr g.E})"

@[simp]
def Graph.isTrivial (g : Graph) := g.N.length = 1 ∧ g.E.isEmpty

instance : Decidable (g : Graph).isTrivial := instDecidableAnd

@[simp]
def Graph.isNull (g : Graph) := g.N.isEmpty

def Graph.parallel (g : Graph) (e f : Edge) := e ∈ g.E ∧ f ∈ g.E ∧ f.incident e.i ∧ f.incident e.j

instance : Decidable (Graph.parallel g e f) := by
  simp [Graph.parallel, Edge.incident]; apply instDecidableAnd

def Graph.adjacent (g : Graph) (n m : Node) := ∃ e, e ∈ g.E ∧ e.incident n ∧ e.incident m

instance : Decidable (Graph.adjacent g n m) := by
  simp [Graph.adjacent, Edge.incident]; exact List.decidableBEx _ g.E

----------------------------------------------

def na : Node := 3
def nb : Node := 2

def K1 := Graph.mk [1] [] (by simp)
def K2 := Graph.mk [1, 2] [Edge.mk 1 1 2] (by simp)
def K3 := Graph.mk [1, 2, 3] [Edge.mk 1 1 2, Edge.mk 2 2 3, Edge.mk 3 3 1] (by simp)

def K0 := instInhabitedGraph.default

#eval K0.isNull

#eval K1
#eval K2
#eval K3

#eval K1.isTrivial
#eval K2.isTrivial
#eval K3.isTrivial

#eval K1.adjacent ((K1.N.get? 0).get (by simp; decide)) ((K3.N.get? 2).get (by simp; decide))

def e1 := (K3.E.get? 1).get (by decide)
def e2 := (K3.E.get? 2).get (by decide)

#eval Graph.parallel K3 e1 e2


end GraphTheory
