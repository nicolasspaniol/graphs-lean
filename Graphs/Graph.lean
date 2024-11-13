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

-- https://math.stackexchange.com/questions/3902966/notation-for-graph-adjacency
instance : Repr Edge where reprPrec e _ := f!"v{e.i}~v{e.j}"

instance : BEq Edge where beq a b := a.id == b.id

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
abbrev Graph.isTrivial (g : Graph) := g.N.length = 1 ∧ g.E.isEmpty

----------------------------------------------

def na : Node := 3
def nb : Node := 2

def K1 := Graph.mk [1] [] (by simp)
def K2 := Graph.mk [1, 2] [Edge.mk 1 1 2] (by simp; decide)
def K3 := Graph.mk [1, 2, 3] [Edge.mk 1 1 2, Edge.mk 2 2 3, Edge.mk 3 3 1] (by simp; decide)

#eval K1
#eval K2
#eval K3

#eval K1.isTrivial
#eval K2.isTrivial
#eval K3.isTrivial


end GraphTheory
