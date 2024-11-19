namespace GraphTheory


-- Node ---------------------------------

abbrev Node := Nat

@[simp]
def unique [BEq a] (as : List a) : Prop :=
match as with
| [] => true
| a::as => if List.filter (fun x => x == a) as == [] then unique as else false

def uniqueB [BEq a] (as : List a) : Bool :=
match as with
| [] => true
| a::as => if List.filter (fun x => x == a) as == [] then uniqueB as else false

theorem unique_uniqueB_iff [BEq a] {as : List a}: uniqueB as ↔ unique as := by
  induction as with
  | nil => rfl
  | cons a as ih =>
    rw [unique, uniqueB]
    simp
    exact fun _ => ih

instance  [BEq a] {as : List a} : Decidable  (unique as) :=
  decidable_of_bool _ unique_uniqueB_iff

-- Edge ---------------------------------

structure Edge where
  id: Nat
  i: Nat
  j: Nat
deriving DecidableEq, Inhabited

-- https://math.stackexchange.com/questions/3902966/notation-for-graph-adjacency
instance : Repr Edge where reprPrec e _ := f!"v{e.i}~v{e.j}"

def Edge.incident (e : Edge) (n : Node) := e.i = n ∨ e.j = n

instance : Decidable (Edge.incident e n) := by
  apply instDecidableOr

-- Graph ---------------------------------

structure Graph where
  N : List Node
  E : List Edge
  ok : (∀ e, e ∈ E → (e.i ∈ N ∧ e.j ∈ N ∧ ¬∃ d ∈ E, d ≠ e ∧ e.id = d.id))
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

def Graph.adjacent (g : Graph) (n m : Node) := ∃ e, e ∈ g.E ∧ ((e.i = n ∧ e.j = m) ∨ (e.j = n ∧ e.i = m))

instance : Decidable (Graph.adjacent g n m) := by
  simp [Graph.adjacent, Edge.incident]; exact List.decidableBEx _ g.E

----------------------------------------------

def na : Node := 3
def nb : Node := 2

def K1 := Graph.mk [1] [] (by simp)
def K2 := Graph.mk [1, 2] [Edge.mk 1 1 2] (by simp)
def K3 := Graph.mk [1, 2, 3] [Edge.mk 1 1 2, Edge.mk 2 2 3, Edge.mk 3 3 1] (by simp)

def KEdges (n : Nat) (xs : List Nat) : List Edge :=
    match xs with
    | [] => []
    | y::ys => List.map (λ x => Edge.mk (x - y + n) y x) ys ++ KEdges (n + ys.length) ys

def K (n : Nat) := Graph.mk ((List.iota n).reverse) (KEdges 0 (List.iota n).reverse)

def K0 := instInhabitedGraph.default

#eval K0.isNull

#eval K1
#eval K2
#eval K3



#eval K1.isTrivial
#eval K2.isTrivial
#eval K3.isTrivial

#eval K1.adjacent ((K1.N.get? 0).get (by simp; decide)) ((K3.N.get? 2).get (by simp; decide))

#eval K 7 (by simp; decide)

#eval (K 4 (by simp; decide)).adjacent 1 1

def e1 := (K3.E.get? 1).get (by decide)
def e2 := (K3.E.get? 2).get (by decide)

#eval Graph.parallel K3 e1 e2

-- Weighted graphs --------------------------------
structure WGraph where
  N : List Node
  E : List Edge
  W : List (Edge × Nat)
  ok : (∀ e, e ∈ E → (e.i ∈ N ∧ e.j ∈ N))
       ∧ (∀ e, e ∈ E → (∃ w, w ∈ W ∧ e = w.1))
       ∧ unique N
       ∧ unique E
       ∧ unique W

instance : Inhabited WGraph where
  default := WGraph.mk [] [] [] (by simp [unique])

instance : Repr WGraph where
  reprPrec g _ :=
    let formatNode := fun n => (f!"v{n}")
    let formatWeights := fun w => (f!"({repr w.1}, w:{w.2})")
    f!"(N={List.map formatNode g.N}, E={repr g.E} W={List.map formatWeights g.W})"

#eval WGraph.mk [1,2,3] [Edge.mk 1 1 2, Edge.mk 2 2 3] [((Edge.mk 1 1 2), 3), ((Edge.mk 2 2 3), 1)] (by simp)

-- Dijkstra ----------------------------

def L (n : Node) (l : List (Node × (Node × Int))) : Int :=
match l.filter (λ (x,_) => x == n) with
| [] => 0
| x::_ => x.2.2

def LPair (n : Node) (l : List (Node × (Node × Int))) : (Node × Node × Int) :=
match l.filter (λ (x,_) => x == n) with
| [] => (0,0,0)
| x::_ => (n, x.2.1, x.2.2)

def newL (n : Node) (v : Nat) (l : List (Node × (Node × Int))) : List (Node × (Node × Int)) :=
match l with
| [] => l
| x::xs => if n == x.1 then (n,(x.2.1, v))::xs else x::(newL n v xs)

#eval newL 2 4 [(2,(0,1)), (3,(0,1))]
#eval L 2  [(2,(0,4)), (3,(0,1))]
#eval LPair 2 [(2, (0, 4)), (3, (0, 1))]

def findMinL  (v : (Node × Int)) (l : List (Node × (Node × Int))) : (Node × Int) :=
match l with
| [] => v
| x::xs => if (x.2.2 < v.2 ∧ x.2.2 != -1) ∨ v.2 == -1 then findMinL x.2 xs else findMinL v xs

def MinLNode (p : Node × (Node × Int)) (l : List (Node × (Node × Int))) : Node :=
  match l with
  | [] => p.1
  | x::xs => if p.2.2 == x.2.2 then MinLNode (x.1, p.2) [] else MinLNode p xs
  termination_by l.length

#eval (fun x => MinLNode (0,x) [(1,0,3), (2,0,2), (3,0,1), (4,0,3)]) <| findMinL (0,-1) [(1,0,2), (2,0,2), (3,0,1), (4,0,3)]

def newLs (ns : List Node) (v : Int) : List (Node × (Node × Int)) :=
ns.map (fun x => (x,(0, v)))

#eval newLs (K 3 (by simp; decide)).N (-1)

def Node.adjacent (es : List Edge) (n m : Node) := ∃ e, e ∈ es ∧ e.incident n ∧ e.incident m ∧ n ≠ m

instance : Decidable (Node.adjacent es n m) := by
  simp [Node.adjacent, Edge.incident]; exact List.decidableBEx _ es


def filterAdj (n : Node) (g : List Node) (es : List Edge) : List Node :=
  g.filter (Node.adjacent es n)

#eval filterAdj 1 (K 4 (by simp; decide)).N (K 4 (by simp; decide)).E

def findWeight (v n : Node) (ws : List (Edge × Int)) : Int :=
  match ws with
  | [] => 0
  | x::xs =>
    if (Edge.incident x.1 v) ∧ (Edge.incident x.1 n) then x.2
    else findWeight v n xs

#eval findWeight 1 2 [(Edge.mk 1 2 3, 3), (Edge.mk 1 1 2, 4)]

def updateLs (v n : Node) (l : List (Node × (Node × Int))) (ws : List (Edge × Int))
    : List (Node × (Node × Int)) :=
    let n_l := L n l
    let vn_w := findWeight v n ws
    let minimum := if n_l == -1 then (L v l) + vn_w else min n_l ((L v l) + vn_w)
    if minimum == n_l then l else help n l minimum where
    help (n : Node) (l : List (Node × (Node × Int))) (label : Int) : List (Node × (Node × Int)) :=
    match l with
    | [] => []
    | x::xs => if x.1 == n then (n,(v,label))::xs else x::(help n xs label)

def updateLsMap (v : Node) (ns : List Node) (l : List (Node × (Node × Int)))  (ws : List (Edge × Int))
  : List (Node × (Node × Int)) :=
  List.foldr (fun x y => updateLs v x y ws) l ns

#eval updateLsMap 1 [2, 3] [(1, 0, 2), (2, 0, 4), (3, 0, 4)] [(Edge.mk 1 1 3, 1), (Edge.mk 1 1 2, 1)]
#eval updateLsMap 1 [2, 3] [(1, 0, 2), (2, 0, 4), (3, 0, 4)] [(Edge.mk 1 1 3, 3), (Edge.mk 1 1 2, 4)]

def isinGraph (n : Node) (ns : List Node) : Bool :=
  if (ns.filter (· == n)).length >= 1 then true else false

#eval isinGraph 1 [2,3]

def t1 : (newLs [a] (-1))++(newLs as (-1)) = newLs (a::as) (-1) := by
      induction as with
      | nil => rfl
      | cons b bs _ =>
        rfl

example : ∀ v, v ∈ T → (fun x => MinLNode (0,x) (updateLsMap v (filterAdj v T es) (newLs T (-1)) ws)) (findMinL (0,-1)  (updateLsMap v (filterAdj v T es) (newLs T (-1)) ws)) ∈ T := by
  simp
  induction T with
  | nil => simp
  | cons a as ih =>
    intro v
    intro h
    rw [←t1]
    simp
    sorry

-- partial definition
partial def Dijkstra (a z : Node) (G : Graph) (W : List (Edge × Int)) : List (Node × (Node × Int)) :=
  let labels := newL a 0 <|newLs G.N (-1)
  let T := G.N
  if T.length = 0 then [(0,(0,0))] else
    help  z T labels T G.E W [] where
     help (z : Node) (t : List Node) (ls : List (Node × (Node × Int)))
      (N : List Node) (es : List Edge) (ws : List (Edge × Int)) (f : List (Node × (Node × Int)))
      : List (Node × Node × Int) :=
      if (isinGraph z t) then
        let v := (fun x => MinLNode (0,x) ls) <| findMinL (0,-1) ls
        let v_l := (LPair v ls)
        let ads := filterAdj v N es
        let new_lbs := List.filter (fun x => x.1 != v) (updateLsMap v ads ls ws)
        let T := t.filter (fun x => x != v)
        help z T new_lbs N es ws (f++[v_l])
      else f

def SimpleW (E : List Edge) : List (Edge × Int) :=
 match E with
 | [] => []
 | x::xs => (x,1)::(SimpleW xs)

def ChangeW (v : Int) (e : Edge) (W : List (Edge × Int)) : List (Edge × Int) :=
match W with
| [] => []
| x::xs => if x.1 == e then (x.1,v)::xs else x::(ChangeW v e xs)

#eval ChangeW 3 (Edge.mk 1 1 2) <| SimpleW (K 4 (by simp; decide)).E
#eval Dijkstra 1 3 (K 3 (by simp; decide)) [(Edge.mk 1 1 3, 5), (Edge.mk 2 1 2, 1), (Edge.mk 3 3 2, 1)]

-- Walks, paths and cycles --------------------------------
def casB (m n : Node) (E : List Edge) : Bool :=
match E with
| [] => if m == n then true else false
| a::as => if m == a.i then casB a.j n as else false

-- the cas function is inspired in the Isabelle's definition of walk, path and cycle
def cas (m n : Node) (E : List Edge) : Prop :=
match E with
| [] => if m == n then true else false
| a::as => if m == a.i then casB a.j n as else false

theorem cas_casB_iff : casB m n E ↔ cas m n E := by
  induction E with
  | nil => rfl
  | cons a as _ =>
    exact Eq.to_iff rfl

instance : Decidable (cas m n E) := decidable_of_bool _ cas_casB_iff

#eval cas 1 3 [Edge.mk 1 1 2, Edge.mk 2 2 3]
#eval cas 1 2 [Edge.mk 1 1 2, Edge.mk 2 2 3]

def firstNode (E : List Edge) : Node :=
  match E with
  | [] => 0
  | a::_ => a.i

def lastNode (n : Node) (E : List Edge) : Node :=
  match E with
  | [] => n
  | a::as => lastNode a.j as

structure Walk where
  start : Node
  aWalk : List Edge
  ok : cas start (lastNode start aWalk) aWalk
       ∧ ((aWalk = []) ∨ start = (firstNode aWalk))

instance : Repr Walk where
  reprPrec w _ :=
    let formatEdge := fun n => (f!"v{n.i}~v{n.j}")
    let formatNode := fun n => (f!"v{n}")
    f!"{[formatNode w.start]++(List.map formatEdge w.aWalk)++[formatNode (lastNode w.start w.aWalk)]}"

#eval Walk.mk 1 [Edge.mk 1 1 2, Edge.mk 2 2 1] (by simp; exact ite_some_none_eq_some.mp rfl)
#eval cas 1 0 [Edge.mk 1 1 2, Edge.mk 2 6 0]

#eval (K 2 (by simp;decide)).N ++ (K 3 (by simp; decide)).N

def Walk.nodes (w : Walk) : List Node :=
  [w.start] ++ help w.aWalk where
  help (walk : List Edge) : List Node :=
    match walk with
    | [] => []
    | a::as => [a.j]++(help as)

#eval (Walk.mk 1 [Edge.mk 1 1 2, Edge.mk 2 2 3] (by simp; exact ite_some_none_eq_some.mp rfl)).nodes

def isSimple (w : Walk) : Prop :=
  if unique (w.nodes) then true else false

instance : Decidable (isSimple w) := by
  rw [isSimple]
  exact (if unique w.nodes then true else false).decEq true

structure Path where
  aWalk : Walk
  isSimple := isSimple aWalk
  ok : unique aWalk.aWalk

instance : Repr Path where
  reprPrec w _ :=
    let formatEdge := fun n => (f!"v{n.i}~v{n.j}")
    let formatNode := fun n => (f!"v{n}")
    f!"{[formatNode w.aWalk.start]++(List.map formatEdge w.aWalk.aWalk)++[formatNode (lastNode w.aWalk.start w.aWalk.aWalk)]}"

def wlk := (Walk.mk 1 [Edge.mk 1 1 2, Edge.mk 2 2 3] (by simp; exact ite_some_none_eq_some.mp rfl))
#eval (Path.mk wlk (isSimple wlk) (by simp)).isSimple
#eval (Path.mk wlk (isSimple wlk) (by simp))
def owlk := (Walk.mk 1 [Edge.mk 1 1 2, Edge.mk 1 2 1] (by simp; exact ite_some_none_eq_some.mp rfl))
#eval (Path.mk owlk (isSimple owlk) (by simp))

structure Cycle where
  aWalk : Walk
  ok : aWalk.start = (lastNode aWalk.start aWalk.aWalk)
     ∧ unique aWalk.aWalk

instance : Repr Cycle where
  reprPrec w _ :=
    let formatEdge := fun n => (f!"v{n.i}~v{n.j}")
    let formatNode := fun n => (f!"v{n}")
    f!"{[formatNode w.aWalk.start]++(List.map formatEdge w.aWalk.aWalk)++[formatNode (lastNode w.aWalk.start w.aWalk.aWalk)]}"

#eval Cycle.mk (Walk.mk 1 [Edge.mk 1 1 2, Edge.mk 2 2 1] (by simp; exact ite_some_none_eq_some.mp rfl)) (by simp; rw [lastNode, lastNode, lastNode])
#eval (Cycle.mk (Walk.mk 1 [Edge.mk 1 1 2, Edge.mk 2 2 1] (by simp; exact ite_some_none_eq_some.mp rfl)) (by simp; rw [lastNode, lastNode, lastNode])).aWalk.nodes

-- Euler graphs --------------------------------

structure EulerPath where
  G : Graph
  aPath : Path
  ok : ∀e, e ∈ G.E → e ∈ aPath.aWalk.aWalk
     ∧ ∀n, n ∈ G.N → n ∈ aPath.aWalk.nodes

instance : Repr EulerPath where
  reprPrec w _ :=
    let formatEdge := fun n => (f!"v{n.i}~v{n.j}")
    let formatNode := fun n => (f!"v{n}")
    f!"{[formatNode w.aPath.aWalk.start]++(List.map formatEdge w.aPath.aWalk.aWalk)++[formatNode (lastNode w.aPath.aWalk.start w.aPath.aWalk.aWalk)]}"


def G1 := Graph.mk [1,2,3] [Edge.mk 1 1 2, Edge.mk 2 2 3] (by simp)
#eval EulerPath.mk G1 (Path.mk (Walk.mk 1  [Edge.mk 1 1 2, Edge.mk 2 2 3] (by simp; decide)) (isSimple (Walk.mk 1  [Edge.mk 1 1 2, Edge.mk 2 2 3] (by simp; decide))) (by exact rfl)) (by simp; decide)


-- the Isabelle's graphs paper implementation doesn't require that the cycle to contain every node
-- of the graph G.
-- but, as in our classes we've stated that it needs to contain all the nodes, the implementation
-- below also has that requirement.
structure EulerCycle where
  G : Graph
  aCycle : Cycle
  ok : ∀e, e ∈ G.E → e ∈ aCycle.aWalk.aWalk
     ∧ ∀n, n ∈ G.N → n ∈ aCycle.aWalk.nodes

instance : Repr EulerCycle where
  reprPrec w _ :=
    let formatEdge := fun n => (f!"v{n.i}~v{n.j}")
    let formatNode := fun n => (f!"v{n}")
    f!"{[formatNode w.aCycle.aWalk.start]++(List.map formatEdge w.aCycle.aWalk.aWalk)++[formatNode (lastNode w.aCycle.aWalk.start w.aCycle.aWalk.aWalk)]}"


#eval EulerCycle.mk K3 (Cycle.mk (Walk.mk 1 [Edge.mk 1 1 2, Edge.mk 2 2 3, Edge.mk 3 3 1] (by simp; exact ite_some_none_eq_some.mp rfl)) (by simp; decide)) (by simp; decide)


def Degree (n : Node) (E : List Edge) : Nat :=
match E with
| [] => 0
| x::xs => if x.i == n ∨ x.j == n then 1 + (Degree n xs) else Degree n xs

#eval Degree 1 (K 4 (by simp; decide)).E

def hasECycle (G : Graph) : Prop :=
  ∀ n ∈ G.N, (Degree n G.E) % 2 = 0

instance : Decidable (hasECycle G) := by
  simp [hasECycle]
  exact List.decidableBAll (fun x => Degree x G.E % 2 = 0) G.N

#eval hasECycle K3
#eval hasECycle (K 4 (by simp;decide))


def ECyclePair (_ : EulerCycle): Prop :=
  true

example (EC : EulerCycle) (G : Graph) : hasECycle EC.G ↔ ECyclePair EC := by
  simp [hasECycle, ECyclePair]
  induction EC.G.E with
  | nil => simp [Degree]
  | cons a as ih =>
  intro n
  simp [Degree]
  by_cases h : a.i = n
  simp [h]
  sorry
  sorry

example (EC : EulerCycle) (G : Graph) : hasECycle EC.G ↔ ECyclePair EC := by
  simp [hasECycle, ECyclePair]
  induction EC.G.N with
  | nil => simp
  | cons t ts ih =>
    intro n
    by_cases h : n ≠ t ∧ n ∈ ts
    cases h
    rename_i ht
    simp
    simp at ih
    rw [ih]
    simp
    apply ht
    simp at h
    sorry


-- Hamiltonian Graphs ------------------------------

structure HamCycle where
  G : Graph
  aCycle : Cycle
  ok : ∀ n ∈ G.N, n ∈ aCycle.aWalk.nodes
     ∧ unique (aCycle.aWalk.nodes.filter (λ x => x != aCycle.aWalk.start))

instance : Repr HamCycle where
  reprPrec w _ :=
    let formatEdge := fun n => (f!"v{n.i}~v{n.j}")
    let formatNode := fun n => (f!"v{n}")
    f!"{[formatNode w.aCycle.aWalk.start]++(List.map formatEdge w.aCycle.aWalk.aWalk)++[formatNode (lastNode w.aCycle.aWalk.start w.aCycle.aWalk.aWalk)]}"


#eval HamCycle.mk K3 (Cycle.mk (Walk.mk 1 [Edge.mk 1 1 2, Edge.mk 2 2 3, Edge.mk 3 3 1] (by simp; decide)) (by simp; decide)) (by simp; decide)

-- first try of implementing a sufficient condition checker
def old_hasHamCycle (G : Graph) : Prop :=
  ∀m n, m ∈ G.N ∧ n ∈ G.N ∧ ¬(G.adjacent m n) → Degree m G.E + Degree n G.E ≥ G.N.length ∧ G.N.length ≥ 3

def hasHam (G:Graph) (N:List Node) : Prop :=
  match N with
  | [] => true
  | t::ts =>
    let D := G.N.length
    if ∀n ∈ ts, Degree n G.E + Degree t G.E ≥ D ∧ G.N.length ≥ 3 then hasHam G ts else false

def hasHamB (G:Graph) (N:List Node) : Bool :=
  match N with
  | [] => true
  | t::ts =>
    let D := G.N.length
    if ∀n ∈ ts, Degree n G.E + Degree t G.E ≥ D ∧ G.N.length ≥ 3 then hasHamB G ts else false

def hasHam_hasHamB_iff {G : Graph} {N : List Node} : hasHamB G N  ↔ hasHam G N:= by
  induction N with
  | nil =>
    rfl
  | cons t ts ih =>
    simp [hasHam, hasHamB]
    exact fun _ => ih

instance : Decidable (hasHam G N) := decidable_of_bool _ hasHam_hasHamB_iff

abbrev hasHamCycle (G : Graph) : Prop := hasHam G G.N

#eval hasHamB K3 K3.N
#eval hasHam K3 K3.N
#eval hasHamCycle K3

-- this decidable is not provable with what we currently have
def isConnected (G : Graph) : Prop :=
  ∀ m n, m ∈ G.N ∧ n ∈ G.N → ∃ (P : Path), P.aWalk.start = m ∧ lastNode P.aWalk.start P.aWalk.aWalk = n

-- Isomorphism ----------------------------------------
@[simp]
def isSubGraph (G H : Graph) : Prop :=
  if (∀ n, n ∈ G.N → n ∈ H.N)
   ∧ (∀ e, e ∈ G.E → ∃ d ∈ H.E, d.i = e.i ∧ d.j = e.j
      ∧ (e.i ∈ G.N ∧ e.j ∈ G.N))
  then true
  else false

@[simp]
instance : Decidable (isSubGraph G H) := by
  rw [isSubGraph]
  exact
    (if
            (∀ (n : Node), n ∈ G.N → n ∈ H.N) ∧
              ∀ (e : Edge),
                e ∈ G.E → ∃ d, d ∈ H.E ∧ d.i = e.i ∧ d.j = e.j ∧ e.i ∈ G.N ∧ e.j ∈ G.N then
          true
        else false).decEq
      true

--other implementation of graphs that can work better for planarity

abbrev oEdge := Nat

structure oGraph where
  N : List Node
  E : List oEdge
  t : oEdge → Node
  h : oEdge → Node
  ok : ∀ e ∈ E, (t e) ∈ N ∧ (h e) ∈ N


#eval isSubGraph (K 3 (by simp;decide)) (K 2 (by simp; decide))
#eval isSubGraph (K 3 (by simp;decide)) (K 4 (by simp; decide))

@[simp]
def Isomorphism (G H : Graph) (f_n : Node -> Node) (f_e : Edge -> Edge) : Prop :=
  (List.map f_n G.N) = H.N ∧ (List.map f_e G.E) = H.E

instance : Decidable (Isomorphism G H f_n f_e) := by
  rw [Isomorphism]

  exact instDecidableAnd

#eval List.map (Nat.add 1 ·) (K 3 (by simp;decide)).N
#eval List.map (fun x => Edge.mk x.id (x.i + 1) (x.j + 1)) (K 3 (by simp;decide)).E
def H := Graph.mk (List.map (Nat.add 1 ·) (K 3 (by simp;decide)).N) (List.map (fun x => Edge.mk x.id (x.i + 1) (x.j + 1)) (K 3 (by simp;decide)).E) (by simp; decide)
#eval Isomorphism (K 3 (by simp;decide)) H (Nat.add 1 ·) (fun x => Edge.mk x.id (x.i + 1) (x.j + 1))

def K5 : Graph := K 5 (by simp;decide)
def K33 : Graph := Graph.mk [1,2,3,4,5,6] [(Edge.mk 1 1 4), (Edge.mk 2 1 5), (Edge.mk 3 1 6),(Edge.mk 4 2 4), (Edge.mk 5 2 5), (Edge.mk 6 2 6),(Edge.mk 7 3 4), (Edge.mk 8 3 5), (Edge.mk 9 3 6)] (by simp)

-- the instances below were defined when trying to prove the decidability of planarity

instance : Decidable (isSubGraph H G ∧ (Isomorphism H K33 f_n f_e ∨ Isomorphism H K5 f_n f_e)) := by
  rw [Isomorphism]
  rw [Isomorphism]
  rw [isSubGraph]
  exact instDecidableAnd

def isSG (G H: Graph) :=  isSubGraph G H
def isAdj (G : Graph) (f_n : Node -> Node) (f_e : Edge -> Edge):=  Isomorphism G K33 f_n f_e ∨ Isomorphism G K5 f_n f_e

instance : Decidable (isSG G H) := by
  rw [isSG]
  exact instDecidableIsSubGraph

instance : Decidable (∃ f_n f_e, Isomorphism G K33 f_n f_e ∨ Isomorphism G K5 f_n f_e) := by
  simp
  unfold List.map
  by_cases h : G.N = []
  rw [h]
  simp
  have h : K33.N = [1,2,3,4,5,6] := by rfl
  have h2 : K5.N = [1,2,3,4,5] := by rfl
  have h3 : K5.N ≠ [] := by rw [h2]; simp
  rw [h, h2]
  simp
  apply instDecidableFalse
  have h1 : G.N ≠ [] := by apply h
  sorry

instance : Decidable (isAdj G f_n f_e) := by
  rw [isAdj]
  simp
  exact instDecidableOr

-- two implementations of planarity that can't be used because of the absence of a proof of decidability

structure Planarity where
  H : Graph
  isPlanar := ∃G f_n f_e, ¬(isAdj G f_n f_e) ∧ isSG G H -- not possible to prove decidability
deriving Repr

instance : Decidable (∃ H f_n f_e, isSubGraph H G ∧ (Isomorphism H K33 f_n f_e ∨ Isomorphism H K5 f_n f_e)) :=
  by sorry

def isnotPlanar (G : Graph) : Prop :=
 ∃H f_n f_e, (isSubGraph H G ) ∧ (Isomorphism H K33 f_n f_e ∨ Isomorphism H K5 f_n f_e)


instance : Decidable (isnotPlanar G) := by
  rw [isnotPlanar]
  exact instDecidableExistsGraphForallNodeForallEdgeAndIsSubGraphOrIsomorphismK33K5

#eval isnotPlanar K5

end GraphTheory
