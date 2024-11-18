namespace GraphTheory


-- Node ---------------------------------

abbrev Node := Nat

@[simp]
def unique [BEq a] (as : List a) := (as ≠ []) → ∀ a ∈ as, (as.filter (. == a)).length = 1

instance  [BEq a] {as : List a} : Decidable  (unique as) := by
  rw [unique]
  induction as with
  | nil => simp; exact instDecidableTrue
  | cons a as ih =>
    simp
    exact instDecidableAnd

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

def e1 := (K3.E.get? 1).get (by decide)
def e2 := (K3.E.get? 2).get (by decide)

#eval Graph.parallel K3 e1 e2



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
#eval L 2  <| newL 2 4 [(2,(0,1)), (3,(0,1))]
#eval LPair 2 [(2, 0, 4), (3, 0, 1)]

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

def new_Ls (ns : List Node) (v : Int) : List (Node × (Node × Int)) :=
ns.map (fun x => (x,(0, v)))

#eval newL 1 0 <| new_Ls (K 3 (by simp; decide)).N (-1)

def Node.adjacent (es : List Edge) (n m : Node) := ∃ e, e ∈ es ∧ e.incident n ∧ e.incident m ∧ n ≠ m

instance : Decidable (Node.adjacent es n m) := by
  simp [Node.adjacent, Edge.incident]; exact List.decidableBEx _ es


def filterAdj (n : Node) (g : List Node) (es : List Edge) : List Node :=
  g.filter (Node.adjacent es n)

#eval filterAdj 1 (K 4 (by simp; decide)).N (K 4 (by simp; decide)).E
#eval (K 4 (by simp; decide)).adjacent 1 1

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

def UpdateLsMap (v : Node) (ns : List Node) (l : List (Node × (Node × Int)))  (ws : List (Edge × Int))
  : List (Node × (Node × Int)) :=
  List.foldr (fun x y => updateLs v x y ws) l ns

#eval UpdateLsMap 1 [2, 3] [(1, 0, 2), (2, 0, 4), (3, 0, 4)] [(Edge.mk 1 1 3, 1), (Edge.mk 1 1 2, 1)]
#eval UpdateLsMap 1 [2, 3] [(1, 0, 2), (2, 0, 4), (3, 0, 4)] [(Edge.mk 1 1 3, 3), (Edge.mk 1 1 2, 4)]

def isinGraph (n : Node) (ns : List Node) : Bool :=
  if (ns.filter (· == n)).length >= 1 then true else false

#eval isinGraph 1 [2,3]

def t1 : (new_Ls [a] (-1))++(new_Ls as (-1)) = new_Ls (a::as) (-1) := by
      induction as with
      | nil => rfl
      | cons b bs _ =>
        rfl

example : ∀ v, v ∈ T → (fun x => MinLNode (0,x) (UpdateLsMap v (filterAdj v T es) (new_Ls T (-1)) ws)) (findMinL (0,-1)  (UpdateLsMap v (filterAdj v T es) (new_Ls T (-1)) ws)) ∈ T := by
  simp
  induction T with
  | nil => simp
  | cons a as ih =>
    intro v
    intro h
    rw [←t1]
    simp
    sorry

-- definition still partial
partial def dijkstra (a z : Node) (G : Graph) (W : List (Edge × Int)) : List (Node × (Node × Int)) :=
  let labels := newL a 0 <|new_Ls G.N (-1)
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
        let new_lbs := List.filter (fun x => x.1 != v) (UpdateLsMap v ads ls ws)
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
#eval dijkstra 1 3 (K 3 (by simp; decide)) [(Edge.mk 1 1 3, 5), (Edge.mk 2 1 2, 1), (Edge.mk 3 3 2, 1)]


-- hamiltonian paths
def casB (m n : Node) (E : List Edge) : Bool :=
match E with
| [] => if m == n then true else false
| a::as => if m == a.i then casB a.j n as else false

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

def FirstNode (E : List Edge) : Node :=
  match E with
  | [] => 0
  | a::_ => a.i

def LastNode (n : Node) (E : List Edge) : Node :=
  match E with
  | [] => n
  | a::as => LastNode a.j as

structure Walk where
  start : Node
  walk : List Edge
  ok : cas start (LastNode start walk) walk
       ∧ ((walk = []) ∨ start = (FirstNode walk))

instance : Repr Walk where
  reprPrec w _ :=
    let formatEdge := fun n => (f!"v{n.i}~v{n.j}")
    let formatNode := fun n => (f!"v{n}")
    f!"{[formatNode w.start]++(List.map formatEdge w.walk)++[formatNode (LastNode w.start w.walk)]}"

#eval Walk.mk 1 [Edge.mk 1 1 2, Edge.mk 2 2 1] (by simp; exact ite_some_none_eq_some.mp rfl)
#eval cas 1 0 [Edge.mk 1 1 2, Edge.mk 2 6 0]

structure Path where
  path : Walk
  -- isSimple := isSimple path
  ok : unique path.walk


def Degree (n : Node) (E : List Edge) : Nat :=
match E with
| [] => 0
| x::xs => if x.i == n ∨ x.j == n then 1 + (Degree n xs) else Degree n xs

#eval Degree 1 (K 4 (by simp; decide)).E
#eval [1,2,3].filter (fun x => ) [1,2,3,4,5]



-- isomorphism
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



#eval isSubGraph (K 3 (by simp;decide)) (K 4 (by simp; decide))
#eval isSubGraph (K 3 (by simp;decide)) (Graph.mk ((K 3 (by simp;decide)).N.insert 4) (K 3 (by simp;decide)).E (by simp; decide))

@[simp]
def isomorphism (G H : Graph) (f_n : Node -> Node) (f_e : Edge -> Edge) : Prop :=
  if (List.map f_n G.N) = H.N ∧ (List.map f_e G.E) = H.E then true else false

@[simp]
instance : Decidable (isomorphism G H f_n f_e) := by
  rw [isomorphism]
  simp
  exact instDecidableAnd

#eval List.map (Nat.add 1 ·) (K 3 (by simp;decide)).N
#eval List.map (fun x => Edge.mk x.id (x.i + 1) (x.j + 1)) (K 3 (by simp;decide)).E
def H := Graph.mk (List.map (Nat.add 1 ·) (K 3 (by simp;decide)).N) (List.map (fun x => Edge.mk x.id (x.i + 1) (x.j + 1)) (K 3 (by simp;decide)).E) (by simp; decide)
#eval isomorphism (K 3 (by simp;decide)) H (Nat.add 1 ·) (fun x => Edge.mk x.id (x.i + 1) (x.j + 1))

def K5 : Graph := K 5 (by simp;decide)
def K33 : Graph := Graph.mk [1,2,3,4,5,6] [(Edge.mk 1 1 4), (Edge.mk 2 1 5), (Edge.mk 3 1 6),(Edge.mk 4 2 4), (Edge.mk 5 2 5), (Edge.mk 6 2 6),(Edge.mk 7 3 4), (Edge.mk 8 3 5), (Edge.mk 9 3 6)] (by simp)


@[simp]
instance : Decidable (isomorphism G K33 f_n f_e ∨ isomorphism G K5 f_n f_e) := by
  exact instDecidableOr


instance : Decidable (∃ H f_n f_e, isSubGraph H G ∧ isomorphism H K33 f_n f_e ∨ isomorphism H K5 f_n f_e) := by
  unfold isomorphism
  simp
  sorry


def isPlanar (G : Graph) : Bool :=
if (∃ H f_n f_e, isSubGraph H G ∧ (isomorphism H K33 f_n f_e) ∨ (isomorphism H K5 f_n f_e))
then false else true

instance : Decidable (isPlanar G) := by
  rw [isPlanar]
  exact
    (if ∃ H f_n f_e, isSubGraph H G ∧ isomorphism H K33 f_n f_e ∨ isomorphism H K5 f_n f_e then
          false
        else true).decEq
      true

#eval isPlanar K5

end GraphTheory
