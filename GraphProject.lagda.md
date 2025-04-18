# Graph Project

First, we import some definitions we need. We will import others as they are
needed.

```agda
module GraphProject where

-- _×_
open import Data.Product

-- ℕ
open import Data.Nat
import Data.Nat.Properties as Nat

-- List
open import Data.List as List using (List; []; _∷_; _++_; [_]; reverse; _∷ʳ_; lookup; filter)
import Data.List.Properties as List

-- _≡_
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; _≢_; module ≡-Reasoning)
```

We define the Graph record, which identifies the operations required for a
graph implementation. Here, `V` represents the type of vertices/nodes (edges are
of type `V × V`), and `G` is the type of the graph instance.

Here, we consider only simple graphs, and we will only consider undirected
implementations.

```agda
open import Data.Vec using (Vec)
import Data.Vec as Vec
open import Relation.Nullary.Negation

record Graph (V : Set) (G : Set) : Set₁ where
  field
    -- The empty graph for the given implementation
    empty : G

    -- Values of isnode g v are proofs that v is a node in g
    isnode : (g : G) (v : V) → Set
    -- Adds a node to the graph, returning the new graph. A proof that the node
    -- does not yet exist is required.
    addnode : (g : G) (v : V) (npv : ¬ isnode g v) → G

    -- Values of isedge g uv are proofs that uv is an edge in g
    isedge : (g : G) (uv : V × V) → Set
    -- Adds a node to the graph, returning the new graph. A couple proofs are
    -- required:
    --   - The edge must not be a self-loop (u ≢ v)
    --   - Both endpoints must be nodes in the graph
    --   - The edge must not exist yet
    addedge : (g : G) (uv : V × V) (nuv : proj₁ uv ≢ proj₂ uv) (pu : isnode g (proj₁ uv)) (pv : isnode g (proj₂ uv)) (npuv : ¬ isedge g uv) → G

    -- The number of nodes in the graph
    n : G → ℕ
    -- A vector of nodes in the graph
    nodes : (g : G) → Vec V (n g)
    -- The number of edges in the graph
    m : G → ℕ
    -- The number of neighbours of a given vertex
    nnbors : G → V → ℕ
    -- The neighbours of a given vertex
    nbors : (g : G) (v : V) → Vec V (nnbors g v)
```

The following are definitions of some small tools we will need for a later graph
implementations: a notion of a list containing an element (`contains`) and the
related notion of a list with unique elements (and with a witness to their
uniqueness)

```agda
open import Data.Fin using (Fin)

-- A value of contains l v is a proof that l contains v
-- We take a constructive approach: l contains v iff there is some index n at
-- which `lookup l n` will give us `v`.
contains : ∀ {A : Set} (l : List A) (v : A) → Set
contains l v = Σ[ n ∈ Fin (List.length l) ] lookup l n ≡ v

-- A witness to the fact that a list l contains unique elements
-- This is by-default true for the empty list, and can be shown for further
-- lists by providing a proof that the 'added element' does not occur later on
-- in the list.
data UniqueWitness {A : Set} : (l : List A) → Set where
  empty : UniqueWitness []
  unique : ∀ {x xs} → ¬ contains xs x → UniqueWitness xs → UniqueWitness (x ∷ xs)

-- A list with a witness to its uniqueness.
record UniqueList (A : Set) : Set where
  constructor _\\_
  field
    l : List A
    wf : UniqueWitness l
```

Here, we implement a graph as a list of vertices and edges. The list of vertices
is unique. We specify vertices by (arbitrary) natural numbers.

```agda
open import Relation.Unary using (Decidable)
open import Relation.Nullary.Decidable using (yes; no)


length-conv : {A : Set} {n m : ℕ} → (n ≡ m) → Vec A n → Vec A m
length-conv Eq.refl v = v

-- A predicate on A × B parametrised on a predicate for A. This predicate holds
-- on (u , v) iff the predicate P holds on u.
data First {A B : Set} (P : A → Set) : A × B → Set where
  observe : ∀ {xy : A × B} → P (proj₁ xy) → First P xy

-- A proof/method to convert a decidable predicate for P into a decidable
-- predicate for `First P`.
First? : ∀ {A B : Set} {P : A → Set} → Decidable P → Decidable (First {A} {B} P)
First? P? (x , _) with P? x
... | yes Px = yes (observe Px)
... | no ¬Px = no λ{ (observe Px) → ¬Px Px }

-- Our graph instances - G - is going to be a unique list of vertices and a list
-- of edges.
Edgelist : Set
Edgelist = UniqueList ℕ × List (ℕ × ℕ)

-- We implement this graph record below.
edgelist-nat-graph : Graph ℕ Edgelist
edgelist-nat-graph .Graph.empty = [] \\ empty , []

-- A natural number is a node iff the vertex list contains it
edgelist-nat-graph .Graph.isnode ( vs \\ _ , _ ) v = contains vs v
edgelist-nat-graph .Graph.addnode  ( vs \\ wit , es ) v p = (v ∷ vs) \\ (unique p wit) , es

-- A natural number pair is an edge iff the edge list contains it
edgelist-nat-graph .Graph.isedge (_ , es) e = contains es e
-- This is what makes the graph undirected: when we add (u , v), we also add
-- (v , u)
edgelist-nat-graph .Graph.addedge (vs , es) (u , v) _ _ _ _ = vs , (u , v) ∷ (v , u) ∷ es

edgelist-nat-graph .Graph.n (vs \\ _ , _) = List.length vs
edgelist-nat-graph .Graph.nodes (vs \\ _ , _) = Vec.fromList vs

-- Note that, since we added both (u , v) and (v , u) to the edgelist upon
-- adding (u , v), we need to halve our answer for the number of edges.
edgelist-nat-graph .Graph.m (_ , es) = List.length es / 2

-- To find the number of neighbours, we filter the edgelist by looking for
-- edges with 'begin at' u. For every neighbour v, the edge (u , v) will be in
-- the edge list, so we simply count the number of these. To get the neighbours
-- themselves, we omit the counting step (and we project into the second element
-- of the edge, which is the neighbour itself).
edgelist-nat-graph .Graph.nnbors (_ , es) v = List.length (filter (First? (Nat._≟_ v)) es)
edgelist-nat-graph .Graph.nbors (_ , es) v = length-conv (List.length-map proj₂ (filter (First? (Nat._≟_ v)) es))
                                             (Vec.fromList (List.map proj₂ (filter (First? (Nat._≟_ v)) es)))
```

QUESTION FOR READER: is there a way to make the implementation of
`edgelist-nat-graph .Graph.nnbors`
Look something like:
`edgelist-nat-graph .Graph.nnbors (_ , es) v = List.length (filter (First? (Nat._≟_ v)) es)`
Currently, Agda will complain that it doesn't know that
`Vec.fromList (List.map proj₂ (filter (First? (Nat._≟_ v)) es))`
Has length equal to `List.length (filter (First? (Nat._≟_ v)) es)`, which makes
sense: it "doesn't know" that List.map does not change the length. But there is
a lemma for this (length-map). I added `length-conv` to handle this, but this
seems ugly - is this the only way?

The following code sets up our environment for graph induction. The idea is
based on graphs' recursive definition, as follows. A graph is either:
- Empty (no vertices, no edges)
- The result of adding a vertex to a graph
- The result of adding an edge to a graph

Thus, each valid graph has a "construction" that encodes which operations were
performed on the empty graph to get there. If, for any construction, one can
prove a property about the graph, then the property must be true for all
graphs. This is the idea behind `graph-induction`: a value of this type is a
proof about all graphs (of a certain implementation) by induction on the
operations used to create that graph.

```agda
-- A graph construction is a value that specifies how a given graph was created.
data GraphConstruction {V G} (Gr : Graph V G) : G → Set where
  empty-gcons : GraphConstruction Gr (Graph.empty Gr)
  addnode-gcons : ∀ {g} → GraphConstruction Gr g → ∀ {v npv} → GraphConstruction Gr (Graph.addnode Gr g v npv)
  addegde-gcons : ∀ {g} → GraphConstruction Gr g → ∀ {uv nuv pu pv npuv} → GraphConstruction Gr (Graph.addedge Gr g uv nuv pu pv npuv)

-- This is parametrised on a graph implementation and a predicate.
-- A proof by graph induction is a function that takes in any graph, takes in
-- how it was constructed, and proves that the property holds.
graph-induction : ∀ {V G} → (Gr : Graph V G) → (P : Graph V G → G → Set) → Set
graph-induction {G = G} Gr P = {g : G} → GraphConstruction Gr g → P Gr g
```

As a simple initial example of graph induction, we show that the graphs
implemented above are undirected.

```agda
undirected : ∀ {V G} (Gr : Graph V G) → (g : G) → Set
-- A graph is undirected if, for every edge (u , v), (v , u) is also an edge
undirected {V} Gr g = ((uv : V × V) → Graph.isedge Gr g uv → Graph.isedge Gr g (Data.Product.swap uv))

-- This is a proof by graph induction that the edgelist-nat-graph implementation
-- is undirected.
edgelist-undirected : graph-induction edgelist-nat-graph undirected
-- This is vacuously true in the empty case
edgelist-undirected empty-gcons _ ()
-- Adding a node changes nothing about edges, so it's simply true by the IH in
-- the addnode case.
edgelist-undirected (addnode-gcons gc) uv uv-in-g = edgelist-undirected gc uv uv-in-g
-- Adding an edge has 3 sub-cases: either it was the edge that was added, or it
-- was the 'reverse' of the edge that was added, or it already existed in the
-- graph. In the first two cases, we show this directly by the definition. In
-- the last case, we use induction.
edgelist-undirected (addegde-gcons gc) _ (Fin.zero , Eq.refl) = Fin.suc Fin.zero , Eq.refl
edgelist-undirected (addegde-gcons gc) _ (Fin.suc Fin.zero , Eq.refl) = Fin.zero , Eq.refl
edgelist-undirected (addegde-gcons {g} gc) (u , v) (Fin.suc (Fin.suc idx) , Eq.refl) = Fin.suc (Fin.suc (proj₁ ih)) , proj₂ ih
                                      where
                                      ih : Graph.isedge edgelist-nat-graph g (v , u)
                                      ih = edgelist-undirected gc (u , v) (idx , Eq.refl)
```
 