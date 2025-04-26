Here, we will try to prove the handshake lemma for the edgelist implementation.
That is, for any graph G, the sum of the degrees of each vertex is twice the
number of edges. This is simple to prove via double-counting, but is much more
complicated in a mechanised setting.

This is a big proof, so we separated it into a new file.

First, we open the GraphProject module and some definitions we will need.

```agda
module HandshakeLemma where

open import GraphProject

-- _×_ and _⊎_ and ⊤ and ⊥
open import Data.Product
open import Data.Sum
open import Data.Empty
open import Data.Unit

-- ℕ
open import Data.Nat
import Data.Nat.Properties as Nat

-- List
open import Data.List as List using (List; []; _∷_; _++_; [_]; reverse; _∷ʳ_; lookup; filter)
import Data.List.Properties as List

-- _≡_
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; _≢_; module ≡-Reasoning)

open import Data.Vec using (Vec)
import Data.Vec as Vec
open import Relation.Nullary.Negation
open import Data.Fin using (Fin)
import Data.Fin as Fin
open import Relation.Nullary.Decidable using (yes; no)
```

Our first proof on the way to handshake is a proof, by induction, that a vertex
that does not exist in a given graph has no neighbours. We show this on the
adjlist implementation.

```agda
nonnode-no-edges : ∀ {V G} (Gr : Graph V G) → (g : G) → Set
nonnode-no-edges {V} Gr g = (v : V) → (¬ Graph.isnode Gr g v) → Graph.nnbors Gr g v ≡ 0

edgelist-nonnode-no-edges : graph-induction edgelist-nat-graph nonnode-no-edges
--  On an empty graph, there are no neighbours at all!
edgelist-nonnode-no-edges empty-gcons _ _ = Eq.refl
-- If we add a node, the edgelist is unchanged, so we simply proceed by the IH.
-- Note: v_nonnode tells us that v is not a node in the graph AFTER adding the
-- new node. So, it is simple to prove that v was also not a node BEFORE adding
-- the new node, which is necessary to invoke the IH.
edgelist-nonnode-no-edges (addnode-gcons {vs \\ _ , _} gc) v v_nonnode = edgelist-nonnode-no-edges gc v v_nonnode'
                            where
                            v_nonnode' : ¬ contains vs v
                            v_nonnode' (idx , Eq.refl) = v_nonnode ((Fin.suc idx) , Eq.refl)
-- If we add an edge, we know that both endpoints must have been nodes, so, in
-- particular, neither can possibly be w (which is not a node, by assumption).
-- So, we know that the "first two" (aka the new) elements of the edgelist cannot
-- mention w, so, by applying the IH, we know that w cannot be mentioned at all.
edgelist-nonnode-no-edges (addedge-gcons {vs , es} gc {u , v} {_} {u_node} {v_node}) w w_nonnode with Nat._≟_ w u in eq1 | Nat._≟_ w v in eq2
... | yes Eq.refl | _ = ⊥-elim (w_nonnode u_node)
... | _ | yes Eq.refl = ⊥-elim (w_nonnode v_node)
... | no _ | no _ rewrite eq1 rewrite eq2 = edgelist-nonnode-no-edges gc w w_nonnode
```

Note: we omit a proof that adding a node (aka `addnode`) does not change the
number of neighbours for any vertex, as this is true simply by reflexivity (as
this does not change the edgelist, which is the only construct with affects the
number of neighbours).

Next, we prove that `addedge (u, v)` adds one neighbour to `u`, adds one
neighbour to `v`, and, finally, adds one neighbours to any vertex that is either
`u` or `v` (obviously!).

```agda
-- `addedge (u, v)` adds one neighbour to `u`
addedge-adds-one-nbor : ∀ {V G} (Gr : Graph V G) → (g : G) → Set
addedge-adds-one-nbor Gr g = ∀ {u v nuv pu pv npuv} → Graph.nnbors Gr (Graph.addedge Gr g (u , v) nuv pu pv npuv) u ≡ 1 + Graph.nnbors Gr g u

-- `addedge (u, v)` adds one neighbour to `v`
addedge-adds-one-nbor' : ∀ {V G} (Gr : Graph V G) → (g : G) → Set
addedge-adds-one-nbor' Gr g = ∀ {u v nuv pu pv npuv} → Graph.nnbors Gr (Graph.addedge Gr g (u , v) nuv pu pv npuv) v ≡ 1 + Graph.nnbors Gr g v

-- `addedge (u, v)` adds one neighbour to any vertex that is `u` or `v`
addedge-adds-one-nbor'' : ∀ {V G} (Gr : Graph V G) → (g : G) → Set
addedge-adds-one-nbor'' Gr g = ∀ {w u v nuv pu pv npuv} → (w ≡ u ⊎ w ≡ v) → Graph.nnbors Gr (Graph.addedge Gr g (u , v) nuv pu pv npuv) w ≡ 1 + Graph.nnbors Gr g w

-- `addedge` requires that the edges are different, so we know that u ≡ u and
-- u ≢ v. Thus, addedge adds *exactly* one edge which begins with `u`, so `u`
-- has exactly one more neighbour than before.
edgelist-addedge-adds-one-nbor : (g : Edgelist) → addedge-adds-one-nbor edgelist-nat-graph g
edgelist-addedge-adds-one-nbor g {u} {v} {u≢v} with Nat._≟_ u u in eq1 | Nat._≟_ u v in eq2
... | no u≢u | _ = ⊥-elim (u≢u Eq.refl)
... | _ | yes u≡v = ⊥-elim (u≢v u≡v)
... | yes _ | no _ rewrite eq1 rewrite eq2 = Eq.refl

-- This is the same proof as above, just flipped somewhat
edgelist-addedge-adds-one-nbor' : (g : Edgelist) → addedge-adds-one-nbor' edgelist-nat-graph g
edgelist-addedge-adds-one-nbor' g {u} {v} {u≢v} with Nat._≟_ v u in eq1 | Nat._≟_ v v in eq2
... | _ | no v≢v = ⊥-elim (v≢v Eq.refl)
... | yes v≡u | _ = ⊥-elim (u≢v (Eq.sym v≡u))
... | no _ | yes _ rewrite eq1 rewrite eq2 = Eq.refl

-- This calls one of the above two proofs by simply matching on the injection
-- for whether the node `w` is `u` or `v`
edgelist-addedge-adds-one-nbor'' : (g : Edgelist) → addedge-adds-one-nbor'' edgelist-nat-graph g
edgelist-addedge-adds-one-nbor'' g {w = u} {u} {v} {nuv} {pu} {pv} {npuv} (inj₁ Eq.refl) = edgelist-addedge-adds-one-nbor g {u} {v} {nuv} {pu} {pv} {npuv}
edgelist-addedge-adds-one-nbor'' g {w = v} {u} {v} {nuv} {pu} {pv} {npuv} (inj₂ Eq.refl) = edgelist-addedge-adds-one-nbor' g {u} {v} {nuv} {pu} {pv} {npuv}
```

Next, we prove that `addedge (u, v)` does not modify the number of neighbours
for any vertex that is not `u` or `w`.

```agda
addedge-adds-no-nbors : ∀ {V G} (Gr : Graph V G) → (g : G) → Set
addedge-adds-no-nbors Gr g = ∀ {w u v nuv pu pv npuv} (nwu : w ≢ u) (nwv : w ≢ v) → Graph.nnbors Gr (Graph.addedge Gr g (u , v) nuv pu pv npuv) w ≡ Graph.nnbors Gr g w

-- By assumption, `w` is not either of `u` or `v`. Thus, addedge adds *exactly*
-- zero edges which begin with `u` or `v`, so `w` has exactly the same number of
-- neighbours as before.
edgelist-addedge-adds-no-nbors : (g : Edgelist) → addedge-adds-no-nbors edgelist-nat-graph g
edgelist-addedge-adds-no-nbors g {w} {u} {v} w≢u w≢v with Nat._≟_ w u in eq1 | Nat._≟_ w v in eq2
... | yes w≡u | _ = ⊥-elim (w≢u w≡u)
... | _ | yes w≡v = ⊥-elim (w≢v w≡v)
... | no _ | no _ rewrite eq1 rewrite eq2 = Eq.refl
```

Next, we prove a lemma (using the previous) that, in a list `ws` that does not
contain `u` or `v`, `List.map nnbors ws` will be 'unchanged' after
`addedge (u , v)`. Indeed, we know from the above that each individual element
will not be changed, so all we must do is show it for the entire list.

Now, in furtherance of this, we prove some helper-lemmas about our `contains`
type. Our goal here is to show that, if `contains m v` (that is, if `v ∈ m`),
then, for any `f` and `b`, `contains (f ++ m ++ b) v`. In a non-mechanised
setting, this is trivial, but here this requires a little extra work on both
sides.

To do this, we split this into two lemmas, one covering 'appending on the
front', and the other covering 'appending on the back'.

```agda
-- This first lemma covers the case where the 'back' contains the element, we
-- know that adding more items to the front will not stop the overall list from
-- containing this element.
back-contains : {A : Set} {f : List A} {b : List A} {v : A} → contains b v → contains (f ++ b) v
-- If the front is empty, the premise and the conclusion are identical
back-contains {_} {[]} c = c
-- Otherwise, recursively we know it is true, and then we 'skip the first
-- element' in the front.
back-contains {A} {fx ∷ f} {b} c with back-contains {A} {f} {b} c
... | idx , Eq.refl = (Fin.suc idx) , Eq.refl

-- A simple lemma that appending a list in front of another list increases its
-- length. It is much easier to induct on the first list (by how ≤ is set up).
-- It is a classic induction proof.
append-increases-length : {A : Set} {f : List A} {b : List A} → List.length f ≤ List.length (f ++ b)
append-increases-length {A} {[]} {b} = z≤n
append-increases-length {A} {x ∷ f} {b} = s≤s (append-increases-length {A} {f} {b})

-- A lemma saying, in effect, if you append a list onto the back of another
-- list, any lookups in the "first list" will 'stay the same'. So,
-- `lookup f i` ≡ `lookup (f ++ b) i`.
-- The statement of the lemma is complicated due to the index type relying on
-- the type of the list, but the proof is simple induction.
lookup-++-id : {A : Set} {f : List A} {b : List A} {idx : Fin (List.length f)} → lookup (f ++ b) (Fin.inject≤ idx (append-increases-length {A} {f} {b})) ≡ lookup f idx
lookup-++-id {_} {x ∷ f} {_} {Fin.zero} = Eq.refl
lookup-++-id {A} {x ∷ f} {b} {Fin.suc idx} = lookup-++-id {A} {f} {b} {idx}

-- This second lemma covers the case where the the 'front' contains the element,
-- we know that adding more items to the back will not stop the overall list
-- from containing this element.
-- This proof uses the lemma above to justify the 'same' index as the index for
-- the element, `v`.
front-contains : {A : Set} {f : List A} {b : List A} {v : A} → contains f v → contains (f ++ b) v
front-contains {A} {f} {b} (idx , Eq.refl) = Fin.inject≤ idx (append-increases-length {A} {f} {b}) , lookup-++-id {A} {f} {b} {idx}

-- The combination of the above two lemmas giving us our most general form:
-- `contains m v` → `contains (f ++ m ++ b) v`.
-- This is slightly enhanced by an additional premise `f ++ m ++ b ≡ fmb` which
-- allows us, in fact, to output `contains fmb v` (which will be useful later).
sub-contains :  {A : Set} {f : List A} {m : List A} {b : List A} {fmb : List A} {v : A} → (f ++ m ++ b ≡ fmb) → contains m v → contains fmb v
sub-contains {A} {f} {m} {b} {_} {v} Eq.refl c =
  let mb = front-contains {A} {m} {b} {v} c in
  back-contains {A} {f} {m ++ b} {v} mb

-- Simple contraposition case of back-contains that will be useful in the
-- following proof.
tail-¬contains : {A : Set} {ws : List A} {x : A} {v : A} → ¬ contains (x ∷ ws) v → ¬ contains ws v
tail-¬contains {A} {ws} {x} v∉xws v∈ws = v∉xws (back-contains {A} {[ x ]} {ws} v∈ws)
```

Now we are ready to prove the identity of `List.map nnbors ws` across an
`addedge` operation that does not involve any element of `ws`. That is, if
`u ∉ ws` and `v ∉ ws`, then `addedge (u , v)` does not change
`List.map nnbors ws`.

```agda
addedge-adds-no-nbors' : ∀ {V G} (Gr : Graph V G) → (g : G) → Set
addedge-adds-no-nbors' Gr g = ∀ {ws u v pu pv nuv npuv} (nwsu : ¬ contains ws u) (nwsv : ¬ contains ws v) → List.map (Graph.nnbors Gr (Graph.addedge Gr g (u , v) pu pv nuv npuv)) ws ≡ List.map (Graph.nnbors Gr g) ws

-- As might be expected, for this proof we go by induction on the list `ws`.
edgelist-addedge-adds-no-nbors' : (g : Edgelist) → addedge-adds-no-nbors' edgelist-nat-graph g
-- In the empty case, `map` maps nothing to nothing on both sides, so this is
-- simply reflexivity.
edgelist-addedge-adds-no-nbors' g {[]} _ _ = Eq.refl
-- In the second case, we simply use the definition of map to extract the first
-- element, use the 'base case' proved above for a single node, and then apply
-- the "IH" to the rest of the list (and then put it back together using the
-- definition of map again).
-- We get that the 'front' element is neither `u` nor `v` by the noncontainment
-- premises, and we can generate the noncontainment premises for the IH using
-- tail-ncontains proven above.
edgelist-addedge-adds-no-nbors' g {x ∷ ws} {u} {v} {u≢v} {u∈g} {v∈g} {uv∉g} u∉x∷ws v∉x∷ws =
    let gp = Graph.addedge edgelist-nat-graph g (u , v) u≢v u∈g v∈g uv∉g in
    let open ≡-Reasoning in
    begin
      List.map (Graph.nnbors edgelist-nat-graph gp) (x ∷ ws)
    ≡⟨⟩
      (Graph.nnbors edgelist-nat-graph gp x) ∷ List.map (Graph.nnbors edgelist-nat-graph gp) ws
    ≡⟨ Eq.cong₂ _∷_ (edgelist-addedge-adds-no-nbors g {x} {u} {v} {u≢v} {u∈g} {v∈g} {uv∉g} x≢u x≢v) (edgelist-addedge-adds-no-nbors' g {ws} {u} {v} {u≢v} {u∈g} {v∈g} {uv∉g} (tail-¬contains u∉x∷ws) (tail-¬contains v∉x∷ws)) ⟩
      (Graph.nnbors edgelist-nat-graph g x) ∷ List.map (Graph.nnbors edgelist-nat-graph g) ws
    ≡⟨⟩
      List.map (Graph.nnbors edgelist-nat-graph g) (x ∷ ws)
    ∎
    where
    x≢u : x ≢ u
    x≢u Eq.refl = u∉x∷ws (Fin.zero , Eq.refl)

    x≢v : x ≢ v
    x≢v Eq.refl = v∉x∷ws (Fin.zero , Eq.refl)
```

Next, we move onto a critical part of the proof, and indeed where the
'uniqueness' of the vertex list becomes important.

We have proven so far that, for the vertices involved in the `addedge (u , v)`
operation, one neighbour is added, and for all other vertices no neighbours are
added. This lends itself to our overall proof by indcution of the handshake
lemma (when we add an edge, the number of neighbours increases by 2 overall).

In order to push this idea through, the strategy is to split the vertex list,
`vs`, into five sections, as follows:
1. A front, `f`
2. Either `u` or `v` (call it `e₁`)
3. A middle, `m`
4. Either `u` or `v` (not the one not chosen for part 2, call it `e₂`)
5. A back, `b`
Then, we have that `vs ≡ f ++ e₁ ∷ m ++ e₂ ∷ b`, where each of `f`, `m`, and `b`
do not contain either `u` or `v` (and so we can call
`edgelist-addedge-adds-no-nbors'` proven above), and each of `e₁` and `e₂` are
either `u` or `v` (and so we can call
`edgelist-addedge-adds-one-nbor''` proven above), getting that the overall list
of vertices' neighbour counts are such that all but two are unchanged, and two
have each increased by one.

This is also an interestingly practical example of the proof itself being an
algorithm for computing a result.

```agda
-- Immediate helper lemma to show that the empty list does not contain any
-- elements. This is showable since there cannot be any value of the first
-- projection of the Σ type in this case: `Fin (List.length [])`, aka `Fin
-- zero`.
empty-¬contains : {A : Set} {v : A} → ¬ contains [] v
empty-¬contains ()

-- Small helper lemma to allow for the simplification of a common list form we
-- see in the following proof.
list-movement : {A : Set} {l1 : List A} {v : A} {l2 : List A} → (l1 ++ v ∷ []) ++ l2 ++ [] ≡ l1 ++ v ∷ l2
list-movement {_} {[]} {v} {[]} = Eq.refl
list-movement {A} {[]} {v} {x ∷ l2} = Eq.cong₂ _∷_ Eq.refl (list-movement {A} {[]} {x} {l2})
list-movement {A} {x ∷ l1} {v} {l2} = Eq.cong₂ _∷_ Eq.refl (list-movement {A} {l1} {v} {l2})

-- First half (and simpler version) of the double-split proof/algorithm. This
-- performs a single split, transforming a UniqueList into a 'front' `f` and
-- back `b` by 'splitting at `u`'. Overall, we know `u ∉ f` and `u ∉ b`, and
-- that `ul ≡ f ++ u ∷ b`.
unique-split : ∀ {A : Set} (ul : UniqueList A) (u : A) → (contains (UniqueList.l ul) u) → Σ[ (f , b) ∈ List A × List A ] ((f ++ u ∷ b ≡ UniqueList.l ul) × (¬ contains f u) × (¬ contains b u))
-- In the first case, the front element is `u` (note, this is because the index
-- contained within the proof of `contains ul u` is Fin.zero). Here, the 'front'
-- is empty, and the back is the rest of the list. The proofs hold trivially
-- from the definition of the uniqueness witness in the unique list.
unique-split ((x ∷ l) \\ unique x∉l _) _ (Fin.zero , Eq.refl) = ([] , l) , Eq.refl , empty-¬contains , x∉l
-- In the second case, we recurse. Then, we show that u ∉ x ∷ f: we know u ∉ f
-- by the IH, and we know u ≢ x because we know that `u` shows up further down
-- in the list, but this is a unique list (so `x` can't show up again, and so
-- u ≢ x).
unique-split {A} ((x ∷ l) \\ unique x∉l ws) u (Fin.suc idx , Eq.refl) with unique-split (l \\ ws) u (idx , Eq.refl)
... | (f , b) , (f++u∷b≡l , u∉f , u∉b) =
        (x ∷ f , b) , (Eq.cong₂ _∷_ Eq.refl f++u∷b≡l , u∉x∷f , u∉b)
        where
        u∉x∷f : ¬ contains (x ∷ f) u
        u∉x∷f (Fin.zero , Eq.refl) = x∉l (idx , Eq.refl)
        u∉x∷f (Fin.suc idxup , looku) = u∉f (idxup , looku)

-- Full double split algorithm. Of particular mention is that *we do not know*
-- which one of `u` or `v` comes first, hence leading to the ⊎ in the output.
-- We currently do not care so much which one comes first.
-- Note, critically, that u ≢ v (this applies in our case as we do not have
-- self-loops in our graphs).
unique-double-split : ∀ {A : Set} (ul : UniqueList A) (u : A) (v : A) → (contains (UniqueList.l ul) u) → (contains (UniqueList.l ul) v) → (u ≢ v) → Σ[ (f , m , b) ∈ List A × List A × List A ] (((f ++ u ∷ m ++ v ∷ b ≡ UniqueList.l ul) ⊎ (f ++ v ∷ m ++ u ∷ b ≡ UniqueList.l ul)) × (¬ contains f u) × (¬ contains f v) × (¬ contains m u) × (¬ contains m v) × (¬ contains b u) × (¬ contains b v))
-- In the first case, both `u` and `v` appear at the front of the list. But this
-- contradicts that `u ≢ v`!
unique-double-split ((_ ∷ _) \\ _ ) _ _ (Fin.zero , Eq.refl) (Fin.zero , Eq.refl) u≢v = ⊥-elim (u≢v Eq.refl)
-- In the second case, `u` is at the front of the list. Then, we use the single-
-- split algorithm to find `v` in the remainder of the list, and then put the
-- pieces back together. In particular, we know `u` cannot be in any of the
-- 'remainder' of the list by the uniqueness condition.
-- Note that, in this case, we know `u` came first, so we produce the first
-- injection for the ⊎ in the output.
unique-double-split {A} ((_ ∷ l) \\ unique u∉l wf) _ v (Fin.zero , Eq.refl) (Fin.suc idxv , Eq.refl) _ with unique-split (l \\ wf) v (idxv , Eq.refl)
... | (m , b) , (m++v∷b≡l , v∉m , v∉b) =
        ([] , m , b) , (inj₁ (Eq.cong₂ _∷_ Eq.refl m++v∷b≡l) , empty-¬contains , empty-¬contains , (λ c → u∉l (sub-contains {A} {[]} {m} m++v∷b≡l c)) , v∉m , (λ c → u∉l (sub-contains {A} {m ++ v ∷ []} {b} m++v∷[]++b++[]≡l c)) , v∉b)
        where
        m++v∷[]++b++[]≡l : (m ++ v ∷ []) ++ b ++ [] ≡ l
        m++v∷[]++b++[]≡l = Eq.trans list-movement m++v∷b≡l
-- This third case is the same as the second case, but flipping `u` and `v`.
unique-double-split {A} ((_ ∷ l) \\ unique v∉l wf) u _ (Fin.suc idxu , Eq.refl) (Fin.zero , Eq.refl) _ with unique-split (l \\ wf) u (idxu , Eq.refl)
... | (m , b) , (m++u∷b≡l , u∉m , u∉b) =
        ([] , m , b) , ( inj₂ (Eq.cong₂ _∷_ Eq.refl m++u∷b≡l) , empty-¬contains , empty-¬contains , u∉m , (λ c → v∉l (sub-contains {A} {[]} {m} m++u∷b≡l c)) , u∉b , (λ c → v∉l (sub-contains {A} {m ++ u ∷ []} {b} m++u∷[]++b++[]≡l c)) )
        where
        m++u∷[]++b++[]≡l : (m ++ u ∷ []) ++ b ++ [] ≡ l
        m++u∷[]++b++[]≡l = Eq.trans list-movement m++u∷b≡l
-- In the final case, the list starts with neither `u` nor `v`, so we just move
-- on (recurse). Then, we add `x` back to the front (and the proofs involving
-- `f`). We know u ≢ x for the same reason as in the second case of
-- unique-split, namely, `x` is here and cannot appear again, but `u` appears
-- later on. The same holds for `v`. Thus, `u ∉ x ∷ f` (as we also know `u ∉ f`
-- by the IH).
unique-double-split {A} ((x ∷ l) \\ unique x∉l wf) u v (Fin.suc idxu , Eq.refl) (Fin.suc idxv , Eq.refl) nuv with unique-double-split (l \\ wf) u v (idxu , Eq.refl) (idxv , Eq.refl) nuv
... | (f , m , b) , (f++e₁∷m++e₂∷b≡l , u∉f , v∉f , u∉m , v∉m , u∉b , v∉b) = 
        ( x ∷ f , m , b) , ( Data.Sum.map (Eq.cong₂ _∷_ Eq.refl) (Eq.cong₂ _∷_ Eq.refl) f++e₁∷m++e₂∷b≡l , u∉x∷f , v∉x∷f , u∉m , v∉m , u∉b , v∉b)
        where
        u∉x∷f : ¬ contains (x ∷ f) u
        u∉x∷f (Fin.zero , Eq.refl) = x∉l (idxu , Eq.refl)
        u∉x∷f (Fin.suc idxup , looku) = u∉f (idxup , looku)

        v∉x∷f : ¬ contains (x ∷ f) v
        v∉x∷f (Fin.zero , Eq.refl) = x∉l (idxv , Eq.refl)
        v∉x∷f (Fin.suc idxvp , lookv) = v∉f (idxvp , lookv)
```

Again as an aside, we now prove a few facts about lists and vectors. Some of
these may exist in the standard library, but it took less time to prove them
than to find them there.

```agda
-- First, we prove that `map fn (f ++ b) ≡ map fn f ++ map fn b`.
-- This is simple and by induction on `f`. The base case holds trivially and
-- the inductive case holds by congruence across ∷.
list-map-split : {A B : Set} {f : List A} {b : List A} {fn : A → B} → List.map fn (f ++ b) ≡ List.map fn f ++ List.map fn b
list-map-split {_} {_} {[]} = Eq.refl
list-map-split {A} {B} {x ∷ f} = Eq.cong₂ _∷_ Eq.refl (list-map-split {A} {B} {f})

-- Next we prove that `sum (f ++ b) ≡ sum f + sum b`.
-- This is once again simple and by induction on `f`, but a little extra work is
-- required after the IH using associativity to get the proof to line up.
list-sum-split : {f : List ℕ} {b : List ℕ} → List.sum (f ++ b) ≡ List.sum f + List.sum b
list-sum-split {[]} = Eq.refl
list-sum-split {x ∷ f} {b} =
    let open ≡-Reasoning in
    begin
      List.sum (x ∷ f ++ b)
    ≡⟨⟩
      x + List.sum (f ++ b)
    ≡⟨ Eq.cong₂ _+_ Eq.refl (list-sum-split {f} {b}) ⟩
      x + (List.sum f + List.sum b)
    ≡⟨ Nat.+-assoc x (List.sum f) (List.sum b) ⟨
      (x + List.sum f) + List.sum b
    ≡⟨⟩
      List.sum (x ∷ f) + List.sum b
    ∎

-- Finally, we show that the sum over a mapped vector (obtained from a list `l`)
-- is the same as the sum over that list mapped with the same function.
-- This too is by simple induction on the list and congruence across +. Quite a
-- bit of work here is being done by the typechecker 'automatically' for it to
-- realise that, indeed, the first element of `Vec.map fn (Vec.fromList l)` is
-- indeed the same as the first element of `List.map fn l`.
-- This is created since the graph outputs are all in terms of vectors, but all
-- the lemmas we have proved are about lists, so it would be nice to be able to
-- convert between the two.
vec-map-sum≡list-map-sum : {A : Set} {l : List A} {fn : A → ℕ} → Vec.sum (Vec.map fn (Vec.fromList l)) ≡ List.sum (List.map fn l)
vec-map-sum≡list-map-sum {_} {[]} = Eq.refl
vec-map-sum≡list-map-sum {A} {x ∷ l} = Eq.cong₂ _+_ Eq.refl (vec-map-sum≡list-map-sum {A} {l})
```

We are now ready to prove the primary 'crux' lemma: when you add an edge, the
sum of the number of neighbours across all vertices goes up by two.

This is quite a long proof, and not for very interesting reasons. A lot of the
steps are simply 'arithmetic minutiae' like associativity and commutativity of
addition, and there is a lot of repetition in the proof. This is because we
split the vector list into five parts: f, e₁, m, e₂, and b, where, for the
purposes of this proof, f, m, and b are effectively the same as each other, as
are e₁ and e₂.

We did employ one technique to 'halve' the length of the proof: we really don't
care whether `u` or `v` comes first, but, in some sense, we need to know which
is which in order to apply all the facts that we get from `unique-double-split`.
For this, we introduced the `sorted` 'lemma'/'function' which takes in the
output from `unique-double-split` and 'tells us' which came first. Its output,
instead of being in terms of `u` and `v` is in terms of `e₁` and `e₂`, which is
the actual form we care about (as we don't care which one is which, but we do
care which one is first and second). We then are also given that `e₁` and `e₂`
are both either `u` or `v` (as we will also need this for the proof).

Now, instead of copy-pasting the same proof twice, swapping some `u`s and `v`s,
we can write the proof exactly once, caring only about `e₁` and `e₂` (whatever
they may be).

```agda
-- As mentioned, this is the property that adding an edge adds two to the
-- overall sum of neighbours. This is the crux of the handshake proof.
addedge-adds-two-nbors : ∀ {V G} (Gr : Graph V G) → (g : G) → Set
addedge-adds-two-nbors Gr g = ∀ {u v nuv pu pv npuv} →
    let gp = Graph.addedge Gr g (u , v) nuv pu pv npuv in
    Vec.sum (Vec.map (Graph.nnbors Gr gp) (Graph.nodes Gr gp)) ≡ 2 + Vec.sum (Vec.map (Graph.nnbors Gr g) (Graph.nodes Gr g))

-- This is the `sorted` lemma. The type does not much shed light on its utility,
-- but the previous explanation provides its purpose. It is implemented via
-- pattern matching on the ⊎ item and constructing the output tuples
-- appropriately (effectively, flipping `u` and `v`).
sorted : ∀ {u v f m b l} → ((f ++ u ∷ m ++ v ∷ b ≡ l) ⊎ (f ++ v ∷ m ++ u ∷ b ≡ l)) → (¬ contains f u) → (¬ contains f v) → (¬ contains m u) → (¬ contains m v) → (¬ contains b u) → (¬ contains b v) → Σ[ (e1 , e2) ∈ (ℕ × ℕ) ] ((e1 ≡ u ⊎ e1 ≡ v) × (e2 ≡ u ⊎ e2 ≡ v) × (f ++ e1 ∷ m ++ e2 ∷ b ≡ l) × (¬ contains f e1) × (¬ contains f e2) × (¬ contains m e1) × (¬ contains m e2) × (¬ contains b e1) × (¬ contains b e2))
sorted {u} {v} (inj₁ Eq.refl) fu fv mu mv bu bv = (u , v) , (inj₁ Eq.refl , inj₂ Eq.refl , Eq.refl , fu , fv , mu , mv , bu , bv)
sorted {u} {v} (inj₂ Eq.refl) fu fv mu mv bu bv = (v , u) , (inj₂ Eq.refl , inj₁ Eq.refl , Eq.refl , fv , fu , mv , mu , bv , bu)

-- And finally we have the full proof. There are a couple of 'critical moves',
-- and a significanly more 'uninteresting moves' (commutativity and
-- associativity of addition being chief among them). The interesting moves are
-- as follows:
--  1. Splitting the list of vertices at `u` and `v` using unique-double-split
--  2. 'Sorting' the output (as described previously) using `sorted`
--  3. Converting the vector operation into a list operation using
--     vec-map-sum≡list-map-sum
--  4. Pulling our the front of the list (`f`) using list-map-split and
--     list-sum-split
--  5. Appling edgelist-addedge-adds-no-nbors' to `f` to show that the number of
--     neighbours stays the same after adding the new edge
--  6. Pulling out the (new) front of the list (`e₁`) using list-map-split
--     and list-sum-split (and some reflexivity)
--  7. Appling edgelist-addedge-adds-one-nbor'' to `e₁` to show that the number
--     of neighbours increases by one after adding the new edge
--  8. Performing steps 4 and 5 on the new front, `m`, to show that the number
--     of neighbours stays the same after adding the new edge
--  9. Performing steps 6 and 7 on the new front, `e₂`, to show that the number
--     of neighbours increases by one after adding the new edge
-- 10. Performing steps 4 and 5 on the remainder, `b`, to show that the number
--     of neighbours stays the same after adding the new edge
-- 11. Moving all the numbers around using associativity and commutativity of
--     addition to extract the `2 + _` from what we obtained already
-- 12. Reversing the list-map-split and list-sum-split steps on the newly-
--     reduced components, re-forming f ++ e₁ ∷ m ++ e₂ ∷ b.
-- 13. 'Unsplitting' the list f ++ e₁ ∷ m ++ e₂ ∷ b to re-form the list of
--      vertices.
-- 14. Converting this list operation back into a vector operation, so it
--     matches the proof statement.
--
-- Step 11 takes a significant number of tedious steps. Many of the individual
-- steps are very long, because a lot of congruence is required to 'target' the
-- right expression.

edgelist-addedge-adds-two-nbors : (g : Edgelist) → addedge-adds-two-nbors edgelist-nat-graph g
edgelist-addedge-adds-two-nbors (vs , es) {u} {v} {nuv} {pu} {pv} {npuv} with unique-double-split vs u v pu pv nuv
... | ((f , m , b) , ( ueq , fu , fv , mu , mv , bu , bv )) with sorted ueq fu fv mu mv bu bv
... | (e1 , e2) , (e1e , e2e , eq , fe1 , fe2 , me1 , me2 , be1 , be2) =
    let g = (vs , es) in
    let Gr = edgelist-nat-graph in
    let gp = Graph.addedge Gr g (u , v) nuv pu pv npuv in
    let open ≡-Reasoning in
    begin
      Vec.sum (Vec.map (Graph.nnbors Gr gp) (Graph.nodes Gr gp))
    ≡⟨ vec-map-sum≡list-map-sum {ℕ} {UniqueList.l vs} ⟩
      List.sum (List.map (Graph.nnbors Gr gp) (UniqueList.l vs))
    ≡⟨ Eq.cong List.sum (Eq.cong₂ List.map Eq.refl eq) ⟨
      List.sum (List.map (Graph.nnbors Gr gp) (f ++ e1 ∷ m ++ e2 ∷ b))
    ≡⟨⟩
      List.sum (List.map (Graph.nnbors Gr gp) (f ++ (e1 ∷ []) ++ m ++ (e2 ∷ []) ++ b))
    ≡⟨ Eq.cong List.sum (list-map-split {ℕ} {ℕ} {f}) ⟩
      List.sum (List.map (Graph.nnbors Gr gp) f ++ List.map (Graph.nnbors Gr gp) ((e1 ∷ []) ++ m ++ (e2 ∷ []) ++ b))
    ≡⟨ list-sum-split {List.map (Graph.nnbors Gr gp) f} ⟩
      List.sum (List.map (Graph.nnbors Gr gp) f) + List.sum (List.map (Graph.nnbors Gr gp) ((e1 ∷ []) ++ m ++ (e2 ∷ []) ++ b))
    ≡⟨ Eq.cong₂ _+_ (Eq.cong List.sum (edgelist-addedge-adds-no-nbors' g {f} {u} {v} {nuv} {pu} {pv} {npuv} fu fv)) Eq.refl ⟩
      List.sum (List.map (Graph.nnbors Gr g) f) +
      List.sum (List.map (Graph.nnbors Gr gp) ((e1 ∷ []) ++ m ++ (e2 ∷ []) ++ b))
    ≡⟨ Eq.cong₂ _+_ {List.sum (List.map (Graph.nnbors Gr g) f)} Eq.refl (Eq.cong List.sum (list-map-split {ℕ} {ℕ} {e1 ∷ []} {m ++ (e2 ∷ []) ++ b} {Graph.nnbors Gr gp})) ⟩
      List.sum (List.map (Graph.nnbors Gr g) f) +
      List.sum (List.map (Graph.nnbors Gr gp) (e1 ∷ []) ++ List.map (Graph.nnbors Gr gp) (m ++ (e2 ∷ []) ++ b))
    ≡⟨⟩
      List.sum (List.map (Graph.nnbors Gr g) f) +
      List.sum ((Graph.nnbors Gr gp e1) ∷ List.map (Graph.nnbors Gr gp) (m ++ (e2 ∷ []) ++ b))
    ≡⟨⟩
      List.sum (List.map (Graph.nnbors Gr g) f) +
      (Graph.nnbors Gr gp e1 +
      List.sum (List.map (Graph.nnbors Gr gp) (m ++ (e2 ∷ []) ++ b)))
    ≡⟨ Eq.cong₂ _+_ Eq.refl (Eq.cong₂ _+_ (edgelist-addedge-adds-one-nbor'' g {nuv = nuv} {pu = pu} {pv = pv} {npuv = npuv} e1e) Eq.refl) ⟩
      List.sum (List.map (Graph.nnbors Gr g) f) +
      ((1 + Graph.nnbors Gr g e1) +
      List.sum (List.map (Graph.nnbors Gr gp) (m ++ (e2 ∷ []) ++ b)))
    ≡⟨ Eq.cong₂ _+_ Eq.refl (Nat.+-assoc 1 (Graph.nnbors Gr g e1) (List.sum (List.map (Graph.nnbors Gr gp) (m ++ (e2 ∷ []) ++ b)))) ⟩
      List.sum (List.map (Graph.nnbors Gr g) f) +
      (1 + (Graph.nnbors Gr g e1 +
      List.sum (List.map (Graph.nnbors Gr gp) (m ++ (e2 ∷ []) ++ b))))
    ≡⟨ Nat.+-assoc (List.sum (List.map (Graph.nnbors Gr g) f)) 1 (Graph.nnbors Gr g e1 + List.sum (List.map (Graph.nnbors Gr gp) (m ++ (e2 ∷ []) ++ b))) ⟨
      (List.sum (List.map (Graph.nnbors Gr g) f) +
      1) + (Graph.nnbors Gr g e1 +
      List.sum (List.map (Graph.nnbors Gr gp) (m ++ (e2 ∷ []) ++ b)))
    ≡⟨ Eq.cong₂ _+_ (Nat.+-comm (List.sum (List.map (Graph.nnbors Gr g) f)) 1) Eq.refl ⟩
      1 +
      List.sum (List.map (Graph.nnbors Gr g) f) +
      (Graph.nnbors Gr g e1 +
      List.sum (List.map (Graph.nnbors Gr gp) (m ++ (e2 ∷ []) ++ b)))
    ≡⟨ Eq.cong₂ _+_ {1 + List.sum (List.map (Graph.nnbors Gr g) f)} Eq.refl (Eq.cong₂ _+_ Eq.refl (Eq.cong List.sum (list-map-split {ℕ} {ℕ} {m}))) ⟩
      1 +
      List.sum (List.map (Graph.nnbors Gr g) f) +
      (Graph.nnbors Gr g e1 +
      List.sum (List.map (Graph.nnbors Gr gp) m ++ List.map (Graph.nnbors Gr gp) ((e2 ∷ []) ++ b)))
      -- Plausibly could be more efficient here
    ≡⟨ Eq.cong₂ _+_ {1 + List.sum (List.map (Graph.nnbors Gr g) f)} Eq.refl (Eq.cong₂ _+_ Eq.refl (list-sum-split {List.map (Graph.nnbors Gr gp) m})) ⟩
      1 +
      List.sum (List.map (Graph.nnbors Gr g) f) +
      (Graph.nnbors Gr g e1 +
      (List.sum (List.map (Graph.nnbors Gr gp) m) +
      List.sum (List.map (Graph.nnbors Gr gp) ((e2 ∷ []) ++ b))))
    ≡⟨ Eq.cong₂ _+_ {1 + List.sum (List.map (Graph.nnbors Gr g) f)} Eq.refl (Eq.cong₂ _+_ {Graph.nnbors Gr g e1} Eq.refl (Eq.cong₂ _+_ (Eq.cong List.sum (edgelist-addedge-adds-no-nbors' g {m} {u} {v} {nuv} {pu} {pv} {npuv} mu mv)) Eq.refl)) ⟩
      1 +
      List.sum (List.map (Graph.nnbors Gr g) f) +
      (Graph.nnbors Gr g e1 +
      (List.sum (List.map (Graph.nnbors Gr g) m) +
      List.sum (List.map (Graph.nnbors Gr gp) ((e2 ∷ []) ++ b))))
    ≡⟨ Eq.cong₂ _+_ {1 + List.sum (List.map (Graph.nnbors Gr g) f)} Eq.refl (Eq.cong₂ _+_ {Graph.nnbors Gr g e1} Eq.refl (Eq.cong₂ _+_ {List.sum (List.map (Graph.nnbors Gr g) m)} Eq.refl (Eq.cong List.sum (list-map-split {ℕ} {ℕ} {e2 ∷ []} {b} {Graph.nnbors Gr gp})))) ⟩
      1 +
      List.sum (List.map (Graph.nnbors Gr g) f) +
      (Graph.nnbors Gr g e1 +
      (List.sum (List.map (Graph.nnbors Gr g) m) +
      List.sum (List.map (Graph.nnbors Gr gp) (e2 ∷ []) ++ List.map (Graph.nnbors Gr gp) b)))
    ≡⟨⟩
      1 +
      List.sum (List.map (Graph.nnbors Gr g) f) +
      (Graph.nnbors Gr g e1 +
      (List.sum (List.map (Graph.nnbors Gr g) m) +
      List.sum ((Graph.nnbors Gr gp e2) ∷ List.map (Graph.nnbors Gr gp) b)))
    ≡⟨⟩
      1 +
      List.sum (List.map (Graph.nnbors Gr g) f) +
      (Graph.nnbors Gr g e1 +
      (List.sum (List.map (Graph.nnbors Gr g) m) +
      (Graph.nnbors Gr gp e2 +
      List.sum (List.map (Graph.nnbors Gr gp) b))))
    ≡⟨ Eq.cong₂ _+_ {1 + List.sum (List.map (Graph.nnbors Gr g) f)} Eq.refl (Eq.cong₂ _+_ {Graph.nnbors Gr g e1} Eq.refl (Eq.cong₂ _+_ {List.sum (List.map (Graph.nnbors Gr g) m)} Eq.refl (Eq.cong₂ _+_ (edgelist-addedge-adds-one-nbor'' g {nuv = nuv} {pu = pu} {pv = pv} {npuv = npuv} e2e) Eq.refl))) ⟩
      1 +
      List.sum (List.map (Graph.nnbors Gr g) f) +
      (Graph.nnbors Gr g e1 +
      (List.sum (List.map (Graph.nnbors Gr g) m) +
      ((1 + Graph.nnbors Gr g e2) +
      List.sum (List.map (Graph.nnbors Gr gp) b))))
    ≡⟨ Eq.cong₂ _+_ {1 + List.sum (List.map (Graph.nnbors Gr g) f)} Eq.refl (Eq.cong₂ _+_ {Graph.nnbors Gr g e1} Eq.refl (Eq.cong₂ _+_ {List.sum (List.map (Graph.nnbors Gr g) m)} Eq.refl (Nat.+-assoc 1 (Graph.nnbors Gr g e2) (List.sum (List.map (Graph.nnbors Gr gp) b))))) ⟩
      1 +
      List.sum (List.map (Graph.nnbors Gr g) f) +
      (Graph.nnbors Gr g e1 +
      (List.sum (List.map (Graph.nnbors Gr g) m) +
      (1 + (Graph.nnbors Gr g e2 +
      List.sum (List.map (Graph.nnbors Gr gp) b)))))
    ≡⟨ Eq.cong₂ _+_ {1 + List.sum (List.map (Graph.nnbors Gr g) f)} Eq.refl (Eq.cong₂ _+_ {Graph.nnbors Gr g e1} Eq.refl (Nat.+-assoc (List.sum (List.map (Graph.nnbors Gr g) m)) 1 (Graph.nnbors Gr g e2 + List.sum (List.map (Graph.nnbors Gr gp) b)))) ⟨
      1 +
      List.sum (List.map (Graph.nnbors Gr g) f) +
      (Graph.nnbors Gr g e1 +
      ((List.sum (List.map (Graph.nnbors Gr g) m) +
      1) + (Graph.nnbors Gr g e2 +
      List.sum (List.map (Graph.nnbors Gr gp) b))))
    ≡⟨ Eq.cong₂ _+_ {1 + List.sum (List.map (Graph.nnbors Gr g) f)} Eq.refl (Eq.cong₂ _+_ {Graph.nnbors Gr g e1} Eq.refl (Eq.cong₂ _+_ (Nat.+-comm (List.sum (List.map (Graph.nnbors Gr g) m)) 1) Eq.refl)) ⟩
      1 +
      List.sum (List.map (Graph.nnbors Gr g) f) +
      (Graph.nnbors Gr g e1 +
      (1 +
      (List.sum (List.map (Graph.nnbors Gr g) m) +
      (Graph.nnbors Gr g e2 +
      List.sum (List.map (Graph.nnbors Gr gp) b)))))
    ≡⟨ Eq.cong₂ _+_ {1 + List.sum (List.map (Graph.nnbors Gr g) f)} Eq.refl (Nat.+-assoc (Graph.nnbors Gr g e1) 1 (List.sum (List.map (Graph.nnbors Gr g) m) + (Graph.nnbors Gr g e2 + List.sum (List.map (Graph.nnbors Gr gp) b)))) ⟨
      1 +
      List.sum (List.map (Graph.nnbors Gr g) f) +
      ((Graph.nnbors Gr g e1 +
      1) +
      (List.sum (List.map (Graph.nnbors Gr g) m) +
      (Graph.nnbors Gr g e2 +
      List.sum (List.map (Graph.nnbors Gr gp) b))))
    ≡⟨ Eq.cong₂ _+_ {1 + List.sum (List.map (Graph.nnbors Gr g) f)} Eq.refl (Eq.cong₂ _+_ (Nat.+-comm (Graph.nnbors Gr g e1) 1) Eq.refl) ⟩
      1 +
      List.sum (List.map (Graph.nnbors Gr g) f) +
      (1 +
      (Graph.nnbors Gr g e1 +
      (List.sum (List.map (Graph.nnbors Gr g) m) +
      (Graph.nnbors Gr g e2 +
      List.sum (List.map (Graph.nnbors Gr gp) b)))))
    ≡⟨ Nat.+-assoc 1 (List.sum (List.map (Graph.nnbors Gr g) f)) (1 + (Graph.nnbors Gr g e1 + (List.sum (List.map (Graph.nnbors Gr g) m) + (Graph.nnbors Gr g e2 + List.sum (List.map (Graph.nnbors Gr gp) b))))) ⟩
      1 +
      (List.sum (List.map (Graph.nnbors Gr g) f) +
      (1 +
      (Graph.nnbors Gr g e1 +
      (List.sum (List.map (Graph.nnbors Gr g) m) +
      (Graph.nnbors Gr g e2 +
      List.sum (List.map (Graph.nnbors Gr gp) b))))))
    ≡⟨ Eq.cong₂ _+_ {1} Eq.refl (Nat.+-assoc (List.sum (List.map (Graph.nnbors Gr g) f)) 1 (Graph.nnbors Gr g e1 + (List.sum (List.map (Graph.nnbors Gr g) m) + (Graph.nnbors Gr g e2 + List.sum (List.map (Graph.nnbors Gr gp) b))))) ⟨
      1 +
      ((List.sum (List.map (Graph.nnbors Gr g) f) +
      1) +
      (Graph.nnbors Gr g e1 +
      (List.sum (List.map (Graph.nnbors Gr g) m) +
      (Graph.nnbors Gr g e2 +
      List.sum (List.map (Graph.nnbors Gr gp) b)))))
    ≡⟨ Eq.cong₂ _+_ {1} Eq.refl (Eq.cong₂ _+_ (Nat.+-comm (List.sum (List.map (Graph.nnbors Gr g) f)) 1) Eq.refl) ⟩
      1 +
      (1 +
      (List.sum (List.map (Graph.nnbors Gr g) f) +
      (Graph.nnbors Gr g e1 +
      (List.sum (List.map (Graph.nnbors Gr g) m) +
      (Graph.nnbors Gr g e2 +
      List.sum (List.map (Graph.nnbors Gr gp) b))))))
    ≡⟨⟩
      2 +
      (List.sum (List.map (Graph.nnbors Gr g) f) +
      (Graph.nnbors Gr g e1 +
      (List.sum (List.map (Graph.nnbors Gr g) m) +
      (Graph.nnbors Gr g e2 +
      List.sum (List.map (Graph.nnbors Gr gp) b)))))
    ≡⟨ Eq.cong₂ _+_ {2} Eq.refl (Eq.cong₂ _+_ {List.sum (List.map (Graph.nnbors Gr g) f)} Eq.refl (Eq.cong₂ _+_ {Graph.nnbors Gr g e1} Eq.refl (Eq.cong₂ _+_ {List.sum (List.map (Graph.nnbors Gr g) m)} Eq.refl (Eq.cong₂ _+_ {Graph.nnbors Gr g e2} Eq.refl ((Eq.cong List.sum (edgelist-addedge-adds-no-nbors' g {b} {u} {v} {nuv} {pu} {pv} {npuv} bu bv))))))) ⟩
      2 +
      (List.sum (List.map (Graph.nnbors Gr g) f) +
      (Graph.nnbors Gr g e1 +
      (List.sum (List.map (Graph.nnbors Gr g) m) +
      (Graph.nnbors Gr g e2 +
      List.sum (List.map (Graph.nnbors Gr g) b)))))
    ≡⟨ Eq.cong₂ _+_ {2} Eq.refl (Eq.cong₂ _+_ {List.sum (List.map (Graph.nnbors Gr g) f)} Eq.refl (Eq.cong₂ _+_ {Graph.nnbors Gr g e1} Eq.refl (Eq.cong₂ _+_ {List.sum (List.map (Graph.nnbors Gr g) m)} Eq.refl (Eq.cong₂ _+_ {Graph.nnbors Gr g e2} (Eq.trans Eq.refl (Nat.+-comm 0 (Graph.nnbors Gr g e2))) Eq.refl)))) ⟩
      2 +
      (List.sum (List.map (Graph.nnbors Gr g) f) +
      (Graph.nnbors Gr g e1 +
      (List.sum (List.map (Graph.nnbors Gr g) m) +
      (List.sum (List.map (Graph.nnbors Gr g) (e2 ∷ [])) +
      List.sum (List.map (Graph.nnbors Gr g) b)))))
    ≡⟨ Eq.cong₂ _+_ {2} Eq.refl (Eq.cong₂ _+_ {List.sum (List.map (Graph.nnbors Gr g) f)} Eq.refl (Eq.cong₂ _+_ {Graph.nnbors Gr g e1} Eq.refl (Eq.cong₂ _+_ {List.sum (List.map (Graph.nnbors Gr g) m)} Eq.refl (list-sum-split {List.map (Graph.nnbors Gr g) (e2 ∷ [])} {List.map (Graph.nnbors Gr g) b})))) ⟨
      2 +
      (List.sum (List.map (Graph.nnbors Gr g) f) +
      (Graph.nnbors Gr g e1 +
      (List.sum (List.map (Graph.nnbors Gr g) m) +
      List.sum (List.map (Graph.nnbors Gr g) (e2 ∷ []) ++ List.map (Graph.nnbors Gr g) b))))
    ≡⟨ Eq.cong₂ _+_ {2} Eq.refl (Eq.cong₂ _+_ {List.sum (List.map (Graph.nnbors Gr g) f)} Eq.refl (Eq.cong₂ _+_ {Graph.nnbors Gr g e1} Eq.refl (Eq.cong₂ _+_ {List.sum (List.map (Graph.nnbors Gr g) m)} Eq.refl (Eq.cong List.sum (list-map-split {ℕ} {ℕ} {e2 ∷ []} {b}))))) ⟨
      2 +
      (List.sum (List.map (Graph.nnbors Gr g) f) +
      (Graph.nnbors Gr g e1 +
      (List.sum (List.map (Graph.nnbors Gr g) m) +
      List.sum (List.map (Graph.nnbors Gr g) (e2 ∷ b)))))
    ≡⟨ Eq.cong₂ _+_ {2} Eq.refl (Eq.cong₂ _+_ {List.sum (List.map (Graph.nnbors Gr g) f)} Eq.refl (Eq.cong₂ _+_ {Graph.nnbors Gr g e1} Eq.refl (list-sum-split {List.map (Graph.nnbors Gr g) m}))) ⟨
      2 +
      (List.sum (List.map (Graph.nnbors Gr g) f) +
      (Graph.nnbors Gr g e1 +
      List.sum (List.map (Graph.nnbors Gr g) m ++ List.map (Graph.nnbors Gr g) (e2 ∷ b))))
    ≡⟨ Eq.cong₂ _+_ {2} Eq.refl (Eq.cong₂ _+_ {List.sum (List.map (Graph.nnbors Gr g) f)} Eq.refl (Eq.cong₂ _+_ {Graph.nnbors Gr g e1} Eq.refl (Eq.cong List.sum (list-map-split {ℕ} {ℕ} {m} {e2 ∷ b})))) ⟨
      2 +
      (List.sum (List.map (Graph.nnbors Gr g) f) +
      (Graph.nnbors Gr g e1 +
      List.sum (List.map (Graph.nnbors Gr g) (m ++ e2 ∷ b))))
    ≡⟨ Eq.cong₂ _+_ {2} Eq.refl (Eq.cong₂ _+_ {List.sum (List.map (Graph.nnbors Gr g) f)} Eq.refl (Eq.cong₂ _+_ {Graph.nnbors Gr g e1} (Eq.trans Eq.refl (Nat.+-comm 0 (Graph.nnbors Gr g e1))) Eq.refl)) ⟩
      2 +
      (List.sum (List.map (Graph.nnbors Gr g) f) +
      (List.sum (List.map (Graph.nnbors Gr g) (e1 ∷ [])) +
      List.sum (List.map (Graph.nnbors Gr g) (m ++ e2 ∷ b))))
    ≡⟨ Eq.cong₂ _+_ {2} Eq.refl (Eq.cong₂ _+_ {List.sum (List.map (Graph.nnbors Gr g) f)} Eq.refl (list-sum-split {List.map (Graph.nnbors Gr g) (e1 ∷ [])} {List.map (Graph.nnbors Gr g) (m ++ e2 ∷ b)})) ⟨
      2 +
      (List.sum (List.map (Graph.nnbors Gr g) f) +
      (List.sum (List.map (Graph.nnbors Gr g) (e1 ∷ []) ++ List.map (Graph.nnbors Gr g) (m ++ e2 ∷ b))))
    ≡⟨ Eq.cong₂ _+_ {2} Eq.refl (Eq.cong₂ _+_ {List.sum (List.map (Graph.nnbors Gr g) f)} Eq.refl (Eq.cong List.sum (list-map-split {ℕ} {ℕ} {e1 ∷ []} {m ++ e2 ∷ b}))) ⟨
      2 +
      (List.sum (List.map (Graph.nnbors Gr g) f) +
      (List.sum (List.map (Graph.nnbors Gr g) (e1 ∷ m ++ e2 ∷ b))))
    ≡⟨ Eq.cong₂ _+_ Eq.refl (list-sum-split {List.map (Graph.nnbors Gr g) f}) ⟨
      2 +
      (List.sum (List.map (Graph.nnbors Gr g) f ++ List.map (Graph.nnbors Gr g) (e1 ∷ m ++ e2 ∷ b)))
    ≡⟨ Eq.cong₂ _+_ Eq.refl (Eq.cong List.sum (list-map-split {ℕ} {ℕ} {f})) ⟨
      2 + List.sum (List.map (Graph.nnbors Gr g) (f ++ e1 ∷ m ++ e2 ∷ b))
    ≡⟨ Eq.cong₂ _+_ Eq.refl (Eq.cong List.sum (Eq.cong₂ List.map Eq.refl (Eq.sym eq))) ⟨
      2 + List.sum (List.map (Graph.nnbors Gr g) (UniqueList.l vs))
    ≡⟨ Eq.cong₂ _+_ Eq.refl (vec-map-sum≡list-map-sum {ℕ} {UniqueList.l vs}) ⟨
      2 + Vec.sum (Vec.map (Graph.nnbors Gr g) (Graph.nodes Gr g))
    ∎
```

Now we are done with the harder side of the handshake proof, and have
represented what happens to the sum of the degrees of the vertices when adding
a new edge.

Next, we prove that, when we add an edge, indeed the count of edges (`Graph.m`)
increases by 1. This is slightly complex, as `Graph.m` involves dividing by two,
and division is well-known for being difficult to deal with.

```agda
open import Data.Nat.DivMod as DivMod

addedge-adds-an-edge : ∀ {V G} (Gr : Graph V G) → (g : G) → Set
addedge-adds-an-edge Gr g = ∀ {u v nuv pu pv npuv} → Graph.m Gr (Graph.addedge Gr g (u , v) nuv pu pv npuv) ≡ 1 + Graph.m Gr g

-- The proof idea is somewhat simple: the length of the edge list becomes two
-- greater when adding an edge (one for (u , v), and one for (v , u)), and, in
-- this case, integer division distributes over addition.
-- In particular, integer division by `d` distributes over the addition of `a`
-- and `b` iff `a % d + b % d < d`. In this case, `a = d = 2`, so this becomes
-- `0 + b % d < d`, which is reflexively equal to `b % d < d`, which is true for
-- all `b`, `d` by properties of modulus.
-- It turns out, as we have proven, that `b` in this case (`List.length es`) is
-- also even, but we do not need this fact to push the proof through due to the
-- reasoning above.
edgelist-addedge-adds-an-edge : (g : Edgelist) → addedge-adds-an-edge edgelist-nat-graph g
edgelist-addedge-adds-an-edge (vs , es) {u} {v} {nuv} {pu} {pv} {npuv} =
    let g = (vs , es) in
    let Gr = edgelist-nat-graph in
    let (vs' , es') = Graph.addedge Gr g (u , v) nuv pu pv npuv in
    let open ≡-Reasoning in
    begin
      List.length es' / 2
    ≡⟨⟩
      (2 + List.length es) / 2
    ≡⟨ +-distrib-/ 2 (List.length es) dlemma ⟩
      1 + List.length es / 2
    ∎
    where
    dlemma : 2 % 2 + (List.length es) % 2 Data.Nat.< 2
    dlemma = m%n<n (List.length es) 2
```

And, finally, we put all the pieces together to prove the handshake lemma.

The empty case is handled via reflexivity. The addnode case relies on the proof
of edgelist-nonnode-no-edges (so, adding a new node does *not* add anything to
the sum of neighbours, because the newly-added vertex must have had no
neighbours prior to being added) and some deconstruction of the value.

Finally, the addedge case puts the pieces we developed above together:
1. It uses edgelist-addedge-adds-two-nbors to get the degree-sum in terms of the
   previous degree-sum.
2. It uses the IH to write the previous degree sum in terms of Graph.m
3. It uses the distributivity of multiplication over addition to 'factor out the
   2' and get `2 * (1 + Graph.m prev)`
4. It uses edgelist-addedge-adds-an-edge to relate `1 + Graph.m prev` to
   `Graph.m cur`, completing the proof!

Hence, the handshake lemma has been proved on edge list graphs by induction.

```agda
handshake : ∀ {V G} (Gr : Graph V G) → (g : G) → Set
handshake Gr g = Vec.sum (Vec.map (Graph.nnbors Gr g) (Graph.nodes Gr g)) ≡ 2 * Graph.m Gr g

edgelist-handshake : graph-induction edgelist-nat-graph handshake
edgelist-handshake empty-gcons = Eq.refl
edgelist-handshake {gp} (addnode-gcons {g} gc {v} {p}) =
                        let Gr = edgelist-nat-graph in
                        let open ≡-Reasoning in
                        begin
                        Vec.sum (Vec.map (Graph.nnbors Gr gp) (Graph.nodes Gr gp))
                        ≡⟨⟩
                        Vec.sum (Vec.map (Graph.nnbors Gr gp) (v Vec.∷ (Graph.nodes Gr g)))
                        ≡⟨⟩
                        Vec.sum ((Graph.nnbors Gr gp v) Vec.∷ Vec.map (Graph.nnbors Gr gp) (Graph.nodes Gr g))
                        ≡⟨⟩
                        (Graph.nnbors Gr gp v) + Vec.sum (Vec.map (Graph.nnbors Gr gp) (Graph.nodes Gr g))
                        ≡⟨⟩
                        (Graph.nnbors Gr gp v) + Vec.sum (Vec.map (Graph.nnbors Gr g) (Graph.nodes Gr g))
                        ≡⟨ Eq.cong₂ _+_ Eq.refl (edgelist-handshake gc) ⟩
                        (Graph.nnbors Gr gp v) + 2 * Graph.m Gr g
                        ≡⟨⟩
                        (Graph.nnbors Gr gp v) + 2 * Graph.m Gr g
                        ≡⟨⟩
                        (Graph.nnbors Gr g v) + 2 * Graph.m Gr g
                        ≡⟨ Eq.cong₂ _+_ (edgelist-nonnode-no-edges gc v p) Eq.refl ⟩
                        0 + 2 * Graph.m Gr g
                        ≡⟨⟩
                        2 * Graph.m Gr gp
                        ∎
edgelist-handshake {gp} (addedge-gcons {g} gc {u , v} {p1} {p2} {p3} {p4}) =
                        let Gr = edgelist-nat-graph in
                        let open ≡-Reasoning in
                        begin
                        Vec.sum (Vec.map (Graph.nnbors Gr gp) (Graph.nodes Gr gp))
                        ≡⟨⟩
                        Vec.sum (Vec.map (Graph.nnbors Gr gp) (Graph.nodes Gr g))
                        ≡⟨ edgelist-addedge-adds-two-nbors g {u} {v} {p1} {p2} {p3} {p4} ⟩
                        2 + Vec.sum (Vec.map (Graph.nnbors Gr g) (Graph.nodes Gr g))
                        ≡⟨ Eq.cong₂ _+_ Eq.refl (edgelist-handshake gc) ⟩
                        2 + 2 * Graph.m Gr g
                        ≡⟨⟩
                        2 * 1 + 2 * Graph.m Gr g
                        ≡⟨ Nat.*-distribˡ-+ 2 1 (Graph.m Gr g) ⟨
                        2 * (1 + Graph.m Gr g)
                        ≡⟨ Eq.cong₂ _*_ {2} Eq.refl (edgelist-addedge-adds-an-edge g {u} {v} {p1} {p2} {p3} {p4}) ⟨
                        2 * Graph.m Gr gp
                        ∎
```
   