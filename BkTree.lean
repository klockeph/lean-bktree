import Lean

-- TODO: use a predefined metric class.
class metric (α : Type _) :=
(distance : α → α → Nat)

instance int_metric : metric Int where
  distance x y := Int.natAbs (x-y)

partial def levenshtein (x : List α) (y : List α) [BEq α] : Nat :=
  match (x, y) with
  | ([],[]) => 0
  | ([],y) => y.length
  | (x,[]) => x.length
  | ((x::xs),(y::ys)) => if x == y then levenshtein xs ys
  else 1 + min3 (levenshtein xs (y::ys)) (levenshtein (x::xs) ys) (levenshtein xs ys)
where min3 (a : Nat) (b : Nat) (c : Nat) : Nat := min (min a b) c
-- TODO: prove termination and remove `partial`.

instance levenshtein_metric {α: Type} [BEq α] : metric (List α) where
  distance x y := levenshtein x y

-- TODO: change from AssocList to RBMap for efficiency. 
-- But doesn't matter too much until RBMap has split.
inductive BkTree (β : Type _) (d : metric β) where
| leaf
| node (value : β) (children : (Lean.AssocList Nat (BkTree β d)))
deriving Inhabited

def BkTree.size (t : BkTree β d) : Nat :=
  match t with
  | leaf => 0
  | node _ ts => foldl 1 ts
where foldl : Nat → Lean.AssocList Nat (BkTree β d) → Nat
      | n, Lean.AssocList.nil => n
      | n, Lean.AssocList.cons _ v t => foldl (n + v.size) t

def BkTree.toList (t : BkTree β d) : List β :=
  match t with
  | leaf => []
  | node v c => v::foldl [] c
where foldl : List β → Lean.AssocList Nat (BkTree β d) → List β
      | n, Lean.AssocList.nil => n
      | n, Lean.AssocList.cons _ v t => foldl (n ++ v.toList) t

-- TODO: prove e.g. that `t.toList.length == t.size`

instance [Repr β]: Repr (BkTree β d) where
  reprPrec t p := "BkTree of " ++ reprPrec t.toList p

def BkTree.empty : BkTree β d :=
  BkTree.leaf

def BkTree.singleton (v : β) : BkTree β d :=
  BkTree.node v Lean.AssocList.nil

-- inserts a new element into a bk tree
partial def BkTree.insert (t : BkTree β d) (v : β) : BkTree β d :=
  match t with
  | leaf => singleton v
  | node val cs => 
    let dist := d.distance v val;
    if dist == 0 then (node val cs) 
    else match cs.find? dist with
    | none => node val (cs.insert dist (singleton v))
    | some c => node val (cs.replace dist (c.insert v))
-- TODO: prove termination and remove `partial`.

-- checks if the BkTree contains an element
partial def BkTree.contains (t : BkTree β d) (v : β) : Bool :=
  match t with
  | leaf => false
  | node val cs =>
    let dist := d.distance v val;
    if dist == 0 then true
    else match cs.find? dist with
    | none => false
    | some c => c.contains v
-- TODO: prove termination and remove `partial`.

-- Returns a new AssocList that contains all elements with keys between min and max.
-- TODO: generalize to work with any key [k : LE] instead of Nat. Gave a Prop instead of a Bool though..
-- Would be more efficient if RBMap had .split but I think it doesn't.
def Lean.AssocList.narrow (l : Lean.AssocList Nat c) (min: Nat) (max: Nat) : (Lean.AssocList Nat c) :=
  match l with
  | Lean.AssocList.nil => Lean.AssocList.nil
  | Lean.AssocList.cons x y ls => if (min <= x) && (x <= max) then Lean.AssocList.cons x y (ls.narrow min max) else (ls.narrow min max)

-- Find all elements that are at most `dist` away from `v`.
partial def BkTree.near (t : BkTree β d) (dist : Nat) (v : β) : (List β) :=
  match t with
  | leaf => []
  | node val cs => 
  let d := d.distance v val;
  let sublist := cs.narrow (d-dist-1) (d+dist+1);
  let subtrees := sublist.toList.map Prod.snd;
  let rest := subtrees.foldl (fun x y => x ++ y.near dist v) []
  if (d <= dist) then val::rest else rest
-- TODO: prove termination and remove `partial`.

partial def findClosest (v : β) (candidate : (β × Nat)) (t : BkTree β d) : (β × Nat) :=
  match t with
  | BkTree.leaf => candidate
  | BkTree.node val cs => 
    let dist := d.distance v val;
    let new_cand := if dist >= candidate.snd then candidate else (val, dist);
    let sublist := cs.narrow (candidate.snd - dist - 1) (candidate.snd + dist + 1);
    let subtrees := sublist.toList.map Prod.snd
  subtrees.foldl (findClosest v) new_cand
-- TODO: prove termination and remove `partial`.

-- Returns the closest element to a given value.
def BkTree.closest? (t : BkTree β d) (v : β) : Option (β × Nat) :=
  match t with
  | leaf => none
  | node val _ => some (findClosest v (val, d.distance v val) t)
-- TODO: Figure out how to view a String as a char array instead of explicitly doing O(n) conversion?
instance lev_string : metric String where
  distance x y := levenshtein (x.toList) (y.toList)


-- #check (BkTree.leaf : (BkTree Int int_metric))
-- #eval ((BkTree.leaf.insert 3).insert 1 : (BkTree Int int_metric)).closest? 2

-- abbrev example_tree : (BkTree String lev_string) := 
--   (BkTree.leaf.insert "cat"
--             |>.insert "dog"
--             |>.insert "house")

-- #eval example_tree.toList
-- #eval example_tree.near 4 "mouse"
-- #eval example_tree.closest? "mouse"
