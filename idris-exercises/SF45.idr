data Id : Type where
    MkId : Nat -> Id

beq_id : (x1, x2 : Id) -> Bool
beq_id (MkId n1) (MkId n2) = n1 == n2

beq_id_refl : (x : Id) -> True = beq_id x x
beq_id_refl (MkId Z) = Refl
beq_id_refl (MkId (S k)) = rewrite beq_id_refl (MkId k) in Refl

data PartialMap : Type where
    Empty : PartialMap
    Record : Id -> Nat -> PartialMap -> PartialMap

update : (d : PartialMap) -> (x : Id) -> (value : Nat) -> PartialMap
update d x value = Record x value d

find : (x : Id) -> (d : PartialMap) -> Maybe Nat
find x Empty = Nothing
find x (Record y v d') =
    if beq_id x y
        then Just v
        else find x d'

update_eq : (d : PartialMap) -> (x : Id) -> (v : Nat) -> find x (update d x v) = Just v
update_eq d x v = rewrite sym $ beq_id_refl x in Refl

update_neq : (d : PartialMap) -> (x, y : Id) -> (o : Nat) -> beq_id x y = False -> find x (update d y o) = find x d
update_neq d x y o prf = rewrite prf in Refl

data Baz : Type where
    Baz1 : Baz -> Baz
    Baz2 : Baz -> Bool -> Baz
