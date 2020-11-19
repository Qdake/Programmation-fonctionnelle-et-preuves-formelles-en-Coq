Require Import Bool Arith List Nat.
Import ListNotations.

Print nat_rect.
Check nat_rect.

Inductive ord :=
|zero : ord
|succ : ord -> ord
|lim : (nat -> ord) -> ord.

Print nat.

Print list.

(*****************)
Set Implicit Arguments.
(*****************)

Fixpoint length {X} (l:list X) :=
  match l with
  | [] => 0
  | _::l => S (length l)
  end.

Check length [1;2;3].
Check length.
Check @length.
Fixpoint concatenation {X} (l1 l2 : list X) :=
  match l1 with 
  | [] => l2
  | x::l => x::(concatenation l l2)
  end.

Compute concatenation [1;2;3] [4;5;6].

Fixpoint retournement_aux {X} (lo lr:list X) :=
  match lo with
  |[] => lr
  |x::l => retournement_aux l (x::lr)
  end.
Definition retournement {X} (l:list X) := retournement_aux l [].

Check @retournement.

Fixpoint map {X Y} (f:X->Y) (l : list X) : list Y :=
  match l with 
  |[] => []
  |x::l => (f x) :: (map f l)
  end.

Compute map S [1;2;3;4].

Fixpoint filter {X} (f : X->bool) (l : list X) : list X := 
  match l with  
  | [] => []
  | x::l => if (f x) then x :: (filter f l)
                     else filter f l
  end.          

Fixpoint even (x:nat) : bool :=
  match x with
  | 0 => true
  | 1 => false
  | S (S n) => even n
  end.

Compute filter even [1;2;3;4;5].

Fixpoint fold_right {A B} (f:B->A->A) (a:A) (l:list B) : A :=
  match l with
  | [] => a
  | x::l => f x (fold_right f a l)
  end.

Fixpoint fold_left {A B} (f:B->A->A) (a:A) (l:list B) : A :=
  match l with
  | [] => a
  | x::l =>fold_left f (f x a) l
  end.

Fixpoint seq_aux (a n:nat) (res:list nat) :=
  match n with
  | 0 => res
  | S n => seq_aux a n ((a+n)::res)
  end.

Definition seq (a n:nat) : list nat := seq_aux a (n+1) [].

Compute seq 3 7.

Definition head {X} (l:list X) : option X :=
  match l with
  | [] => None 
  | x::_ => Some x
  end.

Compute head [1;2;3].
Compute List.hd [1;2;3].
Compute List.rev [1;2;3].

Definition last {X} (l:list X) : option X := 
  match l with
  | [] => None
  | x::l => head (List.rev (x::l))
  end.

Compute last [1;2;3].
Compute last [].

Fixpoint nth {X} (l:list X) (n:nat): option X := 
  match l with
  |[] => None
  |x::l => if n=?1 then Some x
                   else nth l (n-1)
  end.

Compute nth [1;2;3;4] 2.
Compute nth [] 5. 
Compute nth [1;2;3] 6. 

Print seq.
Print List.hd.

Definition head_default_value {A} (l : list A) (dft:A) : A :=
  match l with
  |[] => dft
  |x::_ => x
  end.


Print nat.
Definition forallb {A} (f:A->bool) (l:list A):bool:=
  match l with 
  | [] => true
  | x::q => f x && forallb f q
  end.

Fixpoint increasing l:=
  match l with
  | [] => true
  | [x] => true
  | x::((y::_) as q) => (x <? y) && increasing q
  end.

Compute increasing [1;2;2].

Fixpoint forall_succesive {A} (f:A->A->bool) l := 
  match l with 
  | [] => true 
  | [x] => true
  | x::(y::_ as q) => f x y && forall_succesive f q 
  end.

Definition increasing2 := forall_succesive Nat.ltb.
(* where Nat.ltb is the function behind the <? test *)

Definition delta k l := forall_succesive (fun a b => a+k <=? b) l.


Check prod (list nat) (list nat).


(* merge sort*)
Fixpoint split_aux {A} (l1 l2:list A) (n:nat) {struct n}: (list A)*(list A) :=
  match n with
  | 0 => (l1,l2)
  | S n => match l1 with
           |[] => (l1,l2) (* impossible*)
           |x::l => split_aux l (x::l2) n
           end
  end.
Compute div 5 2.
Definition split (l:list nat) := split_aux l [] (div (List.length l) 2).
  
Compute split [1;2;3;4;5].
Compute split [1].

Check List.app.

(* < *)
Fixpoint merge_aux (l1 l2 l: list nat) (n:nat) {struct n} := 
  match n with
  | 0 => List.rev l
  | S n => match l1,l2 with
           |[],_ => List.rev (List.app (List.rev l2) l)
           |_,[] => List.rev (List.app (List.rev l1) l)
           |x::l1',y::l2' => if y <? x then merge_aux (x::l1') l2' (y::l) n
                                       else merge_aux l1' (y::l2') (x::l) n
           end
  end.

Compute merge_aux [1] [2] [] 2.
Definition merge l1 l2 := merge_aux l1 l2 [] ((List.length l1) + (List.length l2)).

Compute merge [1;2;6;9;23] [1;2;3;5;8;9;14;30].

Fixpoint tri_mergesort (l:list nat) (n:nat):=
  match n with
  | 0 => l
  | S n => match l with
           | [] => []
           | [x] => [x]
           | _ =>
            let '(l1,l2):=(split l) in
                merge (tri_mergesort l1 n) (tri_mergesort l2 n)
            end
  end.

Definition mergesort (l:list nat) := tri_mergesort l (List.length l).


Compute mergesort [1;2].
Compute mergesort [2;1].
Compute split [1;2].
Compute merge [2] [1].
Compute merge [1] [2].

Compute mergesort [1;7;2;3;10;0;3].


(** Exercice 4 : powerset **)

Fixpoint powerset {A} (l:list A) : list (list A) := 
  match l with
  | [] => [[]]
  | x::q => 
      let ll := powerset q in
      ( map (fun l => x::l) ll) ++ ll
  end.

Compute powerset [1;2;3].



