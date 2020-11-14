Require Import Ascii String Nat List.
Open Scope nat_scope.
Open Scope string_scope.
Import ListNotations.
Inductive t: Set:=
  |ess : t
  |fdsfsd (a:t).

Inductive dict : Set := 
  | empty_dict : dict
  | add_dict (s:string) (n:nat) (d : dict): dict.
Check dict.
Check empty_dict.

Open Scope string_scope.
Fixpoint assoc1 (key: string) (mydict: dict) : option nat:= 
  match mydict with
  |empty_dict => None
  |add_dict s v d => match s =? key with
                     |true => Some v
                     |false => assoc1 key d
                    end
  end.

Open Scope nat_scope.
Fixpoint assoc2 (key: nat) (mydict: dict) : option string := 
  match mydict with
  |empty_dict => None%string
  |add_dict s v d => match key =? v with
                     |true => Some s
                     |false => assoc2 key d
                    end
  end.
(* Les dictionnaires seront bijectifs, c’est-`a-dire qu’une chaˆıne ou un nombre n’y apparaˆıt qu’au plus une fois.*)
Fixpoint is_bijectif (mydict : dict) : bool :=
  match mydict with
  |empty_dict => true
  |add_dict s v mydict' => match (assoc1 s mydict', assoc2 v mydict') with
                           | (None, None) => is_bijectif mydict'
                           | _ => false
                           end
  end.

Open Scope char_scope.
Fixpoint cons_init_dict (m : nat) := 
  match m with
  |0 => add_dict (String (ascii_of_nat m) EmptyString) m empty_dict
  |S m => add_dict (String (ascii_of_nat m) EmptyString) m (cons_init_dict m)
  end.


Definition init_dict := cons_init_dict 256.
Check init_dict.

(* Les dictionnaires contiendront des associations pour au moins toutes les chaˆınes de taille 1 (c.`a.d les
caract`eres) *)
Fixpoint contain_str_len_1_aux (m:nat) (mydict : dict) := 
  match m with
  |0 => match assoc1 (String (ascii_of_nat m) EmptyString) mydict with
        |Some _ => true
        |None   => false
        end
  |S m => match assoc1 (String (ascii_of_nat m) EmptyString) mydict with
          |Some _ => contain_str_len_1_aux m mydict
          |None   => false
          end
  end.
Definition contain_str_len_1 (mydict : dict) : bool := 
  contain_str_len_1_aux 256 mydict.

(* les nombres pr ́esents rempliront exactement tout un intervalle entre 0 inclus et un certain
nombre max exclus. *)

Fixpoint list_nb_contained (mydict : dict) : list nat :=
  match mydict with
  | empty_dict => nil
  | add_dict _ v mydict => cons v (list_nb_contained mydict)
  end.
Fixpoint max_list_nat (l : list nat) : nat :=
  match l with
  |nil => 0
  |cons n l => max n (max_list_nat l)
  end.

Open Scope nat.
Definition contain_an_interval (mydict : dict) : bool :=
  let l := list_nb_contained mydict 
  in max_list_nat l =? (List.length l)-2.

Compute list_nb_contained init_dict.
Compute List.length (list_nb_contained init_dict).
Compute contain_an_interval init_dict.