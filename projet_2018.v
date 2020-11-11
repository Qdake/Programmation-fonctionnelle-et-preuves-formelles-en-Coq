Require Import String.
Require Import ZArith.

(* type: nat or string *)
Inductive nos :=    
  | Nos_nat (n:nat)
  | Nos_string (s:string).
Definition dict : Set := nos -> option nos.

Definition empty_dict : dict := fun (n : nos) => None. 
Check empty_dict.

Open Scope string_scope.
Definition add_dict : string -> nat -> dict -> dict :=
  fun (s : string) (n : nat) (mydict : dict) =>
    (* le resultat est un dictionnaire, i.e. est une fonction de string dans nat*)
    fun (key' : nos) => 
      match key' with 
      |Nos_nat n' => if (n' =? n)%nat then Some (Nos_string s)
                     else mydict (Nos_nat n')
      |Nos_string s' => if (s' =? s)%string then Some (Nos_nat n)
                        else mydict (Nos_string s')
      end.

Definition assoc1_1 : string -> dict -> option nat := 
  fun (key : string) (mydict : dict) => 
    match mydict (Nos_string key) with
    |None => None%nat 
    |Some (Nos_nat n) => Some n
    |_=>None
    end.


Definition assoc2_1 : nat -> dict -> option string := 
  fun (key : nat) (mydict : dict) => 
    match mydict (Nos_nat key) with
    |None => None%string 
    |Some (Nos_string s) => Some s 
    |_=>None%string
    end.
