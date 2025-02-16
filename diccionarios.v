(*DICCIONARIOS*)

Inductive id : Type :=
  |Id : nat -> id.

Check Nat.eqb. (*nat -> nat -> bool*)
Print Nat.eqb.

Definition iguales_id (d1 d2 : id) : bool :=
  match d1, d2 with 
  |Id m1, Id m2 => Nat.eqb m1 m2
  end.

Compute (iguales_id (Id 3) (Id 3)).
Compute (iguales_id (Id 3) (Id 4)).

Theorem eqb_id_refl : forall x, iguales_id x x = true.
Proof. intro. destruct x. simpl. induction n.
- simpl. reflexivity.
- simpl. rewrite IHn. reflexivity.
Qed.

Module Diccionario.
Export Listas. (*estoy importando el módulo ListaNat para poder usarlo aquí, y además, si yo en otro sitio hago 
Import Diccionario, tendré disponible tanto lo que definna en este módulo como lo que tenga en ListaNat*)

Inductive diccionario : Type :=
  |vacio : diccionario
  |registro : id -> nat -> diccionario -> diccionario.

Definition dic1 := vacio.
Definition dic2 := registro (Id 3) 6 vacio.
Definition dic3 := registro (Id 2) 4 dic2.

Fixpoint valor (x : id) (dic : diccionario) : option nat :=
  match dic with 
  |vacio => None 
  |registro m n dic' => match iguales_id x m with
                        |true => Some n
                        |false => valor x dic'
                        end
  end.  

Compute (valor (Id 2) dic3).
Compute (valor (Id 2) dic2).

Fixpoint actualizar (dic : diccionario) (x : id) (n : nat) : diccionario :=
  match dic with 
  |vacio => registro x n vacio
  |registro y m dic' => match iguales_id x y with 
                        |true => registro x n dic'
                        |false => registro y m (actualizar dic' x n)
                        end
  end.

Compute actualizar dic3 (Id 2) 3.

Fixpoint encontrar  (x : id) (dic : diccionario) : option nat :=
  match dic with 
  |vacio => None
  |registro y m dic' =>  match iguales_id x y with 
                        |true => Some m
                        |false => encontrar x dic'
                        end
  end.

Compute encontrar (Id 2) dic3.

Definition update (dic : diccionario) (x : id) (value : nat): diccionario :=
  registro x value dic.

Theorem update_neq : forall (dic : diccionario) (x y : id) (n: nat),
    iguales_id x y = false -> encontrar x (update dic y n) = encontrar x dic.
Proof. intros. induction dic.
  - simpl. rewrite H. reflexivity.
  - simpl. rewrite H. reflexivity.
Qed. 
  

End Diccionario.
Check (forall n m : nat, n + m = m + n). (*Prop*)
Check 2 + 4 = 4 + 2. (*Prop*)

Definition es_par (n : nat) : bool :=
  match n mod 2 with
  | 0 => true
  | _ => false
  end.
Definition clasifica_num (n : nat) : string :=
  match es_par n with
  | true => "par"
  | false => "impar"
  end.