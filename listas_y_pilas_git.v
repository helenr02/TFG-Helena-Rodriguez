(*LISTAS*)

(*Primer ejemplo de listas de naturales*)
Inductive ListaNat : Type :=
  |nil : ListaNat
  |cons : nat -> ListaNat -> ListaNat.

(*Abrimos un módulo Listas donde se definen las listas de cualquier tipo de dato A, funciones y  propiedades que se cumplen*)
Module Listas.

(*Defino las listas dando explícitamente el tipo de dato de los elementos que la forman. Es un tipo de estructura
inductiva.*)
Inductive lista (A : Type) : Type :=
  |nil : lista A
  |cons : A -> lista A -> lista A.


(*Con esto no hace falta especificar cada vez que se use nil A y cons A el tipo A al que se están aplicando, 
y Coq lo infiere de forma automática*)
Arguments nil {A}.
Arguments cons {A} _ _.


Notation "[]" := nil.
Notation "[ x ]" := (cons x nil).   
Notation "[ x ; y ; .. ; z ]" := (cons x (cons y .. (cons z nil) .. )).
Notation "x :: xs" := (cons x xs).


(*Funciones con listas--------------------------------------------------------------------------------------------*)

(*Hay que darle un valor por defecto cuando hacemos head de la lista vacía*)
Definition head {A : Type} (default : A) (l : lista A) : A :=
  match l with 
  |[]  => default
  |x :: _ => x
  end.

Compute head 0 [2;3].
Compute head 0 [2].
Compute head 0 [].

Definition tail {A : Type} (l : lista A) : lista A :=
  match l with 
  |[] => []
  |_ :: xs => xs
  end.

Compute tail [2;3;4].
Compute tail [].

Fixpoint concatenar {A : Type} (l m : lista A) {struct l}: lista A :=
  match l with
  |[] => m
  |x :: xs => x :: (concatenar xs m)
  end.

Compute concatenar [1;2] [3;4].
Compute concatenar [] [1].
Compute concatenar [] [2;3].
Compute concatenar [1;2;3] [].
Compute concatenar (4::[2]) [5;3].

Notation "m ++ l" := (concatenar m l).

Compute [1;2] ++ [3;4].
Compute  [] ++ [1].
Compute [] ++ [].
Compute  [] ++ [2;3].
Compute  [1;2;3] ++ [].

(*Por ser una función recursiva, uso Fixpoint. Podríamos poner en el segundo caso 1 + len xs, pero por seguir con la 
notación de los números naturales de Coq, ponemos el constructor S. *)
Fixpoint len {A : Type} (l : lista A) : nat :=
  match l with
  |[] => 0
  |x::xs => S(len xs)
  end.

Compute len [].
Compute len [2;34].

Fixpoint inversa {A : Type} (l : lista A) : lista A :=
  match l with 
  |[] => []
  |x :: xs => inversa xs ++ [x]
  end.

Compute inversa [1;2;3].
Compute inversa [].

(*Obs: indexamos las listas comenzando en 0*)
Fixpoint nthOpcional {A : Type} (l : lista A)(n : nat) : option A :=
  match n, l with 
  |_, [] => None
  |O, x::xs => Some x
  |S n', x::xs => nthOpcional xs n'
  end.
Print option.

Fixpoint nthOpcional' {A : Type} (n : nat)(l : lista A): option A :=
  match l with
  |[] => None
  |x::xs => match n with
            |O => Some x
            |S n' => nthOpcional' n' xs
            end
  end.
Print option.

Compute nthOpcional [4;5;6;7] 0.
Compute nthOpcional [4;5;6;7] 1.
Compute nthOpcional [4;5;6;7] 4.
Compute nthOpcional [] 1.

Fixpoint In {A :Type} (x : A) (l : lista A) : Prop :=
  match l with 
  |[] => False
  |x'::xs => x' = x \/ In x xs
  end.

Check In.  (*A -> lista A -> Prop*)
Compute In 4 [4;3]. (* = 4 = 4 \/ 3 = 4 \/ False*)

Fixpoint map {A B : Type} (f : A->B) (l : lista A) : lista B :=
  match l with 
  |[] => []
  |x::xs => (f x)::map f xs
  end.

Fixpoint All {A : Type} (P : A -> Prop) (l : lista A) : Prop :=
  match l with 
  |[] => True 
  |x::xs => (P x) /\ (All P xs)
  end.

(*Demostraciones de las propiedades----------------------------------------------------------------------------------*)

Lemma head_nil : forall (A:Type) (x:A), head x [] = x.
Proof. intros. simpl. reflexivity. Qed.

Lemma head_cons : forall (A : Type) (x y : A) (l : lista A) , head y (x :: l) = x.  
Proof. intros. simpl. reflexivity. Qed.

(*Si no pongo el @, Coq no sabe de inferir el tipo A de [] y de tail como antes, ya que no tiene contexto.
Al poner el @ obligamos a poner el tipo A de forma explícita y así Coq entiende que tanto [] como tail se aplican
al tipo A*)
Lemma tail_nil : forall (A : Type), @tail A [] = [].
Proof. intros. simpl. reflexivity. Qed.

Lemma tail_cons : forall (A : Type) (x : A) (l : lista A), tail (x :: l) = l.
Proof. intros. simpl. reflexivity. Qed.

Lemma nil_concat : forall (A : Type) (l : lista A), [] ++ l = l.
Proof. intros. simpl. reflexivity. Qed.

Lemma concat_nil : forall (A : Type) (l : lista A), l ++ [] = l.
Proof. intros. induction l.
- simpl. reflexivity.
- simpl. rewrite IHl. reflexivity.
Qed.

Lemma cons_concat : forall (A : Type) (x : A) (m l : lista A), (x :: m) ++ l = x :: (m ++ l).
Proof. intros. simpl. reflexivity. Qed.

Lemma concat_asoc : forall (A : Type) (m l t : lista A), m ++ (l ++ t) = (m ++ l) ++ t.
Proof. intros. induction m.
- simpl. reflexivity.
 -simpl. rewrite IHm. reflexivity.
Qed.

Lemma len_nil : forall (A : Type), @len A [] = 0.
Proof. intro. simpl. reflexivity. Qed.

Lemma len_cons : forall (A : Type) (x : A) (m : lista A), len (x :: m) = 1 + len m.
Proof. intros. simpl. reflexivity. Qed.

Lemma len_concat : forall (A : Type) (m l : lista A), len (m ++ l) = len m + len l.
Proof. 
intros. induction m.
- simpl. reflexivity.
- simpl. rewrite IHm. reflexivity.
Qed.

Print Nat.pred. (*Restar 1
Nat.pred = fun n : nat => match n with
                          | 0 => n
                          | S u => u
                          end
          : nat -> nat*)
Lemma resto_len_pred : forall (A : Type) (m : lista A), pred (len m)  = len (tail m).
Proof. intros. induction m.
- simpl. reflexivity.
- simpl. reflexivity.
Qed.

Lemma len_inversa : forall (A : Type) (m : lista A), len (inversa m) = len m.
Proof. intros. induction m.
- simpl. reflexivity.
- simpl. rewrite <- IHm. rewrite len_concat. simpl. 
  assert (H : forall (n : nat), n + 1 = S n).
  { intro. induction n.
    *simpl. reflexivity.
    *simpl. rewrite IHn. reflexivity. }
  rewrite H. reflexivity.
Qed.

Check len_inversa.
Print len_inversa. 

Theorem In_map : forall (A B : Type) (f : A -> B) (l : lista A) (x : A), In x l -> In (f x) (map f l).
Proof. intros. induction l.
- simpl. contradiction.
- simpl. destruct H.
  * left. rewrite H. reflexivity. 
  * right. apply IHl. assumption.
Qed.

Theorem In_map_iff : forall (A B : Type) (f : A -> B) (l : lista A) (y : B), In y (map f l) <-> exists x, f x = y /\ In x l.
Proof. intros. split.
- intro. induction l.
  { simpl. contradiction. }
  { simpl. destruct H.
    + exists a. split.
      * assumption.
      * left. reflexivity.
    + apply IHl in H. destruct H. exists x. split.
      * destruct H. assumption.
      * right. destruct H. assumption. }
- intro. induction l. 
  { simpl. destruct H. destruct H. apply H0. }
  { simpl. destruct H. destruct H. destruct H0. (*no elegir tan pronto en el objetivo right o left, primero destruir los casos de las hipótesis*)
    + rewrite H0. left. assumption.
    + right. apply IHl. exists x. split.  
      *assumption.
      *assumption. }
Qed.

Theorem All_In : forall A (P : A -> Prop) (l : lista A), (forall x, In x l -> P x) <-> All P l.
Proof. intros. split.
- intros. induction l.
  * simpl. exact I.
  * simpl. split.
    + specialize H with (x := a). apply H. simpl. left. reflexivity.
    + apply IHl. intros. specialize H with (x:=x). apply H. simpl. right. assumption.
-intro. induction l.
  *intros. exfalso. apply H0.
  * simpl. intros. destruct H0.
    +rewrite <- H0. apply H.
    + apply IHl.
      {destruct H. assumption. }
      {assumption. }
Qed.

Theorem in_not_nil : forall (A : Type) (x : A) (l : lista A), In x l -> l <> [].
Proof. intros. intro.
  rewrite H0 in H.
  simpl in H.
  assumption.
Qed.

Lemma len_0_vacia : forall (A : Type) (l : lista A), len l = 0 -> l = [].
Proof. intros. induction l.
  - reflexivity.
  - simpl in H.  discriminate.
Qed.

Lemma nth : forall (A : Type) (n : nat) (l : lista A), n >= len l -> nthOpcional' n l = None.
Proof. intros A. induction n. 
  - intros. induction l. 
    + reflexivity. 
    + simpl in H. Require Import Lia. lia. 
  - intros. induction l. 
    + simpl. reflexivity.
    + simpl. apply IHn. simpl in H. lia.
Qed.


Require Import Extraction.
Extraction Language Haskell.
Extract Inductive bool => "Bool" [ "True" "False" ].
Extract Inductive option => "Maybe" [ "Just" "Nothing" ].
Extract Inductive nat =>
  Int [ "0" "succ" ] "(\\fO fS n -> if n == 0 then fO () else fS (n - 1))".
Extract Inlined Constant Init.Nat.mul => "(*)".
End Listas.
Extraction "C:/Users/Helena/Desktop/UNI/Coq_bueno/extracciones/mislitas.hs" Listas.


(*=================================================================================================================
  =================================================================================================================*)

(*PILAS*)

Module MiPila.
Export Listas.

(*Definimos las pilas como listas. Se comportan como datos inductivos, pero no se definen con la misma estructura.*)
Definition pila (A : Type) := lista A.
Check pila.
Print pila.

(*Definimos por así decirlo el constructor de la pila vacía*)
Definition vacia {A :Type} : pila A := [].

Definition es_vacia {A : Type} (p : pila A) : bool :=
  match p with 
  |[] => true
  |_ => false
  end.

Compute es_vacia [2;3].
Compute es_vacia [].

(*Añadir elemento a la pila*)
Definition push {A : Type} (x : A) (p : pila A) : pila A := x :: p.

(*Introducimos el tipo option que me deja devolver None cuando haga top de la pila []. Cuando sí que
haya elementos, devolveré Some x*)
Definition top {A : Type} (p : pila A) : option A :=
  match p with 
  |[] => None
  |x::xs => Some x
  end.


Definition pop {A : Type} (p : pila A) : option (pila A) :=
  match p with 
  |[] => None
  |_::xs => Some xs
  end.

Definition tam {A : Type} (p : pila A) : nat := 
  len p.

(*Demostracion de las propiedades-----------------------------------------------------------------------------------*)

Lemma vacia_es_vacia : forall (A : Type), es_vacia (@vacia A) = true.
Proof. intro. simpl. reflexivity. Qed.

Check vacia_es_vacia.
Print vacia_es_vacia.

Lemma push_no_vacia : forall (A : Type) (x : A) (p : pila A), es_vacia (push x p) = false.
Proof.  intros. simpl. reflexivity. Qed.

Lemma top_vacia : forall(A : Type) , top (@vacia A) = None.
Proof. intro. simpl. reflexivity. Qed.

Lemma top_push : forall (A : Type) (x : A) (p : pila A), top (push x p) = Some x.
Proof. intros. simpl. reflexivity. Qed.

Lemma pop_vacia : forall (A : Type), pop (@vacia A) = None.
Proof. intro. simpl. reflexivity. Qed.

Lemma pop_push : forall (A : Type) (x : A) (p : pila A), pop (push x p) = Some p.
Proof. intros. simpl. reflexivity. Qed.

Lemma tam_vacia : forall (A : Type) , tam (@vacia A) = 0.
Proof. intros. simpl. reflexivity. Qed.

Lemma tam_push :  forall (A : Type) (x : A) (p : pila A), tam (push x p) = 1 + tam p.
Proof. intros. simpl. reflexivity. Qed.

End MiPila.

Require Import Extraction.
Extraction Language OCaml.
Extract Inductive bool => "bool" [ "true" "false" ].
Extract Inductive option => "option" [ "Some" "None" ].
Extract Inductive lista => "list" [ "[]" "(::)" ].
Extract Inlined Constant length => "List.length".
Extraction "C:/Users/Helena/Desktop/UNI/Coq_bueno/extracciones/miPila.ml" MiPila.

Extraction Language Haskell.
Extraction "C:/Users/Helena/Desktop/UNI/Coq_bueno/extracciones/miPila.hs" MiPila.
