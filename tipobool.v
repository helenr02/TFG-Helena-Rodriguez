(*BOOLEANOS*)

Inductive bool : Set :=
  |true : bool
  |false : bool.

Definition and (a b : bool) : bool :=
  match a, b with 
    |true, true => true
    |_, _ => false
  end.

Notation "x && y" := (and x y).

Compute true && false.
Compute true && true.
Compute false && false.
Compute false && true.

Lemma and_idem : forall a : bool, a && a = a.
Proof. intro. destruct a.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

Lemma and_idem' : forall a : bool, a && a = a.
Proof. intro. destruct a; simpl; reflexivity.
Qed.

Lemma and_conm : forall (a b : bool), a && b = b && a.
Proof. intros. destruct a.
  -destruct b.
    * simpl. reflexivity.
    * simpl. reflexivity. 
  -destruct b.
    * simpl. reflexivity.
    * simpl. reflexivity.
Qed. 

Lemma and_conm' : forall (a b : bool), a && b = b && a.
Proof. intros. destruct a.
  - destruct b; simpl; reflexivity.
  - destruct b; simpl; reflexivity.
Qed.

Lemma and_asoc : forall (a b c: bool), (a && b) && c = a && (b && c).
Proof. intros. destruct a.
  - destruct b; destruct c; simpl; reflexivity.
  - destruct b; destruct c; simpl; reflexivity.
Qed.

Definition or (a b : bool) : bool :=
  match a, b with
    |false, false => false
    |_, _ => true
  end.

Notation "x || y" := (or x y).


Lemma or_idem' : forall a : bool, a || a = a.
Proof. intro. destruct a; simpl; reflexivity.
Qed.
 
Lemma or_conm' : forall (a b : bool), a || b = b || a.
Proof. intros. destruct a.
  - destruct b; simpl; reflexivity.
  - destruct b; simpl; reflexivity.
Qed.

Lemma or_asoc : forall (a b c: bool), (a || b) || c = a || (b || c).
Proof. intros. destruct a, b, c; simpl; reflexivity. Qed.    

Lemma distrib : forall (a b c : bool), a && (b || c) = (a && b) || (a && c).
Proof. intros. destruct a, b, c; reflexivity; simpl. Qed.

Definition not (a : bool) : bool :=
  match a with 
    |true => false 
    |false => true
  end.

(***OJO: pide deteminar un nivel para saber la preferencia que tiene***)
Notation "¬ x" := (not x)  (at level 75 , right associativity).
Print " ¬ ".

(*he tenido que poner paréntesis porque el ¬ me lo aplicaba a todo y no solo al lado izquierdo de la igualdad*)
Lemma not_not : forall a : bool, (¬ (¬ a)) =  a.
Proof. intro. destruct a; simpl; reflexivity. Qed.


Lemma morgan : forall (a b : bool), (¬ (a && b)) = (¬ a) || (¬ b).
Proof. intros. destruct a, b; simpl; reflexivity. Qed.

 




