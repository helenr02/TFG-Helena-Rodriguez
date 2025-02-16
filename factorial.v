Require Import Arith.

Fixpoint fact (n : nat) :=
  match n with 
  |0 => 1
  |S p => n * (fact p)
  end.

Inductive factorial_of : nat -> nat -> Prop :=
  |factorial_of_zero : factorial_of 0 1
  |factorial_of_succ : forall (a b : nat), factorial_of a b -> factorial_of (S a) ((S a) * b).

Theorem fact_correct : forall n:nat, factorial_of n (fact n).
Proof. 
induction n.
- simpl. apply factorial_of_zero.
- apply factorial_of_succ in IHn. simpl. assumption. 
Qed.



(*Aplicar el mmodus ponems, para demostrar B, como tengo fact_correct: A ->B y A=IHn, demuestro B*)
Theorem fact_correct_apuntes : forall n:nat, factorial_of n (fact n).
Proof. 
induction n as [| k IH].
- simpl. apply factorial_of_zero.
- simpl. apply factorial_of_succ. assumption.
Qed.

(*Otra forma de implementar factorial más eficiente*)
Fixpoint fact_tr_acc (n : nat) (acc : nat) :=
  match n with
  |0 => acc
  |S p => fact_tr_acc p (n * acc)
  end.

Definition fact_tr (n : nat) := fact_tr_acc n 1.

Theorem fact_tr_correct : forall n:nat, factorial_of n (fact_tr n).
Proof. 
induction n.
- apply factorial_of_zero.
- apply factorial_of_succ in IHn. unfold fact_tr. unfold fact_tr in IHn. 
  assert (fact_tr_acc (S n) 1 = S n * fact_tr_acc n 1).
    {induction n.
      *simpl. reflexivity.
      *Restart.
intro. unfold fact_tr. induction n.
- simpl. apply factorial_of_zero.
- simpl. Check mult_1_r. Check Nat.mul_1_r. rewrite Nat.mul_1_r. destruct n.
  * simpl. simpl fact_tr_acc in IHn. rewrite <- Nat.mul_1_r. apply factorial_of_succ.  assumption.
  * Abort.

Lemma fact_tr_acc_mult : forall (n m :nat), fact_tr_acc n m = m * fact_tr_acc n 1.
Proof. 
intros. induction n.
- simpl. rewrite Nat.mul_1_r. reflexivity. (*se puede usar táctica ring*) 
- induction m.
  * simpl. rewrite Nat.mul_0_r. rewrite IHn. simpl. reflexivity.
  * simpl. rewrite Nat.mul_1_r. Restart.
intros. induction n.
- simpl. rewrite Nat.mul_1_r. reflexivity. (*se puede usar táctica ring*) 
- assert (H : fact_tr_acc (S n) m = (fact_tr_acc n ((S n) * m))).
  {simpl. reflexivity. }
  rewrite H. (*no podemos usar IHn porque tiene m y el goal (S n * m), no deja matchear. Eso es porque hemos 
hecho el intro de m y entonces para usar IHn, debe ser tal cual el mismo valor. Vamos a no hacer intro m al principio*)
Restart.

intro. induction n.
  - intro. simpl. rewrite Nat.mul_1_r. reflexivity.
  - intro. assert (H : fact_tr_acc (S n) m = (fact_tr_acc n ((S n) * m))).
    {simpl. reflexivity. }
    rewrite H. rewrite IHn. simpl. rewrite Nat.mul_1_r. rewrite IHn with (m := S n). ring.
Qed.

Theorem fact_tr_correct_mio : forall n:nat, factorial_of n (fact_tr n).
Proof. intro. unfold fact_tr. induction n.
  - simpl. apply factorial_of_zero.
  - simpl. rewrite Nat.mul_1_r. destruct n.
      * simpl. simpl fact_tr_acc in IHn. rewrite <- Nat.mul_1_r. apply factorial_of_succ.  assumption.
      * apply factorial_of_succ in IHn. rewrite fact_tr_acc_mult. assumption.
Qed.

Theorem fact_tr_correct : forall n:nat, factorial_of n (fact_tr n).
Proof. 
intro. unfold fact_tr. induction n.
- simpl. apply factorial_of_zero.
- simpl. rewrite Nat.mul_1_r. destruct n.
  * simpl. rewrite <- Nat.mul_1_r. simpl fact_tr_acc in IHn. apply factorial_of_succ. assumption.
  * rewrite fact_tr_acc_mult. apply factorial_of_succ. assumption.
Qed.

Lemma fact_helper : forall (n acc : nat), fact_tr_acc n acc = (fact n) * acc.
Proof. 
intro n. induction n; intro.
- simpl. ring.
- simpl. rewrite IHn. ring.
Qed.

Theorem fact_tr_is_fact : forall n:nat, fact_tr n = fact n.
Proof. 
intro. unfold fact_tr.  rewrite fact_helper. ring.
Qed.

Require Import Extraction.
Extraction Language OCaml.
Extract Inductive nat =>
  int [ "0" "succ" ] "(fun fO fS n -> if n=0 then fO () else fS (n1))".
Extract Inlined Constant Init.Nat.mul => "( * )".
Extraction "C:/Users/Helena/Desktop/UNI/Coq bueno/extracciones/fact.ml" fact_tr.
(*Especificamos el cambio del tipo nat de Coq al de OCaml para que realice las operaciones de suma y multiplicación de 
forma eficiente*)


Extraction Language Haskell.
Extraction "C:/Users/Helena/Desktop/UNI/Coq bueno/facthaskell.hs" fact_tr.
    


