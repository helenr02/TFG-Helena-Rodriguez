
(*LIBRO 1 SOFTWARE *)

Inductive day : Type :=
  | monday
  | tuesday
  | wednesday
  | thursday
  | friday
  | saturday
  | sunday.

Definition next_weekday (d:day) : day :=
  match d with
  | monday => tuesday
  | tuesday  =>  wednesday
  | wednesday  =>  thursday
  | thursday  =>  friday
  | friday  =>  monday
  | saturday  =>  monday
  | sunday  =>  monday
  end.

Print day.
Print next_weekday.

Compute (next_weekday friday). 
Compute next_weekday friday. (*no hacen falta los paréntesis*)
Compute next_weekday (next_weekday monday).

Example test_next_weekday:
  (next_weekday (next_weekday saturday)) = tuesday.
Proof.
  simpl.
  reflexivity.
Qed.



From Coq Require Export String.

Inductive bool : Type :=
  |true
  |false. 

Definition negb (b:bool) : bool :=
  match b with 
  | true => false
  |false => true 
  end.

Definition andb (b1:bool) (b2:bool) : bool :=
  match b1 with 
  |true => b2
  |false => false 
  end.

Definition orb (b1:bool) (b2:bool) : bool :=
  match b1 with 
  |true => true
  |false => b2
  end.  

Example test_orb1: orb true false =  true.
Proof. simpl. reflexivity. Qed.
Example test_orb2: (orb false false) = false.
Proof. simpl. reflexivity. Qed.
Example test_orb3: (orb false true) = true.
Proof. simpl. reflexivity. Qed.
Example test_orb4: (orb true true) = true.
Proof. simpl. reflexivity. Qed.

Example prueba_orbGen: forall b:bool, 
  (orb true b) = true.
Proof.
  intro. 
  destruct b.
    -simpl. reflexivity.
    -apply test_orb1.
Qed.

Notation "x && y" := (andb x y).
Notation "x || y" := (orb x y).

Check true && false.


Example test_orb5: false || false || true = true.
Proof. simpl. reflexivity. Qed.

Definition negb' (b:bool) : bool :=
  if b then false
  else true. 

Definition andb' (b1:bool) (b2:bool) : bool :=
  if b1 then b2
  else false.

Definition orb' (b1:bool) (b2:bool) : bool :=
  if b1 then b2
  else false.


Definition nandb (b1:bool) (b2:bool) : bool :=
  match b1 with 
  |true => (negb' b2)
  |false => true
  end.

 
Example test_nandb1: (nandb true false) = true.
  simpl. reflexivity. Qed.
Example test_nandb2: (nandb false false) = true.
  simpl. reflexivity. Qed.
Example test_nandb3: (nandb false true) = true.
  simpl. reflexivity. Qed.
Example test_nandb4: (nandb true true) = false.
  simpl. reflexivity. Qed. 

Definition andb3 (b1:bool) (b2:bool) (b3:bool) : bool :=
  match b1 with 
  |true => andb b2 b3
  |false => false
  end.

Example test_andb31: (andb3 true true true) = true.
  simpl. reflexivity. Qed.
Example test_andb32: (andb3 false true true) = false.
  simpl. reflexivity. Qed.
Example test_andb33: (andb3 true false true) = false.
  simpl. reflexivity. Qed.
Example test_andb34: (andb3 true true false) = false.
  simpl. reflexivity. Qed.

Check true : bool.
Check true.
Check negb.

Module NatPlayground.
Inductive nat : Type :=
  | O
  | S (n : nat).

Definition pred (n : nat) : nat :=
  match n with
  | O => O
  | S n' => n'
  end.

End NatPlayground.

Check S.

Fixpoint even (n:nat) : bool :=
  match n with
  | O => true
  | S O => false
  | S (S n') => even n'
  end.

Definition odd (n:nat) : bool :=
  negb (even n).
Example test_odd1: odd 1 = true.
Proof. simpl. reflexivity. Qed. (*No se aplica simpl*)
Example test_odd2: odd 4 = false.
Proof. simpl. reflexivity. Qed.

Module NatPlayground2.

Fixpoint plus (n m:nat) : nat :=
  match n with 
  |O => m
  |S n' => S (plus n' m)
  end.

Compute plus 3 5.

Fixpoint mult (n m : nat) : nat :=
  match n with 
  |O => O
  |S n' => plus m (mult n' m)
  end.

Example test_mult1: (mult 3 3) = 9.
Proof. simpl. reflexivity. Qed.

Fixpoint minus (n m : nat) : nat :=
  match n, m with 
  |O , _ => O
  |S _, O => n
  |S n', S m' => minus n' m'
  end.  

End NatPlayground2.

Fixpoint exp (base power : nat) : nat :=
  match power with 
  |O => S O
  |S n' => mult base (exp base n')
  end.

Fixpoint factorial (n:nat) : nat :=
  match n with 
  |O => S O
  |S O => S O
  |S n' => mult n (factorial n')
  end.

Example test_factorial1: (factorial 3) = 6.
Proof. simpl. reflexivity. Qed.
Example test_factorial2: (factorial 5) = (mult 10 12).
Proof. simpl. reflexivity. Qed.

Notation "x + y" := (plus x y)(at level 50, left associativity) : nat_scope.
Notation "x - y" := (minus x y)(at level 50, left associativity) : nat_scope.
Notation "x * y" := (mult x y)(at level 40, left associativity) : nat_scope.

Compute 3+4.
Compute 3 + 4.
Check ((0 + 1) + 1).
Compute 0 + 1 + 1.

Fixpoint eqb (n m : nat) : bool :=
  match n with 
  |O => match m with 
        |O => true
        |S n'  => false
        end
  |S n' => match m with 
        |O => false 
        |S m' => eqb n' m'
        end
  end.

Fixpoint leb (n m : nat) : bool :=
  match n with 
  |O => true
  |S n' => match m with 
          |O => false
          |S m' => leb n' m'
          end
  end.

Example test_leb1: leb 2 2 = true.
Proof. simpl. reflexivity.  Qed.
Example test_leb2: leb 2 4 = true.
Proof. simpl. reflexivity. Qed.
Example test_leb3: leb 4 2 = false.
Proof. simpl. reflexivity. Qed.

Notation "x =? y" := (eqb x y) (at level 70) : nat_scope.
Notation "x <=? y" := (leb x y) (at level 70) : nat_scope.

Example test_leb3': (4 <=? 2) = false.
Proof. simpl. reflexivity. Qed.

Fixpoint ltb (n m : nat) : bool :=
  if n =? m then false
  else match n with 
       |O => true 
       |S n' => ltb n' m 
        end.

Notation "x <? y" := (ltb x y) (at level 70) : nat_scope.
Example test_ltb1: (ltb 2 2) = false.
Proof. simpl. reflexivity.  Qed.
Example test_ltb2: (ltb 2 4) = true. 
Proof. simpl. reflexivity.  Qed.
Example test_ltb3: (ltb 4 2) = false.
Proof. simpl. reflexivity.  Qed.

Theorem plus_O_n : forall n : nat, 0 + n = n.
Proof. intro n. simpl. reflexivity. Qed.
Theorem mult_0_l : forall n:nat, 0 * n = 0.
Proof. intro. simpl. reflexivity. Qed.

Theorem plus_id_example : forall n m:nat, n = m -> n + n = m + m.
Proof. intro n. intro m. intro H. rewrite <- H. reflexivity. Qed. (*podemos elegir al hacer rewrite qué lado de la igualdad en H queremos sustituir*)
Theorem plus_id_exercise : forall n m o : nat, n = m -> m = o -> n + m = m + o.
Proof. intros n m o. intros H H0. rewrite -> H. rewrite H0. reflexivity. Qed.

Check mult_n_O.
Check mult_n_Sm.

Theorem mult_n_0_m_0 : forall p q : nat,(p * 0) + (q * 0) = 0.
Proof. intros p q. rewrite <- mult_n_O. rewrite <- mult_n_O. simpl. reflexivity. Qed. (*podemos usar teoremas o lemas que no están en las hipótesis pero que se han demostrado ya antes o vienen en las funciones de Coq*)
Theorem mult_n_1 : forall p : nat, p * 1 = p.
Proof. intro. rewrite <- mult_n_Sm. rewrite <- mult_n_O. simpl. reflexivity. Qed.

Theorem plus_1_neq_0_firsttry : forall n : nat, (n + 1) =? 0 = false.
Proof. intros n. destruct n as [|n'] eqn:E. 
  -reflexivity.
  -reflexivity.
Qed.

Theorem negb_involutive : forall b : bool, negb (negb b) = b.
Proof. intro. destruct b eqn:E.
  -simpl. reflexivity.
  -simpl. reflexivity.
Qed.

Theorem andb_commutative : forall b c, andb b c = andb c b.
Proof. intros. destruct b eqn:Eb.
  -destruct c eqn:Ec.
   *simpl. reflexivity.
   *simpl. reflexivity.
  -destruct c eqn:Ec.
   *simpl. reflexivity.
   *simpl. reflexivity.
Qed.

Theorem andb_true_elim2 : forall b c : bool,
  andb b c = true -> c = true.
Proof. intros. destruct b eqn:Eb.
  -destruct c eqn:Ec.
    *reflexivity.
    *rewrite <- H. simpl. reflexivity.
  -destruct c eqn:Ec.
    *reflexivity.
    *rewrite <- H. simpl. reflexivity.
Qed.


Theorem identity_fn_applied_twice : forall (f : bool -> bool), 
  (forall (x : bool), f x = x) -> forall (b : bool), f (f b) = b.
Proof. intro. intro. intro. 
  rewrite -> H. 
  rewrite -> H. 
  reflexivity.
Qed.

Theorem negation_fn_applied_twice : forall (f : bool -> bool), 
  (forall (x : bool), f x = negb x) -> forall (b : bool), f (f b) = b.
Proof. intro. intro. intro. 
  rewrite -> H.
  rewrite -> H.
  destruct b.
  -simpl. reflexivity.
  -simpl. reflexivity.
Qed.

Theorem andb_eq_orb : forall (b c : bool), (andb b c = orb b c) -> b = c.
Proof.
  intros.
  destruct b.
  -destruct c.
    *reflexivity.
    *simpl in H. rewrite H. reflexivity.
  -destruct c.
    *simpl in H. rewrite -> H. reflexivity.
    *reflexivity.
Qed.

Module LateDays.

Inductive letter : Type :=
  | A | B | C | D | F.

Inductive modifier : Type :=
  | Plus | Natural | Minus.

Inductive grade : Type :=
  Grade (l:letter) (m:modifier).

Inductive comparison : Type :=
  | Eq (* "equal" *)
  | Lt (* "less than" *)
  | Gt. (* greater than *)

Definition letter_comparison (l1 l2 : letter) : comparison :=
  match l1, l2 with
  | A, A => Eq
  | A, _ => Gt
  | B, A => Lt
  | B, B => Eq
  | B, _ => Gt
  | C, (A | B) => Lt
  | C, C => Eq
  | C, _ => Gt
  | D, (A | B | C) => Lt
  | D, D => Eq
  | D, _ => Gt
  | F, (A | B | C | D) => Lt
  | F, F => Eq
  end.

Compute letter_comparison B A.
Compute letter_comparison D D.
Compute letter_comparison B F.

Theorem letter_comparison_Eq : forall l, letter_comparison l l = Eq.
Proof. intro. destruct l. reflexivity. reflexivity. reflexivity. reflexivity. reflexivity.
Qed.

Definition modifier_comparison (m1 m2 : modifier) : comparison :=
  match m1, m2 with
  | Plus, Plus => Eq
  | Plus, _ => Gt
  | Natural, Plus => Lt
  | Natural, Natural => Eq
  | Natural, _ => Gt
  | Minus, (Plus | Natural) => Lt
  | Minus, Minus => Eq
  end.

Check grade.
Check Grade A Plus.
Check Grade.


Definition grade_comparison (g1 g2 : grade) : comparison :=
  match g1, g2 with
  |Grade l1 m1, Grade l2 m2 =>
    match letter_comparison l1 l2 with
    |Gt => Gt
    |Lt => Lt
    |Eq => modifier_comparison m1 m2
    end
  end.

Example test_grade_comparison1 :
  (grade_comparison (Grade A Minus) (Grade B Plus)) = Gt.
Proof. simpl. reflexivity. Qed.
Example test_grade_comparison2 :
  (grade_comparison (Grade A Minus) (Grade A Plus)) = Lt.
Proof. simpl. reflexivity. Qed.
Example test_grade_comparison3 :
  (grade_comparison (Grade F Plus) (Grade F Plus)) = Eq.
Proof. simpl. reflexivity. Qed.
Example test_grade_comparison4 :
  (grade_comparison (Grade B Minus) (Grade C Plus)) = Gt.
Proof. simpl. reflexivity. Qed.

Definition lower_letter (l : letter) : letter :=
  match l with
  | A => B
  | B => C
  | C => D
  | D => F
  | F => F (* Can't go lower than F! *)
  end.

Theorem lower_letter_lowers: forall (l : letter),
  letter_comparison (lower_letter l) l = Lt.
Proof.
  intros l.
  destruct l.
  - simpl. reflexivity.
  - simpl. reflexivity.
  - simpl. reflexivity.
  - simpl. reflexivity.
  - simpl. (* We get stuck here. *)
Abort.
  
Theorem lower_letter_F_is_F:
  lower_letter F = F.
Proof.
  simpl. reflexivity.
Qed.


Theorem lower_letter_lowers:
  forall (l : letter),
    letter_comparison F l = Lt ->
    letter_comparison (lower_letter l) l = Lt.
Proof. intros. destruct l.
  - simpl. reflexivity.
  - simpl. reflexivity.
  - simpl. reflexivity.
  - simpl. reflexivity.
  - simpl. rewrite <- H. simpl. reflexivity.
Qed.

Definition lower_grade (g : grade) : grade :=
  match g with
  |Grade F Minus => Grade F Minus
  |Grade l m => match m with 
                |Plus => Grade l Natural
                |Natural => Grade l Minus
                |Minus => Grade (lower_letter l) Plus
                end
  end.

Example lower_grade_A_Plus :
  lower_grade (Grade A Plus) = (Grade A Natural).
Proof. simpl. reflexivity. Qed.
Example lower_grade_A_Natural :
  lower_grade (Grade A Natural) = (Grade A Minus).
Proof. simpl. reflexivity. Qed.
Example lower_grade_A_Minus :
  lower_grade (Grade A Minus) = (Grade B Plus).
Proof. simpl. reflexivity. Qed.
Example lower_grade_B_Plus :
  lower_grade (Grade B Plus) = (Grade B Natural).
Proof. simpl. reflexivity. Qed.
Example lower_grade_F_Natural :
  lower_grade (Grade F Natural) = (Grade F Minus).
Proof. simpl. reflexivity. Qed.
Example lower_grade_twice :
  lower_grade (lower_grade (Grade B Minus)) = (Grade C Natural).
Proof. simpl. reflexivity. Qed.
Example lower_grade_thrice :
  lower_grade (lower_grade (lower_grade (Grade B Minus))) = (Grade C Minus).
Proof. simpl. reflexivity. Qed.


Theorem lower_grade_F_Minus : lower_grade (Grade F Minus) = (Grade F Minus).
Proof. simpl. reflexivity. Qed.

Theorem lower_grade_lowers :
  forall (g : grade),
    grade_comparison (Grade F Minus) g = Lt ->
    grade_comparison (lower_grade g) g = Lt.
Proof. intros. rewrite <- H.  destruct g. destruct m. Admitted.


Definition apply_late_policy (late_days : nat) (g : grade) : grade :=
  if late_days <? 9 then g
  else if late_days <? 17 then lower_grade g
  else if late_days <? 21 then lower_grade (lower_grade g)
  else lower_grade (lower_grade (lower_grade g)).

Theorem apply_late_policy_unfold : forall (late_days : nat) (g : grade),
(apply_late_policy late_days g) =
  (if late_days <? 9 then g 
   else if late_days <? 17 then lower_grade g
   else if late_days <? 21 then lower_grade (lower_grade g)
   else lower_grade (lower_grade (lower_grade g))).
Proof. intros. reflexivity. Qed.

Theorem no_penalty_for_mostly_on_time :
  forall (late_days : nat) (g : grade),
    (late_days <? 9 = true) ->
    apply_late_policy late_days g = g.
Proof. intros. rewrite -> apply_late_policy_unfold. rewrite H. reflexivity. Qed.

Theorem grade_lowered_once :
  forall (late_days : nat) (g : grade),
    (late_days <? 9 = false) ->
    (late_days <? 17 = true) ->
    (grade_comparison (Grade F Minus) g = Lt) ->
    (apply_late_policy late_days g) = (lower_grade g).
Proof. intros. rewrite -> apply_late_policy_unfold. rewrite H0. rewrite H. reflexivity. Qed.

End LateDays.

(*TEMA2: INDUCTION*)

Theorem add_0_r_firsttry : forall n:nat,
  n + 0 = n.
Proof. intro. simpl. (*No funciona, no puedo hacer n + 0  porque en la definición de la suma, 
no puede decrecer n porque no sabe cuánto vale, en cambio cuando poníamos 0 + n = n  
sí que se puede usar simpl.*)
Abort.
Theorem add_0_r_secondtry : forall n:nat,
  n + 0 = n.
Proof.
  intros n. destruct n as [| n'] eqn:E.
  - (* n = 0 *)
    reflexivity. (* so far so good... *)
  - (* n = S n' *)
    simpl. (*Igual que antes, no podemos usar simpl porque no sabe cuánto vale n'*)
Abort.

Theorem add_0_r : forall n:nat, n + 0 = n. 
Proof.
  intros n. induction n as [| n' IHn']. (*aprendemos el comando induction para demostrar por inducción*)
  - (* n = 0 *) reflexivity.
  - (* n = S n' *) simpl. rewrite -> IHn'. reflexivity. Qed.

Theorem minus_n_n : forall n,
  minus n n = 0.
Proof. intro. induction n as [| n' IHn'].
  -simpl. reflexivity.
  -simpl. rewrite <- IHn'. reflexivity.
Qed.

Theorem mul_0_r : forall n:nat,
  n * 0 = 0.
Proof. intro. induction n as [| n' IHn'].
  -simpl. reflexivity.
  -simpl. rewrite IHn'. reflexivity.
Qed.

Theorem plus_n_Sm : forall n m : nat,
  S (n + m) = n + (S m).
Proof. intros n m. induction n as [| n' IHn'].
  -simpl. reflexivity.
  -simpl. rewrite -> IHn'. reflexivity.
Qed.

Theorem add_comm : forall n m : nat,
  n + m = m + n.
Proof. intros n m. induction n as [|n' IHn'].
  -simpl. rewrite -> add_0_r. reflexivity.
  -simpl. rewrite -> IHn'. rewrite -> plus_n_Sm. reflexivity.
Qed.

Theorem add_assoc : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof. intros. induction n as [|n' IHn'].
  -simpl. reflexivity.
  -simpl. rewrite IHn'. reflexivity.
Qed.

Fixpoint double (n:nat) :=
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.

Lemma double_plus : forall n, double n = n + n .
Proof. intro. induction n as [|n' IHn']. 
  -simpl. reflexivity.
  -simpl. rewrite IHn'. rewrite -> plus_n_Sm. reflexivity.
Qed.

Theorem eqb_refl : forall n : nat,
  (n =? n) = true.
Proof. intro. induction n as [| n' IHn'].
  -simpl. reflexivity.
  -simpl. rewrite IHn'. reflexivity.
Qed.

Theorem even_S : forall n : nat,
  even (S n) = negb (even n).
Proof. intro. induction n as [|n' IHn'].
  -simpl. reflexivity.
  -rewrite -> IHn'. rewrite -> negb_involutive. simpl. reflexivity.
Qed.

(*ejemplo de uso del assert*)
Theorem mult_0_plus' : forall n m : nat,
  (n + 0 + 0) * m = n * m.
Proof.
  intros n m.
  assert (H: n + 0 + 0 = n).
    { rewrite add_comm. simpl. rewrite add_comm. reflexivity. }
  rewrite -> H.
  reflexivity. 
Qed.

Theorem plus_rearrange_firsttry : forall n m p q : nat,
  (n + m) + (p + q) = (m + n) + (p + q).
Proof.
  intros n m p q.
  rewrite add_comm. (*al hacer el rewrite, se aplica al más exterior, o sea que no se me va a aplicar al n+m como me gustaría*)
Abort.

Theorem plus_rearrange : forall n m p q : nat,
  (n + m) + (p + q) = (m + n) + (p + q).
Proof.
  intros n m p q.
  assert (H: n + m = m + n). (*me creo una prueba intermedia para las variables que me interesan y así luego puedo usarla como hipótesis*)
    {rewrite add_comm. reflexivity. }
  rewrite H. reflexivity.
Qed.

Theorem add_shuffle3 : forall n m p : nat,
  n + (m + p) = m + (n + p).
Proof. intros. 
  assert (H: n + (m + p) = (n + m) + p).
    { rewrite add_assoc. reflexivity. }
  rewrite H. 
  assert (H': n + m = m + n).
    {rewrite add_comm. reflexivity. }
  rewrite H'. rewrite add_assoc. reflexivity.
Qed.

Theorem add_shuffle3' : forall n m p : nat,  (* hay muchas formas de demostrar los teoremas*)
  n + (m + p) = m + (n + p).
Proof. intros.
  rewrite add_assoc.
  assert (H: m + (n + p) = (m + n) + p).
    {rewrite add_assoc. reflexivity. }
  rewrite -> H. rewrite add_comm. 
  assert (H': n + m = m + n).
    {rewrite add_comm. reflexivity. }
  rewrite H'. rewrite add_comm. reflexivity.
Qed.


Theorem mul_comm : forall m n : nat,
  m * n = n * m.
Proof. intros. induction n as [| n' IHn'].
  -simpl. induction m as [|m' IHm'].
    *simpl. reflexivity.
    *simpl. rewrite IHm'. reflexivity.
  - simpl. rewrite <- IHn'. 
    assert (H: m * (1 + n') = m + m * n').
      {
Admitted.

Check leb.

Theorem plus_leb_compat_l : forall n m p : nat,
  n <=? m = true -> (p + n) <=? (p + m) = true.
Proof. intros. induction p as [|p' IHp'].
  *simpl. rewrite H. reflexivity.
  *simpl. rewrite IHp'. reflexivity.
Qed.

(*SABER ANTES DE ACTUAR SI VA A SER DEMO CON SIMPL+REFLEX, DESTRUCT O INDUCTION*)

Theorem leb_refl : forall n:nat,  (*Pensé: simpl+reflex, Sol: induction*)
  (n <=? n) = true.
Proof. intro. induction n as [|n' IHn'].
  -simpl. reflexivity.
  -simpl. rewrite IHn'. reflexivity.
Qed.

Theorem zero_neqb_S : forall n:nat, (*Pensé: simpl+reflex*)
  0 =? (S n) = false.
Proof. intro. simpl. reflexivity.
Qed.

Theorem andb_false_r : forall b : bool, (*Pense: destruct*)
  andb b false = false.
Proof. intro. destruct b.
  -simpl. reflexivity.
  -simpl. reflexivity.
Qed.

Theorem S_neqb_0 : forall n:nat, (*Pensé: simpl+reflex*)
  (S n) =? 0 = false.
Proof. intro. simpl. reflexivity.
Qed.

Theorem mult_1_l : forall n:nat, 1 * n = n. (*Pensé: induction, Sol: simpl + reflex*)
Proof. intro. simpl. rewrite add_0_r. reflexivity. 
Qed.

Theorem all3_spec : forall b c : bool,
  orb
    (andb b c)
    (orb (negb b)
         (negb c))
  = true.
Proof. intros. destruct b, c.
  -simpl. reflexivity.
  -simpl. reflexivity.
  -simpl. reflexivity.
  -simpl. reflexivity.
Qed.

Theorem mult_plus_distr_r : forall n m p : nat, (*DIFÍCIL*)
  (n + m) * p = (n * p) + (m * p).
Proof. intros. induction n as [|n' IHn'].
  -simpl. reflexivity.
  -simpl. rewrite <- add_assoc. rewrite add_comm. rewrite IHn'. rewrite add_comm. reflexivity.
Qed.

Theorem mult_assoc : forall n m p : nat,
  n * (m * p) = (n * m) * p.
Proof. intros. induction n as [|n' IHn'].
  -simpl. reflexivity.
  -simpl. rewrite add_comm. rewrite IHn'. rewrite <- mult_plus_distr_r. rewrite add_comm. reflexivity.
Qed.











