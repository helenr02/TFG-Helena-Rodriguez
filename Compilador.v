(*COMPILADOR*)

Module Compiler.

(*                  compile
lenguaje fuente -------------->  programa en lenguaje objetivo
    |                                         |
    |eval_expr                                |eval_prog
    ↓                                         ↓
   nat                                    option stack
*)
(*Tenemos un lenguage de origen, donde las expresiones pueden venir dadas por:
  Una constante (n* natural)
  Suma de dos expresiones *)

Inductive expr : Type :=
  |Const : nat -> expr
  |Plus : expr -> expr -> expr.

Fixpoint eval_expr (e : expr) : nat :=
  match e with 
  |Const i => i
  |Plus e1 e2 =>  (eval_expr e1) + (eval_expr e2)
  end.

Example test_1 : eval_expr (Const 42) = 42.
Proof. trivial. Qed.

Example test_2 : eval_expr (Plus (Const 2) (Const 2)) = 4.
Proof. trivial. Qed.

(*Para el lenguaje meta, las instrucciones que podemos dar a la máquina son:
  Push: pone un elemento en la pila
  Add : quita los dos elementos de más arriba de la pila y deja la suma de ambos, add[2,3,1] = [5,1]*)

Inductive instr : Type :=
  |PUSH : nat -> instr 
  |ADD : instr.

(*Un programa viene dado por una lista de instrucciones*)
Require Import List.
Require Import Coq.Lists.List.
Import ListNotations.
Definition prog := list instr.

Definition stack := list nat.

(*Intérprete del lenguage meta*)
Fixpoint eval_prog (p : prog) (s : stack): option stack :=
  match p, s with
  |(PUSH n) :: p', s => eval_prog p' (n::s)
  |ADD :: p', x::y::s' => eval_prog p' ((x+y)::s')
  |nil, s => Some s
  |_, _ => None
  end.

(* no hay forma de que esta línea la ejecute, me devuelve: 
Syntax error: '.' expected after [lconstr] (in [query_command])
Se arregló haciendo Require Import Coq.Lists.List. Import ListNotations.*)
Example target_test_1 : eval_prog [PUSH 42] [] = Some [42].
Proof. trivial. Qed.
Example target_test_2 : eval_prog [PUSH 2; PUSH 2; ADD] [] = Some [4].
Proof. trivial. Qed.


(*Ahora trauducimos del lenguaje fuente al lenguaje objetivo*)
Fixpoint compile (e : expr) : prog :=
  match e with 
  |Const n => [PUSH n]
  |Plus e1 e2 => compile e2 ++ compile e1 ++ [ADD]
  end.
(*El orden en el caso de Plus es importante por cómo se ha definido antes la función eval_prog*)

Example compile_test_1 : compile (Const 42) = [PUSH 42].
Proof. trivial. Qed.
Example compile_test_2 : compile (Plus (Const 2) (Const 3)) = [PUSH 3; PUSH 2; ADD].
Proof. trivial. Qed.

Example post_test_1 : eval_prog (compile (Const 42)) [] = Some [eval_expr (Const 42)].
Proof. trivial. Qed.

Example post_test_2 :eval_prog (compile (Plus (Const 2) (Const 3))) []  = Some [eval_expr (Plus (Const 2) (Const 3))].
Proof. trivial. Qed.


(*Pero esto son solo unos ejemplos concretos de testeo. Lo importante es demostrarlo ahora para cualquier expresión*)
Theorem compile_correct : forall (e : expr), eval_prog (compile e) [] = Some [eval_expr e].
Proof. Proof. intro. induction e.
  - simpl. reflexivity.
  - simpl. assert (compile_helper : forall (e : expr) (p : prog) (s : stack), eval_prog ((compile e) ++ p) s = eval_prog p ((eval_expr e)::s)).
    {admit. }
    rewrite compile_helper. rewrite compile_helper. simpl. reflexivity.
Admitted.
(*Hemos hecho induction sobre expr, hemos simplificado la expresión de compile, nos falta aplicar eval_prog de alguna 
forma. Buscamos un lema que ayude a aplicar la función *)

(*Pensamos en el sentido de aplicar induction sobre e, p y s. 
  -En s no tiene sentido pues es una pila que queda al final y va a recibir elementos delante, en principio no parece tener 
    mucha lógica.
  -En p lo pensé de primeras pero cuando empiezas la demostración te das cuenta de que si haces induction sobre p, 
   no tienes la HI para todo p, por lo que no tiene sentido tampoco.
  -En expr sí que tiene sentido para que nos divida los casos en sus costructores.

  Conclusión: hacemos solo intro e induction de e:expr.
*)
Lemma compile_helper : forall (e : expr) (p : prog) (s : stack), eval_prog ((compile e) ++ p) s = eval_prog p ((eval_expr e)::s).
Proof. intro e. induction e.
   *simpl. reflexivity.
   *simpl. assert (app_assoc_4_mio : forall (A : Type) (l1 l2 l3 l4 : list A), (l1 ++ l2 ++ l3) ++ l4 = l1 ++ (l2 ++ l3 ++ l4)).
     {admit. }
    intros p s. rewrite app_assoc_4_mio. rewrite IHe2. rewrite IHe1. simpl. reflexivity.
Admitted.

Lemma app_assoc_4 : forall (A : Type) (l1 l2 l3 l4 : list A), l1 ++ (l2 ++ l3 ++ l4) = (l1 ++ l2 ++ l3) ++ l4.
Proof. intros. Check app_assoc. (*app_assoc : forall (A : Type) (l m n : list A), l ++ m ++ n = (l ++ m) ++ n*)
   replace (l2 ++ l3 ++ l4) with ((l2 ++ l3) ++ l4).
      - rewrite app_assoc.  reflexivity.
      - rewrite app_assoc. reflexivity.
Qed.

(*En esta demo no podía acabar de demostrarlo con las tácticas que sabía porque el rewrite actúa sobre el lado 
izquierdo de la igualdad en el goal. Por eso uso symmetry y por eso en la documentación que seguí (app_assoc_4)
plantean el lema al revés*)
Lemma app_assoc_4_mio : forall (A : Type) (l1 l2 l3 l4 : list A), (l1 ++ l2 ++ l3) ++ l4 = l1 ++ (l2 ++ l3 ++ l4).
Proof. intros. replace (l2 ++ l3 ++ l4) with ((l2 ++ l3) ++ l4).
 - symmetry. rewrite app_assoc. reflexivity.
 - rewrite app_assoc. reflexivity.
Qed.

End Compiler.

Require Extraction.
Extraction Language OCaml.
Extract Inlined Constant Init.Nat.add => "( + )".
Extract Inlined Constant app => "( @ )".
Extraction "C:/Users/Helena/Desktop/UNI/Coq_bueno/extracciones/miCompilador.ml" Compiler.eval_expr Compiler.eval_prog Compiler.compile.

(*Al extraer a OCaml nuestra especificación, cambiamos la suma add de naturales y la concatenación de listas en Coq, 
por la + y @ en OCaml donde será más eficiente ya que en el lenguaje de llegada estará optimizado. Esto preserva las
demostraciones realizadas en Coq, puesto que está demostrado con una lógica que hay detrás*)




