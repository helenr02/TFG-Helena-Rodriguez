datatype Lista<T> = Nil | Cons(x : T, xs : Lista<T>)

method m() {
  assert Cons(5, Nil).Cons? && Cons(5, Nil).x == 5;
}

method n(){
  assert Cons(4, Nil).(xs := Cons(3, Nil)) == Cons(4, Cons(3, Nil));
}

function head<T>(default : T, l : Lista<T>) : T
    ensures l == Nil ==> head(default, l) == default
    ensures l != Nil ==> head(default, l) == l.x
{
    match l 
    case Nil => default
    case Cons(x,_) => x
}

function tail<T>(l : Lista<T>) : Lista<T>
    ensures l == Nil ==> tail(l) == Nil
    ensures l != Nil ==> tail(l) == l.xs
{
    match l 
    case Nil => Nil
    case Cons(_,xs) => xs
}

function concatenar<T>(l1 : Lista<T>, l2 : Lista<T>) : Lista<T>
    ensures l1 == Nil ==> concatenar(l1, l2) == l2
    ensures l2 == Nil ==> concatenar(l1,l2) == l1
{
    match l1
    case Nil => l2
    case Cons(x,xs) => Cons(x, concatenar(xs, l2))
}

lemma cons_concat<T>(x: T, m: Lista<T>, l: Lista<T>)
    ensures concatenar(Cons(x,m), l) == Cons(x, concatenar(m, l))
{}

lemma concat_asoc<T>(m: Lista<T>, l: Lista<T>, t: Lista<T>)
    ensures concatenar(m, concatenar(l,t)) == concatenar(concatenar(m,l),t)
{}

lemma concat_four_lists<T>(m: Lista<T>, l: Lista<T>, t: Lista<T>, u: Lista<T>)
    ensures concatenar(concatenar(m, l), concatenar(t, u)) == concatenar(m, concatenar(l, concatenar(t, u)))
{
}

function len<T>(l: Lista<T>) : int
    ensures l == Nil ==> len(l) == 0
    ensures l != Nil ==> len(l) == 1 + len(l.xs)
{
    match l 
    case Nil => 0
    case Cons(x,xs) => 1 + len(xs)
}

function inversa<T>(l : Lista<T>) : Lista<T>
    decreases l
{
    match l 
    case Nil => Nil
    case Cons(x,xs) => concatenar(inversa(xs), Cons(x, Nil))
}


lemma len_concat<T>(m: Lista<T>, l: Lista<T>)
    ensures len(concatenar(m, l)) == len(m) + len(l)
{}

lemma len_inversa<T>(m : Lista<T>)
    ensures len(inversa(m)) == len(m)
{
    match m
    case Nil => { // caso base
        assert len(inversa(m)) == 0;
    }
    case Cons(x,xs) => {
        assert len(inversa(xs)) == len(xs); // HI
        len_concat(inversa(xs), Cons(x, Nil)); // Uso un lema
    }
}

function In<T(==)>(x: T, l: Lista<T>): bool //ponemos (==) para definir la igualdad x==y entre tipos T
    ensures l == Nil ==> In(x, l) == false
{
    match l
    case Nil => false
    case Cons(y, ys) => x == y || In(x, ys)
}

function All<T>(P: T -> bool, l: Lista<T>): bool
    ensures l == Nil ==> All(P,l) == true
{
    match l
    case Nil => true
    case Cons(x, xs) => P(x) && All(P, xs)
}



lemma All_In<T>(P: T -> bool, l: Lista<T>)
    ensures (forall x :: (In(x, l) ==> P(x))) ==> All(P, l)
    ensures All(P,l) ==> (forall x :: In(x, l) ==> P(x))
{
    match l
    case Nil => {
        assert forall x :: In(x,Nil) ==> P(x);
        assert  All(P,Nil) == true;
    }
    case Cons(x,xs) => {
        //Primera postcond
        assert (forall x :: (In(x, xs) ==> P(x))) ==>All(P,xs); // HI

        //Segunda postcond
        assert All(P,xs) ==> (forall x :: In(x,xs) ==> P(x));
    }
}