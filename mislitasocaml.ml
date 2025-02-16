
module Listas =
 struct
  (** val lista_rect :
      'a2 -> ('a1 -> 'a1 list -> 'a2 -> 'a2) -> 'a1 list -> 'a2 **)

  let rec lista_rect f f0 = function
  | [] -> f
  | y::l0 -> f0 y l0 (lista_rect f f0 l0)

  (** val lista_rec :
      'a2 -> ('a1 -> 'a1 list -> 'a2 -> 'a2) -> 'a1 list -> 'a2 **)

  let rec lista_rec f f0 = function
  | [] -> f
  | y::l0 -> f0 y l0 (lista_rec f f0 l0)

  (** val head : 'a1 -> 'a1 list -> 'a1 **)

  let head default = function
  | [] -> default
  | x::_ -> x

  (** val tail : 'a1 list -> 'a1 list **)

  let tail = function
  | [] -> []
  | _::xs -> xs

  (** val concatenar : 'a1 list -> 'a1 list -> 'a1 list **)

  let rec concatenar l m =
    match l with
    | [] -> m
    | x::xs -> x::(concatenar xs m)

  (** val len : 'a1 list -> int **)

  let rec len = function
  | [] -> 0
  | _::xs -> succ (len xs)

  (** val inversa : 'a1 list -> 'a1 list **)

  let rec inversa = function
  | [] -> []
  | x::xs -> concatenar (inversa xs) (x::[])

  (** val nthOpcional : int -> 'a1 list -> 'a1 option **)

  let rec nthOpcional n l =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> match l with
                | [] -> Some
                | x::_ -> None x)
      (fun n' -> match l with
                 | [] -> Some
                 | _::xs -> nthOpcional n' xs)
      n

  (** val nthOpcional' : int -> 'a1 list -> 'a1 option **)

  let rec nthOpcional' n = function
  | [] -> Some
  | x::xs ->
    ((fun fO fS n -> if n=0 then fO () else fS (n-1))
       (fun _ -> None x)
       (fun n' -> nthOpcional' n' xs)
       n)

  (** val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list **)

  let rec map f = function
  | [] -> []
  | x::xs -> (f x)::(map f xs)
 end
