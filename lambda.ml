type sorte = Type | Kind

type terme =
    Var of int (* Indices de De Brujin, on commence à 1 et on augmente *)
  | Sorte of sorte
  | Application of (terme * terme) 
  | Abstraction of (terme * terme) 
  | Produit of (terme * terme) 
  | Constant of int 

type definition = {
  definiens : terme option; (* None si la definition est un axiome *) 
  ty : terme;
}

type contexte = {
  defs : definition array; (* Tableau des définitions *)
  vars : terme list (* Liste des types des variables libres *) 
}

let push_var t contexte = {contexte with vars = t :: contexte.vars};;

let rec subst_aux s = function
    | Var n -> s n
    | Application (a, b) -> Application (subst_aux s a, subst_aux s b)
    | Abstraction (a, b) -> Abstraction (subst_aux s a, subst_aux (function
      | 1 -> Var 1
      | n -> incr (s (n - 1))
      ) b)
    | Produit (a, b) -> Produit (subst_aux s a, subst_aux (function
      | 1 -> Var 1
      | n -> incr (s (n - 1))
      ) b)
    | t -> t
and incr t = subst_aux (fun k -> Var (k + 1)) t;;

(* subst n a b = a[n:=b] *)
let subst n a b = subst_aux (function
    | k when k = n -> b
    | k -> Var k) a
;;

(* Beta réduit le terme en garantissant le bon typage *)
let rec reduit = function
    | Abstraction (a, b) -> Abstraction (reduit a, reduit b)
    | Produit (a, b) -> Produit (reduit a, reduit b)
    | Application (a, b) -> ( match reduit a with
      | Abstraction (_, t) -> subst 1 t (reduit b) (* 1 est l'indice de De Brujin de la variable liante *)
      | Produit (_, t) -> subst 1 t (reduit b)
      | t -> Application (reduit t, reduit b)
    ) 
    | t -> t
;;

let rec term_to_string = function
    | Var n -> string_of_int n
    | Sorte Type -> "*"
    | Sorte Kind -> "¤"
    | Application (a, b) -> "(" ^ term_to_string a ^ " " ^ term_to_string b ^ ")"
    | Abstraction (a, b) -> "( λ " ^ term_to_string a ^ " . " ^ term_to_string b ^ ")"
    | Produit (a, b) -> "( Π " ^ term_to_string a ^ " . " ^ term_to_string b ^ ")"
    | Constant n -> "a(" ^ string_of_int n ^ ")"

let rec type_assignment contexte t = ( match reduit t with
    | Var k ->
      let rec incr_by_n n t = match n with
      | 0 -> t
      | n -> incr_by_n (n - 1) (incr t)
      in
      let ty = List.nth contexte.vars (k - 1) in (* le type de t *)
      incr_by_n k ty (* On modifie le type pour faire correspondre au contexte *)
    | Sorte Type -> Sorte Kind
    | Sorte Kind -> failwith "Le terme n'est pas typable : un Kind n'as pas de type" 
    | Application (a, b) -> (
        match type_assignment contexte a with
      | Produit (x, y) -> Application (Produit (x, y), b)
      | t -> failwith "Le terme n'est pas typable : application non légale" 
    )
    | Abstraction (a, b) -> Produit (a, type_assignment (push_var a contexte) b)
    | Produit (a, b) -> type_assignment (push_var a contexte) b
    | Constant k -> contexte.defs.(k).ty
)


let verif_type t a =
    print_string "\n Réduction du type de p : ";
    print_string (term_to_string (reduit t));
    print_string "\n Réduction du type de a :";
    print_string (term_to_string (reduit a));
    if (reduit t) = (reduit a) then
        print_string "\n Réussite : p est bien une preuve de A !"
    else
        failwith "p n'est pas une preuve de A"
;;

let is_proof contexte p a =
    print_string " Terme en entrée  : ";
    print_string (term_to_string p);
    let ty = type_assignment contexte p in
    verif_type ty a
;;

(* Exemple d'utilisation : *)
is_proof {defs=[||]; vars = []}  
(Abstraction(Produit(Sorte Type, Sorte Type), Abstraction(Var 1, Application(Var 2, Var 1)))) (Produit (Produit(Sorte Type, Sorte Type), Produit(Var 1, Sorte Type)));;

(* Sortie du programme :

 Terme en entrée  : ( λ ( Π * . * ) . ( λ 1 . (2 1)))
 Réduction du type de p : ( Π ( Π * . * ) . ( Π 1 . * ))
 Réduction du type de a :( Π ( Π * . * ) . ( Π 1 . * ))
 Réussite : p est bien une preuve de A !

*)
