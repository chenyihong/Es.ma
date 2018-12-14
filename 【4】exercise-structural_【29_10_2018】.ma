(**************************************************************************)
(*       ___	                                                          *)
(*      ||M||                                                             *)
(*      ||A||       A project by Andrea Asperti                           *)
(*      ||T||                                                             *)
(*      ||I||       Developers:                                           *)
(*      ||T||       A.Asperti, C.Sacerdoti Coen,                          *)
(*      ||A||       E.Tassi, S.Zacchiroli                                 *)
(*      \   /                                                             *)
(*       \ /        This file is distributed under the terms of the       *)
(*        v         GNU Lesser General Public License Version 2.1         *)
(*                                                                        *)
(**************************************************************************)

(* Esercizio 0 
   ===========
   
   Compilare i seguenti campi:
   
   Nome1: ...
   Cognome1: ...
   Matricola1: ...
   Account1: ...
   
   Nome2: ...
   Cognome2: ...
   Matricola2: ...
   Account2: ...

   Nota: salvate spesso per evitare la perdita del lavoro svolto in caso di
   crash dell'applicazione.

   Prima di abbandonare la postazione, dopo aver salvato e chiuso Matita,
   consegnare con il comando ``~sacerdot/logica1819/ConsegnaLogica NOME-DEL-VOSTRO-FILE''

*)



(* ATTENZIONE
   ==========
   
   Non modificare la seguente riga che carica la definizione di uguaglianza.
*)
include "logic/equality.ma".


(* Esercizio 1 
   ===========
   
   Definire il seguente linguaggio (o tipo) di espressioni riempiendo gli spazi.
   
   Expr :: "Zero" | "One" | "Minus" Expr | "Plus" Expr Expr | "Mult" Expr Expr 
*)
inductive Expr : Type ≝
| Zero: Expr
| One: …
| Minus: Expr → Expr
| Plus: Expr → Expr → Expr
| Mult: …
.

(* La prossima linea è un test per verificare se la definizione data sia
   probabilmente corretta. Essa definisce `test_Expr` come un'abbreviazione
   dell'espressione `Mult Zero (Plus (Minus One) Zero)`, verificando inoltre
   che l'espressione soddisfi i vincoli di tipo dichiarati sopra. Eseguitela. *)

definition test_Expr : Expr ≝ Mult Zero (Plus (Minus One) Zero).

(* Come esercizio, provate a definire espressioni che siano scorrette rispetto
   alla grammatica/sistema di tipi. Per esempio, scommentate la seguenti
   righe e osservate i messaggi di errore:
   
definition bad_Expr1 : Expr ≝ Mult Zero.
definition bad_Expr2 : Expr ≝ Mult Zero Zero Zero.
definition bad_Expr3 : Expr ≝ Mult Zero Plus.
*)

(* Esercizio 2 
   ===========
   
   Definire il linguaggio (o tipo) dei numeri naturali dove O
   (la lettera maiuscola O) rappresenta il numero naturale zero e
   (S n) rappresenta il successore del numero naturale n.

   nat ::= "O" | "S" nat   
*)

inductive nat : Type ≝
…

definition one : nat ≝ S O.
definition two : nat ≝ S (S O).
definition three : nat ≝ S (S (S O)).

(* Esercizio 3
   ===========
   
   Definire il linguaggio (o tipo) delle liste di numeri naturali.
   
   list_nat ::= "Nil" | "Cons" nat list_nat
   
   dove Nil sta per lista vuota e Cons aggiunge in testa un numero naturale a
   una lista di numeri naturali.
   
   Per esempio, `Cons O (Cons (S O) (Cons (S (S O)) Nil))` rappresenta la lista
   `[0,1,2]`.
*)

inductive list_nat : Type ≝
…

(* La seguente lista contiene 1,2,3 *)
definition one_two_three : list_nat ≝ Cons one (Cons two (Cons three Nil)).

(* Completate la seguente definizione di una lista contenente due uni. *)

definition one_one : list_nat ≝ ….

(* Esercizio 4
   ===========
   
   Definire il linguaggio degli alberi binari (= dove ogni nodo che non è una
   foglia ha esattamente due figli) le cui foglie siano numeri naturali.
   
   tree_nat ::= "Leaf" nat | "Node" tree_nat tree_nat
*)

inductive tree_nat : Type ≝
…

(* Il seguente albero binario ha due foglie, entrambe contenenti uni. *)
definition one_one_tree : tree_nat ≝ Node (Leaf one) (Leaf one).

(* Definite l'albero       /\
                          0 /\
                           1  2  *)
definition zero_one_two_tree : tree_nat ≝
 ….

(* Esercizio 5
   ===========
   
   Osservare come viene definita la somma di due numeri in Matita per
   ricorsione strutturale sul primo.
   
   plus O m = m
   plus (S x) m = S (plus x m) *)

let rec plus n m on n ≝
 match n with
 [ O ⇒ m
 | S x ⇒ S (plus x m) ].

(* Provate a introdurre degli errori nella ricorsione strutturale. Per esempio,
   omettete uno dei casi o fate chiamate ricorsive non strutturali e osservate
   i messaggi di errore di Matita. *)

(* Per testare la definizione, possiamo dimostrare alcuni semplici teoremi la
   cui prova consiste semplicemente nell'effettuare i calcoli. *)
theorem test_plus: plus one two = three.
done. qed.

(* Esercizio 6
   ===========

   Completare la seguente definizione, per ricorsione strutturale, della
   funzione `size_E` che calcola la dimensione di un'espressione in numero
   di simboli.
   
   size_E Zero = 1
   size_E One = 1
   size_E (Minus E) = 1 + size_E E
   ... 
*)
let rec size_E E on E ≝
 match E with
  [ Zero ⇒ one 
  | One ⇒ …
  | Minus E ⇒ plus one (size_E E)
  | Plus E1 E2 ⇒ …
  …
  ]
.

theorem test_size_E : size_E test_Expr = plus three three.
done. qed.

(* Esercizio 7
   ===========
   
   Definire in Matita la funzione `sum` che, data una `list_nat`, calcoli la
   somma di tutti i numeri contenuti nella lista. Per esempio,
   `sum one_two_three` deve calcolare sei.
*)

…

theorem test_sum : sum one_two_three = plus three three.
done. qed.

(* Esercizio 8
   ===========
   
   Definire la funzione `rightmost` che, dato un `tree_nat`, restituisca il
   naturale contenuto nella foglia più a destra nell'albero. *)

…

theorem test_rightmost : rightmost zero_one_two_tree = two.
done. qed.

(* Esercizio 9
   ===========
   
   Definire la funzione binaria `append` che, date due `list_nat` restituisca la
   `list_nat` ottenuta scrivendo in ordine prima i numeri della prima lista in
   input e poi quelli della seconda.
   
   Per esempio, `append (Cons one (Cons two Nil)) (Cons 0 Nil)` deve restituire
   `Cons one (Cons two (Cons 0 nil))`. *)
…

theorem test_append : append (Cons one Nil) (Cons two (Cons three Nil)) = one_two_three.
done. qed.

(* Esercizio 10
   ============
   
   Definire la funzione `visit` che, dato un `tree_nat`, calcoli la `list_nat`
   che contiene tutti i numeri presenti nelle foglie dell'albero in input,
   nell'ordine in cui compaiono nell'albero da sinistra a destra.
   
   Suggerimento: per definire tree_nat usare la funzione `append` già definita
   in precedenza.

   Esempio: `visit zero_one_two_tree = Cons O (Cons one (Cons two Nil))`.    
*)
…

theorem test_visit : visit zero_one_two_tree = Cons O (Cons one (Cons two Nil)).
done. qed.
