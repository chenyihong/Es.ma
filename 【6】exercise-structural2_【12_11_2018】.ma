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

   Prima di abbandonare la postazione consegnare il file usando il solito
   comando   ~sacerdot/logica1819/ConsegnaLogica NOMEFILE.ma
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
| One: Expr
| Minus: Expr → Expr
| Plus: Expr → Expr → Expr
| Mult: Expr → Expr → Expr
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
   
   Definire il linguaggio (o tipo) dei numeri naturali.

   nat ::= "O" | "S" nat   
*)

inductive nat : Type ≝
 O : nat
 | S : nat → nat. 

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
   `[1,2,3]`.
*)

inductive list_nat : Type ≝
 Nil : list_nat
 | Cons : nat → list_nat → list_nat. 

(* La seguente lista contiene 1,2,3 *)
definition one_two_three : list_nat ≝ Cons one (Cons two (Cons three Nil)).

(* Completate la seguente definizione di una lista contenente due uni. *)

definition one_one : list_nat ≝ Cons one (Cons one Nil).

(* Esercizio 4
   ===========
   
   Definire il linguaggio degli alberi binari (= dove ogni nodo che non è una
   foglia ha esattamente due figli) le cui foglie siano numeri naturali.
   
   tree_nat ::= "Leaf" nat | "Node" nat nat
*)

inductive tree_nat : Type ≝
 Leaf : nat → tree_nat
 | Node : tree_nat → tree_nat → tree_nat. 

(* Il seguente albero binario ha due foglie, entrambe contenenti uni. *)
definition one_one_tree : tree_nat ≝ Node (Leaf one) (Leaf one).

(* Definite l'albero       /\
                          0 /\
                           1  2  *)
definition zero_one_two_tree : tree_nat ≝
  Node (Leaf O) (Node (Leaf one) (Leaf two)) .

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
  | One ⇒ one
  | Minus E ⇒ plus one (size_E E)
  | Plus E1 E2 ⇒ plus one (plus (size_E E1) (size_E E2))
  
  | Mult E1 E2 ⇒ plus one (plus (size_E E1) (size_E E2))
  
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


let rec sum L on L ≝
 match L with
 [ Nil ⇒ O
 | Cons N TL ⇒ plus N (sum TL)
 ].


theorem test_sum : sum one_two_three = plus three three.
done. qed.

(* Esercizio 8
   ===========
   
   Definire la funzione `rightmost` che, dato un `tree_nat`, restituisca il
   naturale contenuto nella foglia più a destra nell'albero. *)


let rec rightmost T on T ≝
 match T with
 [ Leaf n ⇒ n
 | Node T1 T2 ⇒ rightmost T2
 ].


theorem test_rightmost : rightmost zero_one_two_tree = two.
done. qed.

(* Esercizio 9
   ===========
   
   Definire la funzione binaria `append` che, date due `list_nat` restituisca la
   `list_nat` ottenuta scrivendo in ordine prima i numeri della prima lista in
   input e poi quelli della seconda.
   
   Per esempio, `append (Cons one (Cons two Nil)) (Cons 0 Nil)` deve restituire
   `Cons one (Cons two (Cons 0 nil))`. *)

let rec append L1 L2 on L1 ≝
 match L1 with
 [ Nil ⇒ L2
 | Cons HD TL ⇒ Cons HD (append TL L2)
 ].


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

let rec visit T on T ≝
 match T with
 [ Leaf N ⇒ Cons N Nil
 | Node T1 T2 ⇒ append (visit T1) (visit T2)
 ].

theorem test_visit : visit zero_one_two_tree = Cons O (Cons one (Cons two Nil)).
done. qed.

(* Esercizio 11
   ============
   
   Definire in Matita la funzione `prod` che, dati due numeri
   naturali, calcoli il loro prodotto.
   
   prod O m = O
   prod (S n) m = plus (prod n m) m
   
   Suggerimento: riguardare la funzione `plus` definita sopra, che
   è definita in maniera simile.
*)

let rec prod n m on n ≝
 …


(* Esercizio 12
   ============
   
   Definire il tipo dei booleani, descritto dalla grammatica:

   bool ::= "true" | "false"
*)

inductive bool : Type ≝ …

(* Esercizio 13
   ============
   
   Definire la funzione `bool_and`, che implementa l'omonimo
   operatore booleano.
   
   La specifica e' la seguente: `and x y` deve restituire `true`
   se entrambi `x` e `y` sono `true`, altrimenti restituire `false`.

*)

let rec bool_and x y on x ≝
 …

(* Testa la funzione `bool_and` con i seguenti: *)
theorem test_and1: bool_and true true = true. done. qed.
theorem test_and2: bool_and true false = false. done. qed.
theorem test_and3: bool_and false true = false. done. qed.
theorem test_and4: bool_and false false = false. done. qed.

(* 
   La seguente funzione `if_then_else` implementa il costrutto
   "if CONDIZIONE then BLOCCO1 else BLOCCO2" presente in
   moltissimi linguaggi di programmazione. 
   
   Il corpo della funzione e' ovvio, ma la prima riga della dichiarazione
   richiede una feature di Matita piu' avanzata, cioe' il polimorfismo
   di tipi.
   Le righe sotto la definizione invece introducono una notazione sintattica
   per utilizzare `if_then_else` piu' comodamente.
   
   Non e' necessario capire queste due definizioni;
   e' sufficiente sapere che l'espressione `if b then x else y`
   restituisce `x` se `b` e' `true`, `y` se `b` e' `false`.
   
   Vedi anche gli esempi sotto.
*)

let rec if_then_else (A:Type[0]) b (x:A) (y:A) on b ≝
 match b with
 [ true ⇒ x
 | false ⇒ y ].

notation "hvbox('if' A break 'then' B break 'else' C)" non associative
 with precedence 30 for @{if_then_else ? $A $B $C}.

(* Esempi:
   - `if true then one else two` restituisce `one`
   - `if false then one else two` restituisce `two`
*)

(* La seguente funzione `len` implementa il predicato
   "minore o uguale di" sui numeri naturali. Prende in input due
   numeri naturali, e restituisce `true` se il primo e' minore
   o uguale del secondo, `false` altrimenti. *)

let rec len n m on n ≝
 match n with
 [ O ⇒ true
 | S n ⇒ match m with [ O ⇒ false | S m ⇒ len n m ]
 ].
 
(* Esempi:
   - `len 2 3` restituisce `true`
   - `len 4 1` restituisce `false`
*)

(* Esercizio 14
   ============
    
   Definire la funzione `insert` che, dato un numero naturale
   e una lista ordinata (in maniera non decrescente) di numeri naturali,
   inserisce il primo nella seconda in modo da ottenere ancora una lista ordinata. 
  
   Suggerimento: usare la notazione `if ... then ... else` definita sopra.
*)


let rec insert n l on l ≝
…

(* Prova la funzione `insert` con `test_insert`. *)
(* Prima alcune definizioni preliminari: *)
definition four : nat ≝ S (S (S (S O))).
(* `one_two_four` rappresenta la lista [1, 2, 4] *)
definition one_two_four : list_nat ≝ Cons one (Cons two (Cons four Nil)).
(* `one_two_three_four` rappresenta la lista [1, 2, 3, 4] *)
definition one_two_three_four : list_nat ≝
  Cons one (Cons two (Cons three (Cons four Nil))).
(* Test: insert 3 [1, 2, 4] = [1, 2, 3, 4] *)
theorem test_insert : insert three one_two_four = one_two_three_four.
  done. qed.

(* Esercizio 15
   ============

   Definire la funzione `insertion_sort` che, data una lista di naturali,
   restituisce la lista contenente gli stessi elementi, ma ordinati in
   ordine non decrescente.

   Suggerimento: procedere per ricorsione strutturale e utilizzare la
   funzione `insert` definita sopra ove necessario. L'algoritmo che otterrete
   va sotto il nome di insertion_sort ed è quello normalmente utilizzato
   nei giochi di carte per mantenere ordinate le carte in mano mentre si
   continua a pescare dal mazzo.
*)

…

(* Prova la funzione `insertion_sort` con `test_sort`. *)
(* `four_two_one_three` rappresenta la lista [4, 2, 1, 3] *)
definition four_two_one_three : list_nat ≝
  Cons four (Cons two (Cons one (Cons three Nil))).
(* Test: insertion_sort [4, 2, 1, 3] = [1, 2, 3, 4] *)
theorem test_sort :
 insertion_sort four_two_one_three = one_two_three_four.
  done. qed.

(* Esercizio 16
   ============

   Definire la funzione `cerca` che, dati un naturale e una lista
   ordinata di naturali, restituisce true se e solo se il naturale compare
   nella lista data.

   Suggerimento: usare la notazione `if ... then ... else ...` e 
   la funzione `len` definita sopra. Notate che la funzione len può anche
   essere utilizzata in un certo modo per determinare se due numeri naturali
   sono uguali.
*)

…

(* Testa la funzione `cerca` con `test_cerca1` e `test_cerca2`: *)
theorem test_cerca1 : cerca three one_two_four = false.
  done. qed.
theorem test_cerca2 : cerca three one_two_three = true.
  done. qed.

(* Esercizio 17
   ============

   Definire una funzione `sub` che, data una lista L
   e una lista ordinata L2, dica se tutti gli elementi di L sono in L2.

   Suggerimento: usare la notazione `if ... then ... else ...` e
    la funzione `cerca` definite sopra.
*)

…

(* Testa la funzione `sub` con `test_sub1` e `test_sub2` *)
(* `list_repeats` rappresenta la lista [4, 2, 1, 3, 1, 2, 3] *)
definition list_repeats : list_nat ≝
  Cons four (Cons two (Cons one (Cons three one_two_three))).
theorem test_sub1 : sub list_repeats one_two_three_four = true.
  done. qed.
theorem test_sub2 : sub list_repeats one_two_four = false.
  done. qed.

(* Esercizio 18
   ============
   
   Gli alberi binari di ricerca (BST, per Boolean Search Trees)
   sono strutture dati usate per implementare efficientemente
   funzioni che associno a dei valori chiamati chiavi degli altri valori
   chiamati dati. L'insieme di tutte le chiavi è il dominio della funzione
   mentre l'insieme dei dati ne è il codominio.
   
   I BST sono alberi binari, e quindi consistono di nodi e foglie.
   Le foglie non hanno figli, contengono un dato detto chiave e
   il valore a esso associato.
   I nodi hanno un sott-albero destro, una chiave e un sotto-albero sinistro.
   
   La proprieta' che caratterizza i BST e' la seguente:
   per ogni nodo dell'albero, la chiave di quel nodo e' maggiore o uguale alle
   chiavi di tutti i figli sinistri del nodo, e minore delle chiavi di
   tutti i figli destri.
   Ad esempio, il seguente e' un BST:
                                       10
                                      /  \
                                     2   12,true
                                    /  \
                                   /    \  
                               1,true   7,false
   e rappresenta la funzione 1 ↦ true, 7 ↦ false, 12 ↦ true.
   
   Il seguente albero invece non e' un BST, perche' il nodo di chiave 11
   è a sinistra di quello di chiave 10:
                                             10
                                            /  \
                                           2   12,false
                                         /  \
                                        /    \
                                    1,true  11,true
   
   Definire il tipo dei BST con chiavi numeri naturali e valori booleani.
   La grammatica e': 
                        bst ::= "Leaf" nat bool | "Node" bst nat bst
   dove nat e' il tipo delle chiavi, `bool` il tipo dei valori,
   e i due argomenti in `Node` di tipo `bst` sono rispettivamente il figlio
   sinistro e destro del nodo. La grammatica accetterà sia veri alberi BST,
   che alberi BST che non rispettano la proprietà di ordinamento delle chiavi.
*)

…

(* Esercizio 19
   ============

   Definire il tipo `option`, che rappresenta o la presenza di un valore
   booleano b, indicata come (Some b), oppure la sua assenza, indicata con
   None.

   La grammatica e':
                       option ::= "None" | "Some" bool
                       
   I dati option vengono utilizzati come valori di ritorno delle funzioni
   che, in certi casi, non saprebbero quale booleano restituire perchè
   l'input è non corretto o perchè l'output cercato è assente (None).
*)

…


(* Esercizio 20
   ============

   Definire la funzione `cerca_bst` che, dati una chiave `n` e un bst `t`,
   cerca il valore associato alla chiave `n` in `t`. Se tale valore esiste
   ed è il booleano `b`, allora la funzione restituirà `Some b`. Altrimenti
   restituirà `None`. 
   
   Esempio: supponiamo di voler cercare la chiave 7 nel bst fornito
    nell'esercizio 18. Si parte dalla radice e si confronta 7 con
    il dato nella radice, cioe' 10. 7 e' minore o uguale a 10,
    quindi per la proprietà dei bst 7 è presente nell'albero sse è presente
    nel figlio sinistro della radice. La ricerca di 7 pertanto deve proseguire
    ricorsivamente in tale sotto-albero. Nel caso delle foglie è necessario
    controllare se la chiave cercata è uguale a quella della foglia.

   Suggerimento: usare `if ... then ... else ...`, `len` e bool_and definite
   in precedenza.
*)

…

(* Testa `cerca_bst` con `test_cerca_bst1`-`test_cerca_bst3` *)
(* `example_bst` rappresenta il bst di esempio fornito nella descrizione
   dell'esercizio 18. Sono stati aggiunti dei valori booleani alle chiavi 
   naturali ( 1 -> false , 7 -> false, 12 -> true ) *)
definition seven  : nat ≝ S (S (S four)).
definition ten    : nat ≝ S (S (S seven)).
definition twelve : nat ≝ S (S ten).
definition example_bst : bst ≝
 BNode
  (BNode (BLeaf one false) two (BLeaf seven false))
  ten
  (BLeaf twelve true).
theorem test_cerca_bst1 : cerca_bst one example_bst = Some false.
 done. qed.
theorem test_cerca_bst2 : cerca_bst twelve example_bst = Some true.
 done. qed.
theorem test_cerca_bst3 : cerca_bst four example_bst = None.
 done. qed.