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

(* Istruzioni: 

     http://mowgli.cs.unibo.it/~tassi/exercise-natural_deduction.html 

*)

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

*)



include "didactic/support/natural_deduction.ma".

theorem EM: ∀A:CProp. A ∨ ¬ A.
(* Il comando assume è necessario perchè dimostriamo A∨¬A
   per una A generica. *)
assume A: CProp.
(* Questo comando inizia a disegnare l'albero *)
apply rule (prove (A ∨ ¬A));
(* qui inizia l'albero, eseguite passo passo osservando come
   si modifica l'albero. *)
apply rule (RAA [H] (⊥)).
apply rule (¬#e (¬(A ∨ ¬A)) (A ∨ ¬A));
	[ apply rule (discharge [H]).
	| apply rule (⊥#e (⊥));
	  apply rule (¬#e (¬¬A) (¬A));
	   [ apply rule (¬#i [K] (⊥)).
       apply rule (¬#e (¬(A ∨ ¬A)) (A ∨ ¬A));
	      [ …
	      | …
	      ]
	   | …
	   ]
	]
qed.

theorem ex1 : (C∧G ⇒ E) ⇒ (¬L ⇒ E∨C) ⇒ G ∨ L ⇒ ¬L ⇒ E.
apply rule (prove ((C∧G ⇒ E) ⇒ (¬L ⇒ E∨C) ⇒ G ∨ L ⇒ ¬L ⇒ E));
…
qed.

theorem ex2 : (A∧¬B ⇒ C) ⇒ (B∧D ⇒ C) ⇒ (D ⇒ A) ⇒ D ⇒ C.
apply rule (prove ((A∧¬B ⇒ C) ⇒ (B∧D ⇒ C) ⇒ (D ⇒ A) ⇒ D ⇒ C));
…
qed.

(* Per dimostrare questo teorema torna comodo il lemma EM
   dimostrato in precedenza. *)
theorem ex3: (F ⇒ G∨E) ⇒ (G ⇒ ¬L∨E) ⇒ (L⇒F) ⇒ L ⇒ E.
apply rule (prove ((F ⇒ G∨E) ⇒ (G ⇒ ¬L∨E) ⇒ (L⇒F) ⇒ L ⇒ E));
…
qed.

theorem ex4: ¬(A∧B) ⇒ ¬A∨¬B.
apply rule (prove (¬(A∧B) ⇒ ¬A∨¬B));
…
qed.

theorem ex5: ¬(A∨B) ⇒ (¬A ∧ ¬B).
apply rule (prove (¬(A∨B) ⇒ (¬A ∧ ¬B)));
…
qed.

theorem ex6: ¬A ∧ ¬B ⇒ ¬(A∨B).
apply rule (prove (¬A ∧ ¬B ⇒ ¬(A∨B)));
…
qed.

theorem ex7: ((A ⇒ ⊥) ⇒ ⊥) ⇒ A.
apply rule (prove (((A ⇒ ⊥) ⇒ ⊥) ⇒ A));
…
qed.

