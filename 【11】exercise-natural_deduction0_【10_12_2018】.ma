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

 Poichè digitare in Matita esercizi di deduzione naturale è un'operazione
 lenta e poichè comunque è bene avere prima la prova completa su carta,
 il punteggio verrà attribuito dal docente o dall'assistente correggendo le
 prove cartacee. Potete comunque usare Matita come strumento di auto-correzione.

*)



include "didactic/support/natural_deduction.ma".

(* Il seguente esercizio è risolto.
   1. eseguite passo passo l'esercizio dopo aver
      attivato (con F3 + icona Home + always-on-top)
      la finestra che visualizza l'albero di deduzione
      naturale. Cercate di capire come funzionano i vari
      comandi.
   2. introducete un errore nell'albero (p.e. sostituite
      una formula in una regola con un'altra) e osservate
      come una parte dell'albero viene segnata come
      errata (in rosso) *)

theorem esercizio_risolto: ((A ∨ C) ⇒ B) ⇒ ¬B ⇒ ¬A.
apply rule (prove ((A ∨ C) ⇒ B) ⇒ ¬B ⇒ ¬A).
 apply rule (⇒#i [h] (¬B ⇒ ¬A));
 apply rule (⇒#i [nb] (¬A));
 apply rule (¬#i [a] (⊥));
 apply rule (¬#e (¬B) (B));
	[ apply rule (discharge [nb]);
	| apply rule (⇒#e (A∨C⇒B) (A∨C));
	  [ apply rule (discharge [h]);
	  | apply rule (∨#i_l (A));
      apply rule (discharge [a]);
	  ]
	]
qed.

(* Tutti gli esercizi che seguono sono dimostrabili sia
   in logica classica che in logica intuizionista, ovvero
   non richiedono l'uso della regola RAA *)

theorem ex1: (A ⇒ ⊥) ∧ (¬B) ⇒ A∨B ⇒ ⊥.
apply rule (prove ((A ⇒ ⊥) ∧ (B ⇒ ⊥) ⇒ A∨B ⇒ ⊥));
…
qed.

theorem ex1: (A ⇒ ⊥) ∧ (B ⇒ ⊥) ⇒ A∨B ⇒ ⊥.
apply rule (prove ((A ⇒ ⊥) ∧ (B ⇒ ⊥) ⇒ A∨B ⇒ ⊥));
…
qed.

theorem ex2: A ∧ (B ∨ C) ⇒ (A ∧ B) ∨ (A ∧ C).
apply rule (prove (A ∧ (B ∨ C) ⇒ (A ∧ B) ∨ (A ∧ C)));
…
qed.

theorem ex3: (A ⇒ B ∨ C) ⇒ (B ⇒ ⊥) ⇒ (C ⇒ ⊥) ⇒ (A ⇒ ⊥).
apply rule (prove ((A ⇒ B ∨ C) ⇒ (B ⇒ ⊥) ⇒ (C ⇒ ⊥) ⇒ (A ⇒ ⊥)));
…
qed.

theorem ex4: (A ∧ B ⇒ C ∨ D) ⇒ (C ⇒ D) ⇒ B ⇒ A ⇒ D.
apply rule (prove ((A ∧ B ⇒ C ∨ D) ⇒ (C ⇒ D) ⇒ B ⇒ A ⇒ D));
…
qed.

(* Questo e' preso da un compito *)
theorem ex5 : (C∧G ⇒ E) ⇒ (¬L ⇒ E∨C) ⇒ G ∨ L ⇒ (L ⇒ ⊥) ⇒ E.
apply rule (prove ((C∧G ⇒ E) ⇒ (¬L ⇒ E∨C) ⇒ G ∨ L ⇒ (L ⇒ ⊥) ⇒ E));
…
qed.

(* Questo e' preso da un compito *)
theorem ex6: (F ⇒ G∨E) ⇒ (G ⇒ (L ⇒ ⊥)∨E) ⇒ (L⇒F) ⇒ L ⇒ E.
apply rule (prove ((F ⇒ G∨E) ⇒ (G ⇒ (L ⇒ ⊥)∨E) ⇒ (L⇒F) ⇒ L ⇒ E));
…
qed.
