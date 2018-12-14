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

   Inviare la soluzione via mail a giulio.pellitta2@unibo.it con il subject
   "laboratorio151215".
*)

include "didactic/support/natural_deduction.ma".

axiom EM: ∀A:CProp. A ∨ ¬ A.

(* Per risolvere alcuni teorema torna comodo il lemma EM.
   Vedi istruzioni nel file HTML su come invocarlo. *)

theorem ex130116 : (¬C ⇒ B) ⇒ ¬(B ∧ ¬A) ⇒ C ∨ A.
apply rule (prove ((¬C ⇒ B) ⇒ ¬(B ∧ ¬A) ⇒ C ∨ A));
…
qed.

theorem ex130221 : ¬(¬B ∧ ¬C) ⇒ (¬A ⇒ ¬C) ⇒ ¬B ⇒ A.
apply rule (prove (¬(¬B ∧ ¬C) ⇒ (¬A ⇒ ¬C) ⇒ ¬B ⇒ A));
…
qed.

theorem ex130607 : (¬A ∨ C) ⇒ (D ⇒ ¬A) ⇒ (B ⇒ D ∨ ¬C) ⇒ ¬A ∨ ¬B.
apply rule (prove ((¬A ∨ C) ⇒ (D ⇒ ¬A) ⇒ (B ⇒ D ∨ ¬C) ⇒ ¬A ∨ ¬B));
…
qed.

theorem ex130705 : (A ∧ C ⇒ B) ⇒ ¬B ∨ ¬A ⇒ (C ⇒ A) ⇒ ¬C.
apply rule (prove ((A ∧ C ⇒ B) ⇒ ¬B ∨ ¬A ⇒ (C ⇒ A) ⇒ ¬C));
…
qed.

theorem ex150702mod : ((A ∨ ¬C) ⇒ D ∧ B) ⇒ ¬A ⇒ (¬E ⇒ ¬B) ⇒ ¬E ⇒ C.
apply rule : ((A ∨ ¬C) ⇒ D ∧ B) ⇒ ¬A ⇒ (¬E ⇒ ¬B) ⇒ ¬E ⇒ C.
…
qed.
