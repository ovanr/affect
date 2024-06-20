
(* handler.v *)

(* This file defines the Haffel handlers. *)

From iris.algebra Require Import ofe.
From iris.base_logic Require Export lib.iprop .
From iris.program_logic Require Export language.
From iris.proofmode Require Import base tactics classes.
From iris.heap_lang Require Export locations.

(* Hazel language *)
From hazel.language Require Export eff_lang.
From hazel.program_logic Require Import weakest_precondition 
                                        basic_reasoning_rules
                                        deep_handler_reasoning
                                        tactics
                                        shallow_handler_reasoning
                                        state_reasoning.

From affect.lib Require Export base logic.

Notation operation := (string).
Definition effect (op : string) := (LitV (LitStr op)).

Definition rec_perform : val := (λ: "x", "x")%V.

Notation "'perform:' op e" := (rec_perform (Do MS (Pair (effect op)  e%E)))
  (at level 200, op at level 1, e at level 200,
   format "'[' 'perform:'  op  e ']'") : expr_scope.

Definition assert : val := (λ: "x", if: "x" then #() else #() #())%V.
Notation "'assert:' e" := (assert e)%E
  (at level 75, format "'[' 'assert:'  e ']'") : expr_scope.

Definition shandler (m : mode) : val := (
  rec: "H" "e" "op'" "h" "r" :=
    shallow-try: "e" #() with
      effect (λ: "x" "k",
          let: "op" := Fst "x" in
          let: "x" := Snd "x" in
          if: ("op" = "op'") then
            "h" "x" (match m with
                          OS => let: "l" := ref #true in 
                                (λ: "x", assert: (Load "l") ;; "l" <- #false ;; "k" "x")%E
                        | MS => "k"
                        end)
          else
            (λ: "y", "H" (λ: <>, "k" "y") "op'" "h" "r") (doₘ: ("op", "x"))
      )%E
      | return "r"
  end
)%V.

Arguments shandler : simpl never.

Definition SHandler (m : mode) (e : expr) (op : operation) (h r : expr) : expr :=
  shandler m (λ: <>, e)%E (effect op) h r.

Definition SHandlerV (m : mode) (e : expr) (op : operation) (h r : expr) : expr :=
  shandler m (λ: <>, e)%V (effect op) h r.

Notation "'shandle[' m ']:' e 'by' op '=>' h | 'ret' '=>' r 'end'" :=
  (SHandler m e%E op h%E r%E)
  (e, op, h, r at level 200) : expr_scope.

Notation "'shandle:' e 'by' op '=>' h | 'ret' '=>' r 'end'" :=
  (SHandler OS e%E op h%E r%E)
  (e, op, h, r at level 200) : expr_scope.

Notation "'shandleₘ:' e 'by' op '=>' h | 'ret' '=>' r 'end'" :=
  (SHandler MS e%E op h%E r%E)
  (e, op, h, r at level 200) : expr_scope.

Definition handler (m : mode) : val := (
  λ: "e" "op'" "h" "r",
    deep-try: "e" #() with
      effect (λ: "x" "k", 
          let: "op" := Fst "x" in
          let: "x" := Snd "x" in
          if: ("op" = "op'") then
            "h" "x" (match m with
                        OS => let: "l" := ref #true in 
                              (λ: "x", assert: (Load "l") ;; "l" <- #false ;; "k" "x")%E
                      | MS => "k"
                      end)
          else
            "k" (doₘ: ("op", "x"))
      )
    | return "r" 
    end
)%V.
            
Arguments handler : simpl never.

Definition Handler (m : mode) (e : expr) (op : operation) (h r : expr) : expr :=
  handler m (λ: <>, e)%E (effect op) h r.

Definition HandlerV (m : mode) (e : expr) (op : operation) (h r : expr) : expr :=
  handler m (λ: <>, e)%V (effect op) h r.

Notation "'handle[' m ']:' e 'by' op '=>' h | 'ret' '=>' r 'end'" :=
  (Handler m e%E op h%E r%E)
  (e, op, h, r at level 200) : expr_scope.

Notation "'handle:' e 'by' op '=>' h | 'ret' '=>' r 'end'" :=
  (Handler OS e%E op h%E r%E)
  (e, op, h, r at level 200) : expr_scope.

Notation "'handleₘ:' e 'by' op '=>' h | 'ret' '=>' r 'end'" :=
  (Handler MS e%E op h%E r%E)
  (e, op, h, r at level 200) : expr_scope.

Definition handler2 (m : mode) : val := (
  λ: "e" "op1" "h1" "op2" "h2" "r",
    deep-try: "e" #() with
        effect (λ: "x" "k", 
            let: "op" := Fst "x" in
            let: "x" := Snd "x" in
            if: ("op" = "op1") then
                "h1" "x" (match m with
                            OS => let: "l" := ref #true in 
                                  (λ: "x", assert: (Load "l") ;; "l" <- #false ;; "k" "x")%E
                          | MS => "k"
                          end)
            else
              if: ("op" = "op2") then
                "h2" "x" (match m with
                            OS => let: "l" := ref #true in 
                                  (λ: "x", assert: (Load "l") ;; "l" <- #false ;; "k" "x")%E
                          | MS => "k"
                          end)
              else
                "k" (doₘ: ("op", "x"))
        )
        | return "r" 
    end
)%V.
            
Arguments handler2 : simpl never.

Definition Handler2 (m : mode) (e : expr) (op1 op2 : operation) (h1 h2 r : expr) : expr :=
  handler2 m (λ: <>, e)%E (effect op1) h1 (effect op2) h2 r.

Definition Handler2V (m : mode) (e : expr) (op1 op2 : operation) (h1 h2 r : expr) : expr :=
  handler2 m (λ: <>, e)%V (effect op1) h1 (effect op2) h2 r.

Notation "'handle2[' m ']:' e 'by' op1 '=>' h1 | op2 '=>' h2 | 'ret' '=>' r 'end'" :=
  (Handler2 m e%E op1 op2 h1%E h2%E r%E)
  (e, op1, h1, op2, h2, r at level 200) : expr_scope.

Notation "'handle2:' e 'by' op1 '=>' h1 | op2 '=>' h2 | 'ret' '=>' r 'end'" :=
  (Handler2 OS e%E op1 op2 h1%E h2%E r%E)
  (e, op1, h1, op2, h2, r at level 200) : expr_scope.

Notation "'handle2ₘ:' e 'by' op1 '=>' h1 | op2 '=>' h2 | 'ret' '=>' r 'end'" :=
  (Handler2 MS e%E op1 op2 h1%E h2%E r%E)
  (e, op1, h1, op2, h2, r at level 200) : expr_scope.
