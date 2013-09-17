(*formal semantics of brainfuck*)

theory brainfuck_semantics
imports Main
  "~~/src/HOL/Word/Word"
begin

type_synonym byte = "8 word"
lemma "(256 :: byte) = 0" by simp


datatype bf_cmd = BF_RIGHT  --">, increment the data pointer (to point to the next cell to the right)." 
                | BF_LEFT  --"<, decrement the data pointer (to point to the next cell to the left)."
                | BF_PLUS  --"+, increment the byte at the data pointer."
                | BF_MINUS  --"-, decrement the byte at the data pointer."
                | BF_OUTPUT  --"., output the byte at the data pointer."
                | BF_INPUT  --",, accept one byte of input, storing its value in the byte at the data pointer."
                | BF_LOOPSTART   --"[, while data pointer is not zero"
                | BF_LOOPEND --"]"


datatype tape = Tape "byte list" byte    "byte list"
--"                   left       current right"
--" left is ordered in reverse"
--"tape is (rev left)@[current]@right"


datatype outp = Outp "byte list"
datatype inp = Inp "byte list"
datatype state = Error | Normal tape inp outp

(*not sure if this syntax annotation awakens daemons*)
datatype tape_visual = B byte ("_\<^sub>b\<^isub>y\<^isub>t\<^isub>e")| XR ("\<longrightarrow>\<^isub>p\<^isub>c")| XL ("\<longleftarrow>\<^isub>p\<^isub>c")

fun print_state :: "state \<Rightarrow> (tape_visual list \<times> byte list \<times> byte list) option" where
  "print_state Error = None" |
  "print_state (Normal (Tape lt c rt) (Inp inp) (Outp outp)) = Some ((map B (rev lt))@[XR]@[B c]@[XL]@(map B rt), inp, rev outp)"


inductive eval_bf :: "bf_cmd list \<Rightarrow> state \<Rightarrow> state \<Rightarrow> bool"  where
init:  "s = s' \<Longrightarrow> eval_bf [] s s'" |
       "eval_bf [BF_RIGHT] (Normal (Tape lt c []) inp outp)       (Normal (Tape (c#lt) 0 []) inp outp)" |
       "eval_bf [BF_RIGHT] (Normal (Tape lt c (rt#rts)) inp outp) (Normal (Tape (c#lt) rt rts) inp outp)" |
       "eval_bf [BF_LEFT]  (Normal (Tape [] c rt) inp outp)       Error"  |
       "eval_bf [BF_LEFT]  (Normal (Tape (lt#lts) c rt) inp outp) (Normal (Tape lts lt (c#rt)) inp outp)" |
       "eval_bf [BF_PLUS]  (Normal (Tape lt c rt) inp outp)       (Normal (Tape lt (c + 1) rt) inp outp)" |
       "eval_bf [BF_MINUS] (Normal (Tape lt c rt) inp outp)       (Normal (Tape lt (c - 1) rt) inp outp)" |
       "eval_bf [BF_OUTPUT] (Normal (Tape lt c rt) inp (Outp outp))     (Normal (Tape lt c rt) inp (Outp (c#outp)))" |
       "eval_bf [BF_INPUT]  (Normal (Tape lt _ rt) (Inp []) outp)       (Normal (Tape lt 0 rt) (Inp []) outp)" |
       "eval_bf [BF_INPUT]  (Normal (Tape lt _ rt) (Inp (i#is)) outp)   (Normal (Tape lt i rt) (Inp is) outp)" |
seq:  "eval_bf code s s' \<Longrightarrow> eval_bf code' s' s'' \<Longrightarrow> eval_bf (code@code') s s''" |
whileTrue:      "c \<noteq> 0 \<Longrightarrow> eval_bf code (Normal (Tape lt c rt) inp outp) (Normal (Tape lt'' c'' rt'') inp'' outp'') \<Longrightarrow>
                  eval_bf ([BF_LOOPSTART]@code@[BF_LOOPEND])  (Normal (Tape lt'' c'' rt'') inp'' outp') (Normal (Tape lt' c' rt') inp' outp') \<Longrightarrow>
        eval_bf ([BF_LOOPSTART]@code@[BF_LOOPEND])  (Normal (Tape lt c rt) inp outp)       (Normal (Tape lt' c' rt') inp' outp')" |
whileFalse:      "c = 0 \<Longrightarrow> 
        eval_bf ([BF_LOOPSTART]@code@[BF_LOOPEND])  (Normal (Tape lt c rt) inp outp)       (Normal (Tape lt c rt) inp outp)" 


inductive_cases b_bf_init: "eval_bf [] s s'"
thm b_bf_init
inductive_cases b_bf_while: "eval_bf (BF_LOOPSTART # code @ [BF_LOOPEND]) s s'"
thm b_bf_while

lemma subst1: "cmd#code' = [cmd]@code'" by (metis append_Cons append_Nil)

lemma seq': "eval_bf [cmd] s s' \<Longrightarrow> eval_bf code' s' s'' \<Longrightarrow> eval_bf (cmd#code') s s''"
apply(subst subst1)
apply(rule eval_bf.seq)
by(auto)

lemma seq_while_split: "eval_bf ([BF_LOOPSTART]@code@[BF_LOOPEND]) s si \<Longrightarrow> eval_bf (code') si s'
   \<Longrightarrow> eval_bf ([BF_LOOPSTART]@code@[BF_LOOPEND]@code') s s'"
  apply(simp)
  apply(rule eval_bf.seq[of "[BF_LOOPSTART]@code@[BF_LOOPEND]" s si "code'", simplified])
by(auto intro: eval_bf.intros)


lemma "eval_bf [] (Normal (Tape [] 0 []) inp outp) (Normal (Tape [] 0 []) inp outp)"
  by(simp add: eval_bf.intros)

lemma "eval_bf [BF_PLUS, BF_OUTPUT] (Normal (Tape [] 0 []) inp (Outp [])) (Normal (Tape [] 1 []) inp (Outp [1]))"
  apply(rule seq')
  apply(auto intro: eval_bf.intros)
 done

code_pred eval_bf .
thm eval_bf.equation (*empty??*)
thm eval_bf_def

definition bf_hello_world :: "bf_cmd list" where
  "bf_hello_world \<equiv> 
BF_PLUS#BF_PLUS#BF_PLUS#BF_PLUS#BF_PLUS#BF_PLUS#BF_PLUS#BF_PLUS#BF_PLUS#BF_PLUS#BF_LOOPSTART#BF_RIGHT#BF_PLUS#BF_PLUS#BF_PLUS#BF_PLUS#BF_PLUS#BF_PLUS#BF_PLUS#BF_RIGHT#BF_PLUS#BF_PLUS#BF_PLUS#BF_PLUS#BF_PLUS#BF_PLUS#BF_PLUS#BF_PLUS#BF_PLUS#BF_PLUS#BF_RIGHT#BF_PLUS#BF_PLUS#BF_PLUS#BF_RIGHT#BF_PLUS#BF_LEFT#BF_LEFT#BF_LEFT#BF_LEFT#BF_MINUS#BF_LOOPEND#BF_RIGHT#BF_PLUS#BF_PLUS#BF_OUTPUT#BF_RIGHT#BF_PLUS#BF_OUTPUT#BF_PLUS#BF_PLUS#BF_PLUS#BF_PLUS#BF_PLUS#BF_PLUS#BF_PLUS#BF_OUTPUT#BF_OUTPUT#BF_PLUS#BF_PLUS#BF_PLUS#BF_OUTPUT#BF_RIGHT#BF_PLUS#BF_PLUS#BF_OUTPUT#BF_LEFT#BF_LEFT#BF_PLUS#BF_PLUS#BF_PLUS#BF_PLUS#BF_PLUS#BF_PLUS#BF_PLUS#BF_PLUS#BF_PLUS#BF_PLUS#BF_PLUS#BF_PLUS#BF_PLUS#BF_PLUS#BF_PLUS#BF_OUTPUT#BF_RIGHT#BF_OUTPUT#BF_PLUS#BF_PLUS#BF_PLUS#BF_OUTPUT#BF_MINUS#BF_MINUS#BF_MINUS#BF_MINUS#BF_MINUS#BF_MINUS#BF_OUTPUT#BF_MINUS#BF_MINUS#BF_MINUS#BF_MINUS#BF_MINUS#BF_MINUS#BF_MINUS#BF_MINUS#BF_OUTPUT#BF_RIGHT#BF_PLUS#BF_OUTPUT#BF_RIGHT#[]
 "

definition hello_world_ascii :: "byte list" where
  "hello_world_ascii \<equiv> [72, 101, 108, 108, 111, 32, 87, 111, 114, 108, 100, 33]"

(*why u no work??*)
values "{zs. eval_bf bf_hello_world (Normal (Tape [] 0 []) (Inp []) (Outp [])) zs}"

lemma hello_world: "eval_bf bf_hello_world 
    (Normal (Tape [] 0 []) (Inp []) (Outp [])) 
    (Normal (Tape [33, 100, 87, 0] 10 []) (Inp []) (Outp (rev hello_world_ascii)))"
apply(simp add: hello_world_ascii_def bf_hello_world_def)
  apply(rule seq')
  apply(auto intro: eval_bf.intros)
  apply(rule seq', auto intro: eval_bf.intros)+
  apply(rule seq_while_split[of "[BF_RIGHT, BF_PLUS, BF_PLUS, BF_PLUS, BF_PLUS, BF_PLUS, BF_PLUS, BF_PLUS, BF_RIGHT, BF_PLUS, BF_PLUS, BF_PLUS,
             BF_PLUS, BF_PLUS, BF_PLUS, BF_PLUS, BF_PLUS, BF_PLUS, BF_PLUS, BF_RIGHT, BF_PLUS, BF_PLUS, BF_PLUS, BF_RIGHT, BF_PLUS, BF_LEFT,
             BF_LEFT, BF_LEFT, BF_LEFT, BF_MINUS]", simplified])
  apply((rule eval_bf.whileTrue[of _ "[BF_RIGHT, BF_PLUS, BF_PLUS, BF_PLUS, BF_PLUS, BF_PLUS, BF_PLUS, BF_PLUS, BF_RIGHT, BF_PLUS, BF_PLUS, BF_PLUS,
             BF_PLUS, BF_PLUS, BF_PLUS, BF_PLUS, BF_PLUS, BF_PLUS, BF_PLUS, BF_RIGHT, BF_PLUS, BF_PLUS, BF_PLUS, BF_RIGHT, BF_PLUS, BF_LEFT,
             BF_LEFT, BF_LEFT, BF_LEFT, BF_MINUS]", simplified], simp),
        (rule seq', auto intro: eval_bf.intros)+)+
  apply(rule eval_bf.whileFalse[of _ "[BF_RIGHT, BF_PLUS, BF_PLUS, BF_PLUS, BF_PLUS, BF_PLUS, BF_PLUS, BF_PLUS, BF_RIGHT, BF_PLUS, BF_PLUS, BF_PLUS,
             BF_PLUS, BF_PLUS, BF_PLUS, BF_PLUS, BF_PLUS, BF_PLUS, BF_PLUS, BF_RIGHT, BF_PLUS, BF_PLUS, BF_PLUS, BF_RIGHT, BF_PLUS, BF_LEFT,
             BF_LEFT, BF_LEFT, BF_LEFT, BF_MINUS]", simplified], simp)
  apply(rule seq', auto intro: eval_bf.intros)+
  done

end
