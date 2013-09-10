theory brainfuck_core
imports Main
  "~~/src/HOL/Word/Word"
  (*"~~/src/HOL/Word/WordBitwise"*)
begin

type_synonym byte = "8 word"
lemma "(256 :: byte) = 0" by simp


datatype bf_cmd_basic = R  --"<, increment the data pointer (to point to the next cell to the right)." 
                | L  --">, decrement the data pointer (to point to the next cell to the left)."
                | P  --"+, increment the byte at the data pointer."
                | M  --"-, decrement the byte at the data pointer."
                | D  --"., output the byte at the data pointer."
                | C  --",, accept one byte of input, storing its value in the byte at the data pointer."

datatype bf_cmd = Basic "bf_cmd_basic list"
                | LB --"[, while data pointer is not zero"
                | RB --"]"


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

fun eval_basic1 :: "bf_cmd_basic \<Rightarrow> state \<Rightarrow> state" where
  "eval_basic1 R (Normal (Tape lt c []) inp outp) = Normal (Tape (c#lt) 0 []) inp outp" |
  "eval_basic1 R (Normal (Tape lt c (rt#rts)) inp outp) = Normal (Tape (c#lt) rt rts) inp outp" |
  "eval_basic1 L (Normal (Tape [] c rt) inp outp) = Error" |
  "eval_basic1 L (Normal (Tape (lt#lts) c rt) inp outp) = Normal (Tape lts lt (c#rt)) inp outp" |
  "eval_basic1 P (Normal (Tape lt c rt) inp outp) = Normal (Tape lt (c + 1) rt) inp outp" |
  "eval_basic1 M (Normal (Tape lt c rt) inp outp) = Normal (Tape lt (c - 1) rt) inp outp" |
  "eval_basic1 D (Normal (Tape lt c rt) inp (Outp outp)) = Normal (Tape lt c rt) inp (Outp (c#outp))" |
  "eval_basic1 C (Normal (Tape lt _ rt) (Inp []) outp) = Normal (Tape lt 0 rt) (Inp []) outp" |
  "eval_basic1 C (Normal (Tape lt _ rt) (Inp (i#is)) outp) = Normal (Tape lt i rt) (Inp is) outp" |
  "eval_basic1 _ Error = Error"

value[code] "print_state (eval_basic1 R (Normal (Tape [2,1] 3 [4,5,6]) (Inp []) (Outp [])))"
value "print_state (eval_basic1 R (Normal (Tape [3,2,1] 4 []) inp outp))"
value "print_state (eval_basic1 L (Normal (Tape [3,2,1] 4 [5,6]) inp outp))"
value "print_state (eval_basic1 L (Normal (Tape [] 1 [2,3]) inp outp))"
value "print_state (eval_basic1 P (Normal (Tape [3,2,1] 8 [4,5,6]) inp outp))"
value "print_state (eval_basic1 M (Normal (Tape [3,2,1] 8 [4,5,6]) inp outp))"
value "print_state (eval_basic1 D (Normal (Tape [3,2,1] 8 [4,5,6]) (Inp [1,2,3]) (Outp [4,5,6])))"
value "print_state (eval_basic1 C (Normal (Tape [3,2,1] 8 [4,5,6]) (Inp [1,2,3]) (Outp [4,5,6])))"
value "print_state (eval_basic1 C (Normal (Tape [3,2,1] 8 [4,5,6]) (Inp []) (Outp [4,5,6])))"

fun eval_basic :: "bf_cmd_basic list \<Rightarrow> state \<Rightarrow> state" where
  "eval_basic [] s = s" |
  "eval_basic (c#cs) s = eval_basic cs (eval_basic1 c s)"

(*0,1,2,3 output*)
value "print_state (eval_basic [D, R, P, D, R, P, P, D, R, P, P, P, D, L, L, L] (Normal (Tape [] 0 []) (Inp []) (Outp [])))"


inductive eval :: "bf_cmd list \<Rightarrow> state \<Rightarrow> nat \<Rightarrow> state \<Rightarrow> bool" for cmd and s where
  "s = s' \<Longrightarrow> pc = 0 \<Longrightarrow> eval cmd s pc s'" |
  "eval cmd s pc s' \<Longrightarrow> pc + 1 = pc' \<Longrightarrow> cmd ! pc =  Basic cb \<Longrightarrow> (eval_basic cb s') = s'' \<Longrightarrow> eval cmd s pc' s''" 
  (*TODO control flow*)


lemma "eval [] (Normal (Tape [] 0 []) inp outp) 0 (Normal (Tape [] 0 []) inp outp)"
  by(simp add: eval.intros)

lemma "eval [Basic [P, D]] (Normal (Tape [] 0 []) inp (Outp [])) 1 (Normal (Tape [] 1 []) inp (Outp [1]))"
  apply(auto intro: eval.intros)
 done


lemma "eval [Basic [P, D], Basic [P, P, P, D]] (Normal (Tape [] 0 []) inp (Outp [])) 2 (Normal (Tape [] 4 []) inp (Outp [4,1]))"
    apply(rule eval.intros(2))
    apply(simp_all)
    apply(rule eval.intros(2))
    apply(simp_all)
    apply(rule eval.intros(1))
    apply(simp_all)
    apply(simp)
done


code_pred eval .

value[code] "eval [Basic [P, D], Basic [P, P, P, D]] 
  (Normal (Tape [] 0 []) (Inp []) (Outp [])) 2 (Normal (Tape [] 4 []) (Inp []) (Outp [4,1]))"


end
