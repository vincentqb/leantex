#check Nat.succ
#check_failure (1 : String)
#eval [1, 2, 3].map (· * 2)
#eval! #[4, 5].size
#reduce (fun n => n + 1) 2
#synth Inhabited Nat
#guard 1 + 1 == 2
#guard_msgs in
#print Nat.add
#print axioms Nat.add_comm
#print sig List.map
#print equations List.length
#print eqns List.append
#print tactic tags
#print "plain text"
#print
  axioms Nat.mul_comm
#where
#version
  #check Nat.zero
	#eval 3
open Nat in #check succ
set_option pp.all true in
#check 1
def size (s : Finset Nat) : Nat := #s
example (s : Finset Nat) : (#s) ≤ #s + 1 := by omega
example : Cardinal := #α
for x in #[1, 2] do pure ()
x#exit #exit' #exit_named in#check
#exit
