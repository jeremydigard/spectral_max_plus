#check fun x : Nat => fun y : Bool => if not y then x + 1 else x + 2
#check fun (x : Nat) (y : Bool) => if not y then x + 1 else x + 2
#check fun x y => if not y then x + 1 else x + 2

#check fun y : Bool => if not y then (fun (x : Nat) => x+1) else (fun (x : Nat) => x+2)
