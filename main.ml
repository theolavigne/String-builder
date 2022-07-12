open Random

(*Question 1.1*)

type string_builder = 
  | Leaf of string * int
  | Node of string_builder * int * string_builder

(*Question 1.2*)

let word str = Leaf (str, String.length str)

(*Question 1.3*)

(*word_length ensures: renturns the word length of a string builder*)
let word_length sb = match sb with
  |Leaf (_,i) -> i
  |Node (_,i,_) -> i

let concat sb1 sb2 = Node (sb1, (word_length sb1) + (word_length sb2), sb2)

(*Question 2*)

(*The mot function ensures the returns of the word represented by a given string builder*)
let rec mot strb = match strb with
  |Leaf (a,_) -> a
  |Node (left, _, right) -> (mot left) ^ (mot right)

let char_at i strb  = String.get (mot strb) i

(*Question 3*)


let rec sub_string i m sb = match sb with 
  |Leaf(a,x) -> Leaf(String.sub a i m,m)
  |Node(Leaf(a,x),y,b)->if x > i then 
                  if x > i+m-1 then Leaf(String.sub a i m,m)
                  else Node(Leaf(String.sub a i (x-i), x-i),m, sub_string 0 (m-x+i) b)
                else sub_string (i-x) m b
  |Node(
    Node(a,x,b),y,c) -> 
      if x > i then
        if x > i+m-1 then sub_string i m (Node(a,x,b))
        else Node(sub_string i (x-i) (Node(a,x,b)),m, sub_string 0 (m-x+i) c)
      else sub_string (i-x) m c;;

(*Question 4*)

(*aux1 ensures to do the cost function with an accumulator to mesure the depht *)
let rec aux1 sb depht = match sb with
  |Leaf (_, i) -> i * depht
  |Node (left, _, right) -> aux1 left (depht + 1) + aux1 right (depht + 1);;

let cost sb = aux1 sb 0

(*Question 5*)

(*random_letter ensures the return of a random string of A T C G *)
let _ = Random.self_init ()
let random_letter () = let x = Random.int 4 in 
                                    if x = 0 then "A" 
                                    else if x = 1 then "T" 
                                    else if x = 2 then "C" 
                                    else if x = 3 then "G"
                                    else failwith "Not Possible"

(*rdm_string ensures the return a random string of lenght y+1 composed of the random letters A T C G *)
let rec rdm_string y = if y = 0 then random_letter ()
                      else let a = random_letter () in
                        a ^ (rdm_string (y - 1))

let rec random_string i = if i = 0 then word (rdm_string (Random.int 10))
                          else let sb1 = random_string (i-1) in
                            let sb2 = random_string (i-1) in
                              concat sb1 sb2

(*Question 6*)

let rec aux sb acc = match sb with
  |Leaf (a,_) -> a::acc
  |Node (left,_,right) -> let acc2 = aux right acc in 
                            aux left acc2

let list_of_string sb = aux sb []

(*Question 7*)

(*leaf_list ensures the return of a "leaf" list, given any string_builder *)
let leaf_list sb = List.map word (list_of_string sb)

(*moy_cost ensures the return of the average cost, given 2 string_builder *)
let moy_cost l1 l2 = (float_of_int (cost l1) +. (float_of_int (cost l2))) /. 2.

(*It is supposed that |list|>=2 *)
(*couple_max returns the position of the max couple *)
let rec couple_max list acc position res = match list with
  |x::(y::q as queue) -> let moy = moy_cost x y in
                          if moy > acc then couple_max queue moy (position+1) position
                          else couple_max queue acc (position+1) res
  |_ -> res

(*It is supposed that |list|>=2 
placement places the elements, following the elements*)

let rec placement list position = match list with
  |[] |_::[] -> failwith "len of list < 2 in placement"
  |x::(y::q as queue) -> if position = 0 then (concat x y)::q
                          else placement queue (position - 1)

(*aux2 implements the final algorithm *)
let rec aux2 list = match list with
  |[] -> failwith "aux2 : list shouldn't be empty"
  |[x] -> x
  |x::y::_ -> let pos = couple_max list (moy_cost x y) 0 0 in
                aux2 (placement list pos)

let balance sb = aux2 (leaf_list sb)

(*Question 8*)

let gain sb = cost sb - (cost (balance sb))

let rec gain_list n acc = if n = 0 then acc else gain_list (n-1) (gain (random_string 10)::acc)

let max list = List.fold_left max min_int list

let min list = List.fold_left min max_int list

let rec sum list = match list with
  |[] -> 0
  |t::q -> t + (sum q)

let average list = float_of_int (sum list) /. float_of_int (List.length list)

let stat_list = gain_list 10 []

let max_gain, average_gain, min_gain = (max stat_list,average stat_list, min stat_list)







(*This part of the code will be reserved to test each function*)

let rec print_tree sb = match sb with
  |Leaf (a,x) -> Format.printf "    Leaf(%s , %d)" a x
  |Node (left, x, right) -> 
    (Format.printf "Node(\n"; print_tree left ; Format.printf "\n,%d,\n" x ; print_tree right; Format.printf "\n)")

let sb_test = Node(
                Node(
                  Leaf("I",1),3,Leaf("am",2))
                ,18,
                Node(
                  Leaf("a",1),15,Leaf("string_builder",14)
                )
              )


(*Uncomment if you want :*)
(*print_tree sb_test*)

(*Question 1.2*)

let () = assert (word "Camille" = Leaf ("Camille", 7))

(*Question 1.3*)

let () = assert( word_length sb_test = 18)

let () = assert( concat (Node(Leaf("I",1),3,Leaf("am",2))) 
                        (Node(Leaf("a",1),15,Leaf("string_builder",14))) 
              = sb_test)

(*Question 2*)

let () = assert( mot sb_test = "Iamastring_builder")

let () = assert( char_at 2 sb_test = 'm')

(*Question 3*)

(*let _ = print_tree (sub_string 1 4 sb_test)*)


(*Question 4*)

let () = assert ( cost sb_test = 36)

(*Question 5*)

(*Uncomment if you want :*)

(*let _ = print_tree (random_string 3)*)
(*let _ = Format.printf "%s" (random_letter())*)
(*let _ = Format.printf "%s" (rdm_string 5)*)

(*Question 6*)

let () = assert (list_of_string sb_test = ["I";"am";"a";"string_builder"])

(*Question 7*)

let () = assert (leaf_list sb_test = 
        [Leaf("I",1);Leaf("am",2);Leaf("a",1);Leaf("string_builder",14)] )

let () = assert (moy_cost (Leaf ("oui",3)) (Leaf ("ok", 2)) = 2.5)

let () = assert (couple_max (leaf_list sb_test) 0. 0 0= 2)

(*let _ = print_tree (balance sb_test) *)

(*Question 8*)

(*let _ = Format.printf "max = %d; average = %f ; min = %d ;\n" max_gain average_gain min_gain*)