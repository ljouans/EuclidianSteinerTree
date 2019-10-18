random__init (unix__time ());;
let path = "/Users/LoicJouans/Desktop/TIPE 5:2/";;
#open "graphics";;
load (path^"/Code Caml Propre/Arbre_Couvrant_Minimal");;
load (path^"/Code Caml Propre/Sys_lin_res");;

let eps = 1e-6;;
let feedbacks = true;;
let pi = 4. *. atan 1.;;




let vec p1 p2 = (fst p2 -. fst p1, snd p2 -. snd p1);;
let sqrd a = a *. a;;
let norme v = sqrt ( (sqrd (fst v)) +. (sqrd (snd v)) );;
let scal u v = ((fst u) *. (fst v)) +. ((snd u) *. (snd v));;


let copier_vect ancien nouveau = 
  let n = vect_length ancien in
  
  for i = 0 to (n - 1) do
    nouveau.(i) <- ancien.(i)
  done;
;;

(*   (i3)
         \
          \ v           (th) est l'angle calcule
           \
      (th)  \
             \
  (i1) ------ (i2)
         u
*)      
let calculer_angle points i1 i2 i3 = 
  let u = vec points.(i2) points.(i1)
  and v = vec points.(i2) points.(i3) in
  
  let nu = max (norme u) (eps) 
  and nv = max (norme u) (eps) in
  (* ON NE FAIT PAS DE TEST DE NORME ! *)
  acos ((scal u v) /. (nu *. nv))
;;



(* 
   > On couple notre liste avec l'angle forme par rapport a une arete de 
   reference.
   > On trie par rapport a cet angle
   > On decouple la liste 
*)
let ordonner_aretes points ind lVoisins = 
  let arRef = hd lVoisins in
  
  let fCoupl = (fun a -> (calculer_angle points arRef ind a, a)) in
  (* Couplage *)
  let couplage = map fCoupl (tl lVoisins) in
  (* Tri *)
  let res = sort__sort (fun (ax, ay) (bx, by) -> ax <. bx) couplage in
  (* Decouplage *)
  (arRef :: map (fun (ax, ay) -> ay) res)
;;



let trouver_feuille arb = 
  let n = vect_length arb 
  and i0 = ref 0 in
  
  while !i0 < n && (list_length arb.(!i0) <> 1) do
    incr i0
  done;
  
  !i0
;;


let dst (ux, uy) (vx, vy) = 
  sqrt ((ux -. vx) *. (ux -. vx) +. (uy -. vy) *. (uy -. vy))
;; 

(* On mesure toutes les aretes, on somme, et on divise le resultat par deux *)
let longueur_FST arbre points = 
  let lg = ref 0. 
  and i = ref 0 
  and n = vect_length points in
  
  let dst_sommets a b = (dst points.(a) points.(b)) in
  
  while (!i < n) && (arbre.(!i) <> []) do
    lg := list_it (fun a b -> b +. (dst_sommets !i a)) arbre.(!i) !lg;
    
    incr i;
  done; 
  
  !lg /. 2.
;;
  
cos pi;;
let rand_vect n = 
  let v = make_vect n (0., 0.) in
  
  for i = 0 to n - 1 do
  	let r = 500. *. (sqrt (random__float (1.))) in
  	let tht = random__float (2.*.pi) in
  	
  	v.(i) <- (500. +. r*.(cos tht), 500. +. r*.(sin tht))
  	
  done;
  v
;;

(*
let rand_vect n =
	let v = make_vect n (0., 0.) in
	for i = 0 to n - 1 do
		v.(i) <- (random__float 1000., random__float 1000.)
	done;
	v
;;
*)

let mod_pi f = 
  if f < 0. then f +. pi
  else if f > 2. *. pi then f -. 2. *. pi 
  else f
;;


(* Retire les points en trop, coupe l'arbre et renvoie le triplet (longueur, points, arbre) *)
let presenter_resultats arb pts = 
  let n = ref 0 
  and nPhysique = vect_length arb in
  
  while !n < nPhysique && arb.(!n) <> [] do
    incr n
  done;
  
  let nPts = make_vect !n (0., 0.)
  and nArb = make_vect !n [] in
  
  for i = 0 to !n - 1 do
    nPts.(i) <- pts.(i);
    nArb.(i) <- arb.(i)
  done;
  longueur_FST arb pts, nPts, nArb
;;



let heuristique_angle points delta nIter animProg = 
  let nFixes = vect_length points 
  and _, arbACM = Arbre_Couvrant_Minimal__calculer_ACM points in 
 
  let arbH = make_vect (2 * nFixes - 1) [] 
  and newPts = rand_vect (2 * nFixes - 1)  
  and pptLibre = ref nFixes in
  
  copier_vect points newPts;
  copier_vect arbACM arbH;
  
  let rec parcours_voisins iMid = function
    | [] -> ()
    | [a] -> ()
    | a :: b :: s -> 
      let th = calculer_angle newPts a iMid b in
      
      if ((mod_pi th) <. 2.09439) (* = 120 degre *)
      then begin 
        
        arbH.(iMid) <- !pptLibre :: (subtract arbH.(iMid) [a; b]);
        arbH.(a) <- !pptLibre :: (except iMid arbH.(a));
        arbH.(b) <- !pptLibre :: (except iMid arbH.(b));
        
        arbH.(!pptLibre) <- [iMid; a; b];
        
        Sys_lin_res__optimiser_positions animProg arbH newPts (nFixes) 
                            (!pptLibre - nFixes+1 ) delta nIter;
        incr pptLibre;
        
        parcours_voisins iMid ((!pptLibre - 1) :: s)
      end else 
        parcours_voisins iMid (b :: s);
  in
     
  (* Parcours en profondeur ?*)
  for i = 0 to nFixes - 1 do
    if feedbacks 
    then begin
      print_int i;
      print_string " / ";
      print_int nFixes;
      print_newline();
    end;
    let voisinsOrdo = ordonner_aretes newPts i arbH.(i) in
    parcours_voisins i voisinsOrdo
  done;
  
  Sys_lin_res__optimiser_positions false arbH newPts nFixes 
                      (!pptLibre - nFixes) delta nIter;
  
  presenter_resultats arbH newPts
  
;;




let bel_arbre n essais = 
  let deltaM = ref 0.
  and bpts = ref [||]
  and barb = ref [||] in
  
  for i = 0 to essais - 1 do
    let v = rand_vect n in
    let lg, pts, arb = heuristique_angle v 0.1 50 false in
    
    let lgACM, _ = Arbre_Couvrant_Minimal__calculer_ACM v in
    if (1. -. lg /. lgACM) >. !deltaM 
    then begin
      bpts := pts;
      barb := arb;
      deltaM := 1. -. lg /. lgACM
    end;
    
    print_int i;
    print_newline()
  done;
  
  !deltaM, !bpts, !barb
;;    


let a, b, c = bel_arbre 1001 1;;
Sys_lin_res__afficher_FST b c 1001;;

let conversion arb points nFixes =
  let s = ref "\\begin{tikzpicture}[scale = #1]\n\\begin{scope}[every node/.style={circle,thick,draw}, inner sep = 0pt, minimum width = 0.08cm]\n" in
  
  let visites = make_vect (vect_length points) false in
  
  for i = nFixes to (vect_length points) - 1 do
    s := !s^"\\node[fill = sthlmOrange] ("^(string_of_int i)^") at ("^(string_of_float (fst points.(i) /. 100.))^", "^(string_of_float (snd points.(i) /. 100.))^") {};\n";
  done;
  
  for i = 0 to nFixes - 1 do
    s := !s^"\\node[fill = white] ("^(string_of_int i)^") at ("^(string_of_float (fst points.(i) /. 100.))^", "^(string_of_float (snd points.(i) /. 100.))^") {};\n";
  done;

  s := !s ^ "\\end{scope}\n";
  s := !s^"\\begin{scope}[>={Stealth[black]},
	every node/.style={fill=white,circle},
	every edge/.style={draw=red,very thick}]\n";
	 
  let jolie_phrase i u = 
    if not visites.(u) then
      s := !s^"\\path ("^(string_of_int i)^") edge ("^(string_of_int u)^");\n"
    ;
  in
   
  
	for i = 0 to (vect_length points) - 1 do
	  visites.(i) <- true;
	  
	  do_list (jolie_phrase i) arb.(i);
	done;
	s := !s^"\\end{scope}\n";
  s := !s^"\\end{tikzpicture}";
  
	!s
;;

print_string (conversion c b 1001);;
  
  
*)