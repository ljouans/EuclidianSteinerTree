let eps = 1e-8;;
#open "graphics";;


(* ------------------------------------ *)
(* ------------ AFFICHAGE ------------- *)
(* ------------------------------------ *)

let wait =
  let time = ref 0. in
  fun delay ->
     while sys__time () -. !time < delay do done;
     time := sys__time ()
;;

let move_to (x,y) = moveto (int_of_float x) (int_of_float y);;
let line_to (x,y) = lineto (int_of_float x) (int_of_float y);;
let trace_pt (x,y) = fill_circle (int_of_float x) (int_of_float y) 3;;
let trace_ligne tab (a,b) = move_to tab.(a); line_to tab.(b);;



let afficher_FST points arb nTerminaux =
  open_graph "1000x800";
  let n = vect_length points in
  
  let rec parc_voisins i = function
    | [] -> ()
    | a :: s -> trace_ligne points (i , a);
      parc_voisins i s
  in
  
  set_color (rgb 255 0 0);
  for i = 0 to nTerminaux - 1 do
    trace_pt points.(i)
  done;
  
  set_color (rgb 0 0 255);
  for i = nTerminaux to n - 1 do
    trace_pt points.(i)
  done;
  
  set_line_width 2;
  set_color (rgb 0 0 0);
  
  for i = 0 to n - 1 do
    parc_voisins i (arb.(i))
  done;
;;




(* ------------------------------------ *)
(* ----- MANIPULATION VECTORIELLE ----- *)
(* ------------------------------------ *)

let mult u scal = (fst u *. scal, snd u *. scal);;
let sum u v = (fst u +. fst v, snd u +. snd v);; 
let div u scal = (fst u /. scal, snd u /. scal);;

let egal x y = 
  abs_float (y -. x) <. eps
;;
let dst (x1, y1) (x2, y2) = 
  sqrt (((x2 -. x1) *. (x2 -. x1)) +. ((y2 -. y1) *. (y2 -. y1)))
;;
let dst_points points indPt indV =
  dst (points.(indPt)) (points.(indV)) 
;;


(* Comme pour <Calcul_positions> degre designe le nombre de voisins de 
Steiner d'un point de Steiner *)
let calcul_degre arb nFixes nSteiner =
  let deg = make_vect nSteiner 0 in
  
  let rec parc_lst = function 
    | [] -> 0
    | a :: s when a >= nFixes -> 1 + parc_lst s
    | a :: s -> parc_lst s
  in
  
  for i = 0 to nSteiner - 1 do
    deg.(i) <- parc_lst arb.(i + nFixes) 
  done;
  
  deg
;;



(* Trouve un voisin de Steiner de degre non-nul *)
let trouver_voisin_puissant arb degre i nFixes = 
  let rec parc_lst = function
      | [] -> -1 (* Aucun voisin puissant n'est present *)
      | a :: s when (a >= nFixes) && (degre.(a - nFixes) >= 1) -> a
      | a :: s -> parc_lst s
    
  in parc_lst arb.(i)
;;



(* Trouve le premier indice k tel que B.(i).(k) <> 0. *)
let select_index b i = 
  let j = ref 1 in 
  while !j < 4 && b.(i).(!j) <> 0. do
    incr j
  done;
  
  if (!j >= 4) then raise (Failure "err <surcharge <cons_mat_systeme");
  !j
;;



(* Lors de la completion de <B>, l'ordre de l'arbre est respecte. 
Si arb.(i) = [j; k; l], et que, mettons, j et l sont des points de Steiner, 
alors
B.(i).(1) <-> (ancien)b.(i).(j)
B.(i).(2) <-> (ancien)b.(i).(l) 
*) 
let cons_mat_system arb points nFixes nSteiner delta =
  let B = make_matrix nSteiner 4 0. 
  (* B.(i).(0) correspond a b.(i).(i) d'avant (cf dossier) *)
  and C = make_vect nSteiner (0., 0.) 
  and visite = make_vect nSteiner false in
  
  
  let rec modif_mat i = function
    | [] -> ()
    | a :: s when a < nFixes ->  
      let dia = max (dst_points points i a) delta in
      C.(i - nFixes) <- sum C.(i - nFixes) (div points.(a) (dia));
      B.(i - nFixes).(0) <- B.(i - nFixes).(0) +. 1. /. dia;
      modif_mat i s
      
    | a :: s when visite.(a - nFixes) -> modif_mat i s
    | a :: s -> 
      let dia = max (dst_points points i a) delta in
      let j0 = select_index B (i - nFixes) in
      B.(i - nFixes).(j0) <- -. 1. /. dia;
      B.(i - nFixes).(0) <- B.(i - nFixes).(0) +. 1. /. dia;
      modif_mat i s
  in
  
  
  for i = nFixes to nFixes + nSteiner - 1 do
    if not visite.(i - nFixes) then begin (* Test inutile *)
      modif_mat i arb.(i);
      (*visite.(i - nFixes) <- true;*)
    end
  done;
  
  B, C
;;



(* trouve k tel que 
  B.(i).(k) <-> (ancien)b.(i).(j) 
*)
let trouver_index arbre i j nFixes =
  let j0 = ref 0 
  and trouve = ref false 
  and voisins = ref arbre.(i) in
  
  while !voisins <> [] do
    let a = hd !voisins in
    voisins := tl !voisins;
    
    if a = j 
    then begin 
      trouve := true;
      voisins := [] (* On a trouve le point cherche *)
    end else if (a >= nFixes) then incr j0; (* C'est un point de Steiner *)
    
  done;
  
  if not !trouve then raise (Failure "<indice non trouve <trouver_index");
  (!j0 + 1) (* /!\, B.(i).(0) est deja occupe *)
;;



(* Realise une operation du pivot de Gauss *)
let gauss_file arbre mB mC i j nFixes =
  let bii = mB.(i).(0) in
  
  mB.(i).(0) <- 1.;
  
  let j0 = trouver_index arbre (i + nFixes) (j + nFixes) nFixes in
  (* 1 <= j0 <= 3 *)
  mB.(i).(j0) <- mB.(i).(j0) /. bii;
  mC.(i) <- div mC.(i) bii;
  
  let i0 = trouver_index arbre (j + nFixes) (i + nFixes) nFixes in
  
  let bji = mB.(j).(i0) in
  mB.(j).(i0) <- mB.(j).(i0) -. bji *. mB.(i).(0);
  mB.(j).(0) <- mB.(j).(0) -. bji *. mB.(i).(j0);
  mC.(j) <- sum (mC.(j)) (mult mC.(i) (-. bji));
;;




(* ------------------------------------ *)
(* ----- MANIPULATION DES FILES ------- *)
(* ------------------------------------ *)
let enfiler (qIn, qOut) a =  
  qIn := a :: !qIn
;;
let defiler (qIn, qOut) = match (!qIn, !qOut) with
  |[], [] -> raise (Failure "File vide")
  |_, [] -> 
    qOut := rev !qIn;
    qIn := [];
    let a = hd !qOut in
    qOut := tl !qOut;
    a
  |_, a :: s -> 
    qOut := s;
    a
;;


(* Resout le systeme lineaire *)
let resoudre_systeme arb points nFixes nSteiner delta =
  let check = make_vect nSteiner false in
  let degre = calcul_degre arb nFixes nSteiner in
  let B, C = cons_mat_system arb points nFixes nSteiner delta in
  
  
  let sFeuilles = (ref [], ref []) 
  and lenFeuilles = ref 0  
  and qRes = ref [] in
  
  
  let resoudre_base i0 = 
    let lbd = B.(i0).(0) in 
    B.(i0).(0) <- 1.;
    C.(i0) <- div C.(i0) (lbd);
  in
  
  (* Ajout des feuilles a qFeuilles *)
  for i = 0 to nSteiner - 1 do
    if degre.(i) <= 1 then begin
      enfiler sFeuilles i;
      incr lenFeuilles
    end;
  done;
  
  (* traitement des feuilles et ajout de nouvelles *)
  while !lenFeuilles > 1 do
    let i = defiler sFeuilles in
    decr lenFeuilles;
    
    let j = trouver_voisin_puissant arb degre (i + nFixes) nFixes in
    
    check.(i) <- true;
    degre.(i) <- 0;
    
    if (j = -1) then begin 
      resoudre_base i; 
    end else begin
    
      gauss_file arb B C i (j - nFixes) nFixes; 
      degre.(j - nFixes) <- degre.(j - nFixes) - 1;
    
      if ((degre.(j - nFixes) = 1) && (not check.(j - nFixes))) 
      (* Si j a deux voisins, il ne doit pas etre ajoute deux fois *)
      then begin
        enfiler sFeuilles (j - nFixes);
        incr lenFeuilles;
        check.(j - nFixes) <- true
      end;
    
      qRes := (i, j - nFixes) :: !qRes;
    end
  done;
  
  let resolution (i, j) =
    let j0 = trouver_index arb (i + nFixes) (j + nFixes) nFixes in 
    let bij = B.(i).(j0) in
    
    C.(i) <- sum (C.(i)) (mult (C.(j)) (-. bij))
  in
  let iMid = defiler sFeuilles in 
  
  resoudre_base iMid;
  do_list resolution !qRes;
  
  for i = 0 to nSteiner - 1 do
    points.(i + nFixes) <- C.(i)
  done
;;


(* Resout <nIter> fois le systeme *)
let optimiser_positions anim arbre points nFixes nSteiner delta nIter =
  for i = 0 to nIter - 1 do
    resoudre_systeme arbre points nFixes nSteiner delta;   
  done;
  
  if anim then begin
    open_graph "1000x800";
    clear_graph ();
    afficher_FST points arbre nFixes;
    wait 0.04
  end
;;

