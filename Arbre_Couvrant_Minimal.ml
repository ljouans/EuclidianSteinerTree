#open "graphics";;

let eps = 1.0e-10;;
let egal a b = abs_float (b-.a) <. eps;; 

type 'a tas_min = {mutable size : int; elem : 'a vect};;

(* ------------------------------------ *)
(* ------------ AFFICHAGE ------------- *)
(* ------------------------------------ *)



let move_to (x,y) = moveto (int_of_float x) (int_of_float y);;
let line_to (x,y) = lineto (int_of_float x) (int_of_float y);;
let trace_pt (x,y) = fill_circle (int_of_float x) (int_of_float y) 3;;
let trace_ligne tab (a,b) = move_to tab.(a); line_to tab.(b);;

let afficher_graham points convexe =
  open_graph "1000x800";
  let n = vect_length points in
  
  for i = 0 to (n - 1) do
    trace_pt points.(i)
  done;
  
  let rec parc_lst = function
    | [] -> ()
    | [a] -> ()
    | a :: b :: s -> trace_ligne points (a, b);
      parc_lst (b :: s)
  
  in parc_lst convexe
;;


let afficher_tsai points arb = 
  open_graph "1000x800";
  let n = vect_length points in
  
  
  for i = 0 to (n - 1) do
    trace_pt points.(i)
  done;
  
  let draw_edge i j = trace_ligne points (i, j) in
  
  for i = 0 to (n - 1) do
    do_list (draw_edge i) arb.(i)
  done;
;;






(* ------------------------------------ *)
(* ----- MANIPULATION VECTORIELLE ----- *)
(* ------------------------------------ *)

let vec a b = (fst b -. fst a, snd b -. snd a);;
let det v w = (fst v *. snd w) -. (snd v *. fst w);;
let sum u v = (fst u +. fst v, snd u +. snd v);;
let div u scal = (fst u /. scal, snd u /. scal);;
let mult u scal = (fst u *. scal, snd u *. scal);;
let sqrd a = a*.a;;
let dst2 p q = sqrd (fst p -. fst q) +. sqrd (snd p -. snd q);;
let alignes a b c = (abs_float (det (vec a b) (vec a c))) <. eps;;



(* ------------------------------------ *)
(* -------- ENVELOPPE CONVEXE --------- *)
(* ------------------------------------ *)



(* Enveloppe superieur *)
let rec maj_sup tab es i = match es with
  | [j] -> i :: es
  | j :: k :: s when (det (vec tab.(i) tab.(j)) (vec tab.(i) tab.(k)) <. 0.) 
      -> maj_sup tab (tl es) i
	| _ -> i :: es
;; 


(* Enveloppe inferieur *)
let rec maj_inf tab ei i = match ei with
  | [j] -> i :: ei
  | j :: k :: s when (det (vec tab.(i) tab.(j)) (vec tab.(i) tab.(k)) >. 0.)
     -> maj_inf tab (tl ei) i
  |_ -> i::ei
;; 	


(* Enveloppe totale *)
let rec maj_env tab ei es i n = match i with
  | k when (k >= n) -> ei, es
  | _ -> maj_env tab (maj_inf tab ei i) (maj_sup tab es i) (i+1) n
;;





(* /!\ le premier sommet reapparait a la fin de la liste !
Calcul l'enveloppe convexe de l'ensemble de points 
 POUR UN TABLEAU TRIE*)
let conv_graham points =
  let ei, es = maj_env points [0] [0] 1 (vect_length points) in
  (rev (tl es)) @ ei
;;


  
(*_______________ ALGORITHME DE TSAI _______________*)
(*
ENTREE : > Un vect de paire de flottants (points).
				 
SORTIE : Une liste d'indices de triangles de la forme : [(a,b,c);...] o
   ptsTab.(a/b/c) sont des points 


ETAPE 1 : Calculer l'enveloppe convexe de (Pi) le nuage de points

ETAPE 2: (Calcul de la triangulation de Delaunay de l'enveloppe)
  > Initialiser A une liste d'indice d'aretes avec celles de l'enveloppe.
  > T, la liste des indice des points de triangles, ici vide.
	
  > Tant que A est non-vide :
  | - Tirer une arete (ab) de A
  | - Trouver c tel que (abc) ne soit pas dans T, et dont
  |     le cercle circonscrit au triangle ne contienne aucun autre
  |     point (Critre de Delaunay)
  | - Ajouter (abc) ˆ T
  | - Si (bc) Žtait dans A, la supprimer. Sinon l'ajouter;
  |     Idem pour (ac)
  Renvoyer T

	
ETAPE 3: (Ajouter les points internes au polygone)

  > Pour tout point M n'appartenant pas ˆ l'enveloppe convexe :
  | - Chercher T1 l'ensemble des triangles dont le cercle circonscrit
  |     contient M (On dira que ces triangles chapeautent M)
  | - Pour chaque arete (ab) des triangles (abc) de T1 : 
  | |   - Si il existe un autre triangle (abd) dont l'une des arte est (ab):
  | |   |   - Supprimer ces deux triangles, et ajouter 
  | |   |	    (abM), (bMd), (acM), (cMd) ˆ la nouvelle liste 
  Renvoyer cette nouvelle liste
				
[Description par Laurent ChŽno, Une bo”te d'outils pour la programmation
caml]

*)


(* ------------------------------------ *)
(* -------- ALGORITHME DE TSAI -------- *)
(* ------------------------------------ *)



(* Renvoie le centre et le rayon AU CARRE du cercle circonscrit a p, q, r *)
let cercle_circonscrit (px, py) (qx, qy) (rx, ry) = 
	let p = dst2 (px, py) (0., 0.)
	and q = dst2 (qx, qy) (0., 0.)
	and r = dst2 (rx, ry) (0., 0.) 
	and div = 2. *. (px *.(qy -. ry) +. qx *. (ry -. py) +. rx *. (py -. qy)) in
	(* position du centre de gravite, rayon *)
	((p *. (qy -. ry) +. q *. (ry -. py) +. r *. (py -. qy)) /. div,
		-. (p *. (qx -. rx) +. q *. (rx -. px) +. r *. (px -. qx)) /. div),
		((dst2 (px, py) (qx, qy)) *. (dst2 (qx, qy) (rx, ry)) 
		 *. (dst2 (rx, ry) (px, py))) /. (sqrd div)
;;


(* Cherche un element validant le predicat *)
let rec trouver_element_valide valider l = match l with
	| [] -> raise (Failure "Pas trouve <err <trouver_elt_valide") 
	| a :: s -> 
	  if (valider a) 
	  then a 
	  else (trouver_element_valide valider s)
;;



(* Cree [n; ...; 1; 0] *)
let rec lst_id n = match n with
	| 0 -> [0]
	| _ -> n :: (lst_id (n - 1))
;;



let rec is_in i = function
  | [] -> false
  | a :: s when a = i -> true
  | a :: s -> is_in i s
;;



(* Regarde si le c_circonscrit a p,q,r ne contient qu'eux *)
let seul_dans_cercle p q r listPt tab = 
	let c, r2 = cercle_circonscrit tab.(p) tab.(q) tab.(r) in
	let valide m = 
	  (mem tab.(m) [tab.(p); tab.(q); tab.(r)]) 
	  || (dst2 c tab.(m) >. r2) in
	  
	for_all valide listPt
;;


(* Annonce si le triangle est nouveau ou non *)
let trg_est_nouveau p q r trg_old tab = 
	let est_autre (a,b,c) = 
	  (subtract [ p; q; r] [ a; b; c] <> []) in
	  
	((not alignes tab.(p) tab.(q) tab.(r)) && (for_all est_autre trg_old))
;;



(* L'egalite doit avoir lieu sur les points, dans un ordre quelconque *)
let egalite_arete (a,b) (p,q) = 
  ((a = p) && (b = q)) || ((a = q) && (b = p))
;;



let rec deja_dans_liste_aretes a ar = match ar with
	| [] -> false
	| b::s -> (egalite_arete a b) || (deja_dans_liste_aretes a s)
;;



(* difference A B = A\B mais pour des aretes*)
let rec difference l1 l2 = match l1 with
	| [] -> []
	| a :: s -> 
	  if (deja_dans_liste_aretes a l2) 
	  then difference s l2
		else a :: (difference s l2)
;;



(* difference_sym A B = A/\B *)
let difference_sym l1 l2 = 
  (difference l1 l2) @ (difference l2 l1)
;;



(* On met a jour la triangulation avec les points interieurs *)


(* Donne tous les triangles dont le cercle circonscrit contient m *)
let triangles_chapeautant m tab (p, q, r)= 
	let c, r2 = cercle_circonscrit tab.(p) tab.(q) tab.(r) in 
	(dst2 tab.(m) c) <. r2
;;



let supprimer_doublons l = 
	let rec lst_doublons l1 = match l1 with
		| [] -> []
		| (a, b) :: s -> 
		  if deja_dans_liste_aretes (a, b) s 
		  then (a, b) :: (lst_doublons s) 
			else (lst_doublons s)
			
	in difference l (lst_doublons l)
;;  



let rec aretes_of_triangles trg = match trg with
	| [] -> []
	| (a, b, c) :: s -> (a, b) :: (b, c) :: (c, a) :: (aretes_of_triangles s)
;;



let rec discriminer predicat l = match l with
	| [] -> [], []
	| (a, b, c) :: s -> let v, f = discriminer predicat s in
		if predicat (a,b,c) 
		then ((a,b,c) :: v, f) 
		else (v, (a,b,c) :: f)
;;

	
	
(* Trie pts en trois listes : sommets, aretes, points_internes *)
let etape_1 points =
 
  let n = vect_length points in
	let convexe = conv_graham points in
	
	let aretes = 
		let rec lister_aretes = function
		| a :: b :: s -> (a, b) :: (lister_aretes (b :: s))
		| _ -> []
		in lister_aretes convexe 
  in
		
	let points_internes = subtract (lst_id (n - 1)) (tl convexe) in
	(tl convexe, aretes, points_internes)
;;



(* Corps de l'algorithme de Tsai *)
let etape_2 sommets aretes ptsTab =
 
	let rec corps ar trg = match ar with
		| [] -> trg
		| (a, b) :: s -> 
		  let potentiel t = (trg_est_nouveau a b t trg ptsTab) && 
		                    (seul_dans_cercle a b t sommets ptsTab) in
		                    
			let c = trouver_element_valide potentiel sommets in
									corps (difference_sym s [(b, c) ; (c, a)]) ((a, b, c) :: trg)
	in corps aretes []
;;



let rec etape_3 pts_traites pts_restant trg points =
	let maj_triangulation m = 
		let chapeautant, ext = discriminer (triangles_chapeautant m points) trg in
		let ar = supprimer_doublons (aretes_of_triangles chapeautant) in
			(map (function (a, b) -> (a, b, m)) ar) @ ext 
		
	in		
	match pts_restant with
	| [] -> trg
	| m :: s -> etape_3 (m :: pts_traites) s (maj_triangulation m) points
;; 



let arb_of_trgLst lst n = 
  let arb = make_vect n [] in
  
  let rec parc_lst = function 
    | [] -> arb
    | (i, j, k) :: s -> 
      let ajout u v = 
        if not (is_in v arb.(u)) then arb.(u) <- v :: arb.(u)
      in
      
      do_list (ajout i) [j; k];
      do_list (ajout j) [i; k];
      do_list (ajout k) [i; j];
      
      parc_lst s
  
  in parc_lst lst
;;



(* Prends en argument un tableau de points tries !
renvoie le tableau d'indices de la triangulation (les aretes) 

/!\ nMax est le plus grand indice avant lequel aucun ŽlŽment ne vaut
(-1, -1) *)
let trianguler_tsai points = 
	let sommets, aretes, pts_internes = etape_1 points in
	let trg_conv = etape_2 sommets aretes points in
	arb_of_trgLst (etape_3 [] pts_internes trg_conv points) (vect_length points)
;;













(* STRUCTURE UTILISƒE : Tas min -> Assure une complexitŽ temporelle en O(nlogn)

ENTRƒE : Matrice de poids

ALGORITHME : Ë chaque Žtape, on ajoute l'arte adjacente au chemin visitŽ de poids 
minimal

SORTIE : L'arbre couvrant minimal, sous forme de liste d'indices d'artes,
(indice des points de ptsTab) et le poids de l'arbre.

*)



(* ------------------------------------ *)
(* ------- MANIPULATION TAS-MIN ------- *)
(* ------------------------------------ *)
(* Retire le dernier element.*) 
let take t = match t.size with
	| 0 -> failwith "Tas vide <take"
	| _ -> t.size <- t.size - 1;
			t.elem.(t.size)
;;



let tas_est_vide tas = 
  tas.size = 0
;;



let n_fils i = 2 * i + 1, 2 * i + 2;;
let n_pere i = (i - 1) / 2;;



let mini inf (a, b) (c, d) = 
  if inf b d 
  then (a, b) 
  else (c, d)
;;



(* Peut-etre modifier pour ne pas toujours inserer au meme endroit *)
let rec percole inf tas pere =
	let val_p = tas.elem.(pere) 
	and nFg, nFd = n_fils pere in
	
  if (nFg < tas.size) (* Le fils gauche existe *)
    then if (nFd < tas.size) (* Le fils droit existe *)
    then begin 
      let (min_f, min_val) = mini inf (nFg, tas.elem.(nFg)) 
                                      (nFd, tas.elem.(nFd)) in
				
				if inf min_val val_p 
				then begin
					tas.elem.(pere) <- min_val;
					tas.elem.(min_f) <- val_p;
					percole inf tas min_f 
				end
			end else  (* Qu'un fils gauche *)
			  if inf tas.elem.(nFg) val_p 
				then begin
					tas.elem.(pere) <- tas.elem.(nFg);
					tas.elem.(nFg) <- val_p;						
					percole inf tas nFg
				end
		(* Si pas de fils gauche, pas de droit non-plus *)
;;
 
 
 
let min_tas inf tas = match tas.size with
	| 0 -> failwith "Tas vide - min_tas"
	| _ -> 
	  let r = tas.elem.(0) in
		let nRac = take tas in 
			tas.elem.(0) <- nRac;
			percole inf tas 0;
			r
;;



let swap v i j = 
  let vi = v.(i) in
  v.(i) <- v.(j);
  v.(j) <- vi
;;



let ajouter_tas inf tas elt =
	(* Echange fils(i)-pere s'il le peux *) 
	let rec remonter i =
		let n_p = n_pere i in
		if inf tas.elem.(i) tas.elem.(n_p) 
		then begin
			swap tas.elem i n_p;
			remonter n_p
		end
	in
	
  tas.elem.(tas.size) <- elt;
	tas.size <- tas.size + 1;
	remonter (tas.size - 1)
;;

	
	


(* ------------------------------------ *)
(* -------- ALGORITHME DE PRIM -------- *)
(* ------------------------------------ *)

(* Prim pour une matrice de poids, avec une structure de tas.
Renvoie la liste du chemin le plus court, et son poids *)
let prim g points = 

	let n = vect_length g in
	let visite = make_vect n false in
	let arb = make_vect n [] in
	 
	let inf_poids (a, i, j) (b, k, l) = a <. b in
	
	visite.(0) <- true;
	
	let rec parcours_graphe tas j = function
	  | [] -> ()
	  | i :: s when egal (dst2 points.(i) points.(j)) 0. -> 
	    parcours_graphe tas j s 
	  | i :: s -> 
	    ajouter_tas inf_poids tas (dst2 points.(i) points.(j), j, i);
	    parcours_graphe tas j s 
	in
	
(* dans tas, (p, j, k) pour (poids AU CARRE, debut, fin) *)
	let rec empiler_depiler tas pds = 
		if (tas_est_vide tas) 
		then pds, arb
		else begin
			let (p, j, k) = min_tas inf_poids tas in
			
			if not visite.(k) then begin (* Je ne suis pas dans l'arbre *)
				visite.(k) <- true;
				parcours_graphe tas k g.(k);
				(* Ajout a l'arbre *)
				arb.(j) <- k :: arb.(j);
				arb.(k) <- j :: arb.(k);
				
				empiler_depiler tas (pds +. (sqrt p))
				
			end else (* Tampis *)
				empiler_depiler tas pds
		end 
	in
			
	let tas = {size = 0; elem = (make_vect (4 * n ) (0. ,0 ,0))} in
	
	parcours_graphe tas 0 g.(0);
	empiler_depiler tas 0.
;;




(* Trie les points dans l'ordre croissant d'abscisses *)
let tri_tableau points =
  let n = vect_length points in
  let pb = vect_of_list (sort__sort (fun a b -> (fst a) <. (fst b)) 
                        (list_of_vect points)) in
  
  for i = 0 to n - 1 do
    points.(i) <- pb.(i)
  done;
;; 

let copier v = 
  let n = vect_length v in
  let w = make_vect n v.(0) in
  
  for i = 0 to n - 1 do
    w.(i) <- v.(i)
  done;
  
  w
;;

let g a = fst (fst a);; 

(* trie v ET LE MODIFIE et cree un <codex> de correspondance *)

let trier_mem v =
  let lv = list_of_vect v 
  and n = vect_length v in
  
  let idx = ref n
  and codex = make_vect n 0 in
  
  (* preparation du codex *)
  let numeroter a = 
    decr idx;
    (a, !idx)
  in
  
  let paire_lv = map numeroter lv in
  let paire_triee = sort__sort (fun a b -> fst (fst a) <. fst (fst b)) paire_lv in
  (* Remplissage du codex *)
  idx := 0;
  let enregistrer_copier a = 
    codex.(!idx) <- snd a;
    v.(!idx) <- fst a;
    incr idx
  in
  
  do_list enregistrer_copier paire_triee;
  codex
;;



let reordonner_solution codex arb = 
  let n = vect_length arb in
  let nArb = make_vect n [] in
  
  for i = 0 to n - 1 do
    nArb.(codex.(i)) <- map (fun a -> codex.(a))  arb.(i)
  done;
  
  nArb
;;
  
let calculer_ACM points = 
  let copyPt = copier points in
  
  let codex = trier_mem copyPt in
  let tr = trianguler_tsai copyPt in
  let lg, arb = prim tr copyPt in
  
  lg, reordonner_solution codex arb
  
;;




