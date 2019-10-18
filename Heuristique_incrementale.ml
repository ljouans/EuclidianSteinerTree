random__init (unix__time ());;
let path = "/Users/LoicJouans/Desktop/TIPE 5:2/";;
let valSup = 2 lsl 61 - 1;;
let feedbacks = false;;
#open "graphics";;
load (path^"/Code Caml Propre/Arbre_Couvrant_Minimal");;
load (path^"/Code Caml Propre/Sys_lin_res");;



let dst (x1, y1) (x2, y2) = 
  sqrt (((x2 -. x1) *. (x2 -. x1)) +. ((y2 -. y1) *. (y2 -. y1)))
;;

(* ------------------------------------ *)
(* ----------- METHODE NAIVE ---------- *)
(* ------------------------------------ *)

(* Cherche trois points et les relie. 
(Prendre au hasard ? Prendre les plus proches ? 
/!\ IL FAUDRA MODIFIER <optimiser_positions> et <longueur_arbre>) 
Ici on prend [0, 1, 2] *)
let ajouter_premiers_points arbre pptNonUtilise =
  arbre.(pptNonUtilise) <- [0; 1; 2];
  arbre.(0) <- [pptNonUtilise];
  arbre.(1) <- [pptNonUtilise];
  arbre.(2) <- [pptNonUtilise];
;;



(* Ajoute un point (d'indice <pptNonUtilise>)
sur l'arete passee en parametre *)
let ajouter_point_sur (i, j) arbre pptNonUtilise idx = 
  arbre.(pptNonUtilise) <- [i; j; idx];
  arbre.(i) <- pptNonUtilise :: (except j arbre.(i));
  arbre.(j) <- pptNonUtilise :: (except i arbre.(j));
  arbre.(idx) <- [pptNonUtilise]; (* idx designe TOUJOURS un terminal *)
  
;;



(* Retire l'ancien point s'il a ete ajoute;
Reforme la liaison;
Rajoute celui passe en parametre *)
let mise_a_jour_arbre arbre (i, j) aRetirer (u, v) aAjouter ptFixe = 
  if (aRetirer <>  -1) 
  then begin
    let [k; l; m] = arbre.(aRetirer) in
    arbre.(k) <- except aRetirer arbre.(k);
    arbre.(l) <- except aRetirer arbre.(l);
    arbre.(m) <- except aRetirer arbre.(m); 
    
    arbre.(u) <- v :: (arbre.(u));
    arbre.(v) <- u :: (arbre.(v));
    
    arbre.(aRetirer) <- []
  end;
  
  arbre.(aAjouter) <- [i; j; ptFixe];
  arbre.(ptFixe) <- [aAjouter];
  arbre.(i) <- aAjouter :: arbre.(i);
  arbre.(j) <- aAjouter :: arbre.(j)    
;;



(* realise l'operaiton inverse d'<ajouter_point_sur> *)
let retirer_liaison arbre aRetirer (u, v) =
  let [i; j; k] = arbre.(aRetirer) in
  
  arbre.(i) <- except aRetirer arbre.(i);
  arbre.(j) <- except aRetirer arbre.(j);
  arbre.(k) <- except aRetirer arbre.(k);
  
  arbre.(aRetirer) <- [];
  
  arbre.(u) <- v :: arbre.(u);
  arbre.(v) <- u :: arbre.(v)
;;




(* Calcul la longueur de l'arbre *)
let longueur_arbre arbre points = 
  let lg = ref 0. 
  and i = ref 0 
  and n = vect_length points in
  
  let dst_sommets a b = (dst points.(a) points.(b)) in
  
  while (!i < n) do
    lg := list_it (fun a b -> b +. (dst_sommets !i a)) arbre.(!i) !lg;
    
    incr i;
  done; 
  
  !lg /. 2.
;;



(* Redimensionne le vecteur passe en parametre *)
let recomposer_vecteur n v = 
  let nV = make_vect n (v.(0)) in
  
  for i = 0 to (n - 1) do
    nV.(i) <- v.(i)
  done;
  
  nV
;;





(* Applique l'heuristique decrite dans mes feuilles.
On suppose avoir au moins quatre points 

lstAretesAAct contient l'ensemble des aretes de l'arbre a l'etude.
(en un et un seul exemplaire pour chaque) 

Des lors qu'un terminal est lie, il est note comme <visite> et ne sera 
jamais plus considere *)
let heuristique vPoints delta nIter anim =
  let n = vect_length vPoints in 
  let meilleurArbre = make_vect (2 * n) [] (* Faudrait areter a 2n-1 *)
  and sousOptiArbre = make_vect (2 * n) [] 
  and nvxPoints = make_vect (2 * n) (0., 0.)
  and lgSousOpti = ref(0.) 
  and pptNonUtilise = ref(n) 
  and lstAretesAAct = ref([(0, n); (1, n); (2, n)]) in
  
  for i = 0 to (n - 1) do 
    nvxPoints.(i) <- vPoints.(i)
  done;
  
  for i = n to (2 * n - 1) do
    nvxPoints.(i) <- (random__float 500., random__float 500.)
  done;
  
  (* <areteSupprimee> contient les indices de l'arete supprimee
  pour creer le dernier arbre optimal. N'a de sens que si <ptAjoute> <> -1 *)
  let rec parcours_aretes ar ptAjoute areteSupprimee idx = match ar with
    | [] -> begin
        ajouter_point_sur areteSupprimee sousOptiArbre !pptNonUtilise idx;
        let (u, v) = areteSupprimee in
        lstAretesAAct := except (u, v) !lstAretesAAct;
        lstAretesAAct := except (v, u) !lstAretesAAct; 
        lstAretesAAct := (idx, ptAjoute) :: (u, ptAjoute) :: (v, ptAjoute) 
                         :: !lstAretesAAct;
        incr pptNonUtilise; 
      end
      
    | (i, j) :: s -> begin
      ajouter_point_sur (i, j) sousOptiArbre !pptNonUtilise idx;
      
      for i = n to (2 * n - 1) do
        nvxPoints.(i) <- (random__float 500., random__float 500.)
      done;
     
      Sys_lin_res__optimiser_positions anim sousOptiArbre nvxPoints n 
                          (!pptNonUtilise - n +1) delta nIter;
      
      
      let lg = longueur_arbre sousOptiArbre nvxPoints in
      if (lg <. !lgSousOpti)       
      then begin
        if ptAjoute <> (-1) then
          retirer_liaison meilleurArbre ptAjoute areteSupprimee
        ;
        
        ajouter_point_sur (i, j) meilleurArbre !pptNonUtilise idx;
        retirer_liaison sousOptiArbre !pptNonUtilise (i, j);
        
        lgSousOpti := lg;
        parcours_aretes s !pptNonUtilise (i, j) idx      
        
      end else begin
        retirer_liaison sousOptiArbre !pptNonUtilise (i, j);
        parcours_aretes s ptAjoute areteSupprimee idx
      end;
      
     end
  in
  
  ajouter_premiers_points meilleurArbre !pptNonUtilise;
  ajouter_premiers_points sousOptiArbre !pptNonUtilise;
  incr pptNonUtilise;
  
  for i = 3 to (n - 1) do
    if feedbacks then begin 
      print_int i;
      print_string "/";
      print_int (n - 1);
      print_newline();
    end;
    lgSousOpti := (float_of_int valSup);
      
    parcours_aretes !lstAretesAAct (-1) (-1, -1) i;
  done;
  
  for i = n to (2 * n - 1) do
    nvxPoints.(i) <- (random__float 500., random__float 500.)
  done;
  
  
  let mA = recomposer_vecteur (!pptNonUtilise ) meilleurArbre
  and mP = recomposer_vecteur (!pptNonUtilise ) nvxPoints in
  
  Sys_lin_res__optimiser_positions anim mA mP n (vect_length mP - n ) 
                                   delta nIter;
  
  (!lgSousOpti, mA, mP)
  
;;


(* ------------------------------------ *)
(* -- TRIES PAR ABSCICES CROISSANTES -- *)
(* ------------------------------------ *)



(* Meme methode, mais les points sont tries par abscisses croissantes *)
let heuristique_croissante vPoints delta nIter anim =
  let tri = (fun (ax, ay) (bx, by) -> 
    if ax =. bx then ay <. by
    else ax <. bx) in
  
  let lpts = list_of_vect vPoints in
  let vPts = vect_of_list (sort__sort tri lpts) in
  
  heuristique vPts delta nIter anim
;;



(* ------------------------------------ *)
(* ----- SELECTION PAR PROXIMITE ------ *)
(* ------------------------------------ *)


(* IDEE : 
  > Calculer l'ACM,
  > Pour chaque point, derterminer la distance moyenne la separant de ses 
  voisins
  
  ? Prendre plutot la ponderation dans la triangulation de Delaunay ?
  
  > Les trier dans l'ordre de proximité
  > Prendre dans l'ordre de ponderation croissante
  
*)


(* Renvoie le vecteur "ponderation" trie par ordre de ponderation croissante 
des indices des points *)
let calculer_ponderation vPoints = 
  let n = vect_length vPoints in
  let pond = make_vect n (0, 0.)
  and fstPond = make_vect n 0 in
  
  let _, arbCouvMin = Arbre_Couvrant_Minimal__calculer_ACM vPoints in
  
  let calc_pond i a = 
    pond.(i) <- (i, (snd pond.(i)) +. (dst vPoints.(i) vPoints.(a)))
    
  and tri_pond a b = 
    snd a <. snd b
  in
  
  for i = 0 to n - 1 do
    do_list (calc_pond i) arbCouvMin.(i);
  done; 
  
  for i = 0 to n - 1 do
    pond.(i) <- (i, 
                 (snd pond.(i)) /. float_of_int (list_length arbCouvMin.(i)))
  done;
 
  let lstPond = list_of_vect pond in
  let pondTrie = vect_of_list (sort__sort tri_pond lstPond) in
  
  for i = 0 to n - 1 do
    fstPond.(i) <- fst pondTrie.(i)
  done;
  
  fstPond
;;



(* traite le cas de base de l'algorithme suivant *)
let ajouter_premiers_points_proximite arbre pond pptNonUtilise =
  arbre.(pptNonUtilise) <- [pond.(0); pond.(1); pond.(2)];
  arbre.(pond.(0)) <- [pptNonUtilise];
  arbre.(pond.(1)) <- [pptNonUtilise];
  arbre.(pond.(2)) <- [pptNonUtilise];
;;



let heuristique_proximite vPoints delta nIter anim =
  let n = vect_length vPoints in 
  let meilleurArbre = make_vect (2 * n) [] 
  and sousOptiArbre = make_vect (2 * n) [] 
  and nvxPoints = make_vect (2 * n) (0., 0.)
  and lgSousOpti = ref(0.) 
  and pptNonUtilise = ref(n) in
  
  let ponderation = calculer_ponderation vPoints in
  let lstAretesAAct = ref [(ponderation.(0), n); (ponderation.(1), n); 
                           (ponderation.(2), n)] in

  
  (* Copie de l'ancien vecteur dans l'agrandit *)
  for i = 0 to (n - 1) do 
    nvxPoints.(i) <- vPoints.(i)
  done;
  
  (* Initialisation des points de steiner, qui ne doivent 
  pas etre superposes par defaut *)
  for i = n to (2 * n - 1) do
    nvxPoints.(i) <- (random__float 500., random__float 500.)
  done;
  
  (* <areteSupprimee> contient les indices de l'arete supprimee
  pour creer le dernier arbre optimal. N'a de sens que si <ptAjoute> <> -1 *)
  let rec parcours_aretes ar ptAjoute areteSupprimee idx = match ar with
    | [] -> begin
        ajouter_point_sur areteSupprimee sousOptiArbre !pptNonUtilise idx;
        let (u, v) = areteSupprimee in
        
        lstAretesAAct := except (u, v) !lstAretesAAct;
        lstAretesAAct := except (v, u) !lstAretesAAct; 
        lstAretesAAct := (idx, ptAjoute) :: (u, ptAjoute) 
                         :: (v, ptAjoute) :: !lstAretesAAct;
        
        incr pptNonUtilise; 
      end
      
    | (i, j) :: s -> begin
      ajouter_point_sur (i, j) sousOptiArbre !pptNonUtilise idx;
      
      for i = n to (2 * n - 1) do
        nvxPoints.(i) <- (random__float 500., random__float 500.)
      done;
     
      Sys_lin_res__optimiser_positions anim sousOptiArbre nvxPoints (n) 
                          (!pptNonUtilise - n +1) delta nIter;
      
      
      let lg = longueur_arbre sousOptiArbre nvxPoints in
      if lg <. !lgSousOpti       
      then begin
        if ptAjoute <> (-1) then
          retirer_liaison meilleurArbre ptAjoute areteSupprimee
        ;
        ajouter_point_sur (i, j) meilleurArbre !pptNonUtilise idx;
        retirer_liaison sousOptiArbre !pptNonUtilise (i, j);
        
        lgSousOpti := lg;
        parcours_aretes s !pptNonUtilise (i, j) idx      
        
      end else begin
        retirer_liaison sousOptiArbre !pptNonUtilise (i, j);
        parcours_aretes s ptAjoute areteSupprimee idx
      end;
      
     end
  in
  
  ajouter_premiers_points_proximite meilleurArbre ponderation !pptNonUtilise;
  ajouter_premiers_points_proximite sousOptiArbre ponderation !pptNonUtilise;
  incr pptNonUtilise;
  
  for i = 3 to n - 1 do
    if feedbacks then begin 
      print_int i;
      print_string "/";
      print_int (n - 1);
      print_newline();
      
    end;
    lgSousOpti := (float_of_int valSup);

    
    parcours_aretes !lstAretesAAct (-1) (-1, -1) (ponderation.(i));
    
  done;
  
  for i = n to (2 * n - 1) do
    nvxPoints.(i) <- (random__float 500., random__float 500.)
  done;
  
  
 
  let mA = recomposer_vecteur (!pptNonUtilise ) meilleurArbre
  and mP = recomposer_vecteur (!pptNonUtilise ) nvxPoints in
  
  Sys_lin_res__optimiser_positions anim mA mP (n ) (vect_length mP - n ) delta nIter;
  
  (!lgSousOpti, mA, mP)
  
;;


let rand_vect n = 
  let v = make_vect n (0., 0.) in
  
  for i = 0 to n - 1 do
    v.(i) <- (random__float 500., random__float 500.)
  done;
  v
;;

let v2 = rand_vect 16;;
let a2, b2, c2 = heuristique_proximite v2 0.1 35 false;;

Sys_lin_res__afficher_FST c2 b2 15;;


let bel_arbre n essais = 
  let deltaM = ref 0.
  and bpts = ref [||]
  and barb = ref [||] in
  
  for i = 0 to essais - 1 do
    let v = rand_vect n in
    let lg, pts, arb = heuristique_proximite v 0.1 50 false in
    
    let lgACM, _ = Arbre_Couvrant_Minimal__calculer_ACM v in
    if ( lg /. lgACM) >. !deltaM 
    then begin
      bpts := pts;
      barb := arb;
      deltaM := lg /. lgACM
    end;
    
    print_float !deltaM;
    print_newline()
  done;
  
  !deltaM, !bpts, !barb
;;    


let a234, b234, c234 = bel_arbre 18 10;;
Sys_lin_res__afficher_FST c b 14;;



let conversion arb points nFixes =
  let s = ref "\\begin{tikzpicture}[scale = #1]\n\\begin{scope}[every node/.style={circle,thick,draw}, inner sep = 0pt, minimum width = 0.3cm]\n" in
  
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

print_string (conversion b c 16);;*)

(* Cette methode est un echec : plusieurs causes :
  > A tendance a creer de "super-points", des conglomerats ou s'accumulent 
  des dizaines d'aretes. => Necessite un plus grand nombre d'appel de la 
  resolution pour trouver des resultats precis
  
  > Ces memes conglomerats donnent un poid trop important a certaines zones du 
  graphe. L'ajout d'un point ailleurs ne va pas suffisament devier les aretes, 
  et des croisements vont etre observes. La longueur totale en prends un 
  serieux coup. *)
