let path = "/Users/LoicJouans/Desktop/TIPE 5:2/Steiner - Exact";;
#open "graphics";;
load ("/Users/LoicJouans/Desktop/TIPE 5:2/Code Caml Propre/Sys_lin_res");;
	let pi = 4.0 *. atan 1.0;;
let eps_float = 1e-7;;
(* Vrai si l'on veut afficher la progression *)
let feedbacks = false;;
let val_sup = float_of_int (2 lsl 61 - 1);;


type Arbre = N of int * Arbre * Arbre | Nil;;




 

(* ---------------------------- *)
(* - MANIPULATION DE VECTEURS - *)
(* ---------------------------- *)
let vec a b = (fst b -. fst a, snd b -. snd a);;
let sum u v = (fst u +. fst v, snd u +. snd v);;
let div u scal = (fst u /. scal, snd u /. scal);;
let mult u scal = (fst u *. scal, snd u *. scal);;
let scal u v = (fst u) *. (fst v) +. (snd u) *. (snd v);;

let dst (ax, ay) (bx, by) = 
  sqrt ((bx -. ax)*.(bx -. ax) +. (by -. ay)*.(by -. ay));;

let norme v = dst (0., 0.) v;;


(* Distance entre deux points, pour legerement plus de lisibilite *)
let dst_points points indPt indV =
  dst (points.(indPt)) (points.(indV))  
;;

(* On utilise la methode de resolution de Smith

On peut s'arreter soit lorsque les angles aux points de Steiner sont a epsilon 
pres de 120 degres ou au bout d'un nombre impose d'iterations.

La fonction principale renverra un vecteur de coordonnees (n - 2 points de 
steiner, n points fixes) ainsi que la longueur totale du chemin
	
	
TYPE : 
  Nous considerons un arbre code sous forme de liste d'ajdacence, avec un
tableau global contenant la position des points.
  
  Pour la conversion du str a la liste d'adjacence, on passe par la structure
d'arbre binaire


/!\ DANGER /!\ Par soucis de simplicite, et contrairement a la premiere partie, 
les points fixes SONT LES <n> PREMIERS POINTS
*)



(* --------------------------- *)
(* ------ RECUPERATION ------- *)
(* --------------------------- *)

(* Trouve l'indice d'une virgule dans une sous-chaine de caracteres  
(specifique au format d'encodage des arbres de Steiner) *)
let trouver_virgule strg ideb ifin =
  if (ifin - ideb <= 2) then ideb
  else begin
    let nbP = ref(0) 
    and idx = ref(ideb + 2) in
  
    if (strg.[ideb + 1] = `(`) then incr nbP;
    while (!idx < ifin) && (!nbP > 0) do
      begin match strg.[!idx] with
      | `(` -> incr nbP
      | `)` -> decr nbP
      | _ -> ()
      end;
      incr idx
    done;
 
    while (!idx < ifin) && (!nbP = 0) && (strg.[!idx] <> `,`) do
      incr idx; 
    done;
  
    !idx
  end
;; 



(* Conversion str (issu du fichier) -> ABR (defini plus haut) *)
let abr_of_str n strg =
  
  let mLibre = ref n in
  
  let rec decode ideb ifin =      
    let imid = trouver_virgule strg ideb ifin in
    
    if (strg.[imid] <> `,`) 
    then begin 
      let e =  begin
        if ifin = ideb 
        then int_of_char (strg.[ideb]) - int_of_char `0`
        else int_of_string (sub_string strg ideb (ifin - ideb))
      end in
      
      N(e - 1, Nil, Nil)
      
    end else begin
      let a = N(!mLibre, decode (ideb + 1) (imid - 1), 
                         decode (imid + 1) (ifin - 1)) in   
      incr mLibre;
      a
    end
  
  in
  
  decode 0 (string_length strg)
;;



(* Conversion ABR (defini) -> liste d'adjacences *)
let rec tab_of_tree tab arb = match arb with
  | N(e, Nil, Nil) -> e
  | N(e, fg, fd) -> 
    let ig = tab_of_tree tab fg
    and id = tab_of_tree tab fd in

    tab.(e) <- ig :: tab.(e);
    tab.(ig) <- e :: tab.(ig);
    tab.(e) <- id :: tab.(e);
    tab.(id) <- e :: tab.(id);
    
    e
  |_ -> failwith "Structure d'ABR non respectee <err <tab_of_tree>"
;;



(* Conversion str (fichier) -> liste d'adjecences *)
let fst_of_str n strg = 
  let v = make_vect (2*n - 2) [] in
  let e = tab_of_tree v (abr_of_str n strg) in
  
  (* Mais, dans notre encodage, nous n'avons pas note le sommet d'indice 0 !*)
  v.(0) <- [e];
  v.(e) <- 0 :: v.(e);
  
  v 
;;



let lire_repClassesEtq n =  
  let fich = open_in (path^"/repClassesEtiquetes_"^(string_of_int n)^".txt") 
  in
  
  let listeArb = ref([]) in  
  begin try 
  
    while true do
      let a = (fst_of_str n (input_line fich)) in
      listeArb := a :: (!listeArb)      
    done
  
  with End_of_file -> () 
  end;
  
  !listeArb
;;    





(* ----------------------------------- *)
(* --- RECHERCHE DU MEILLEUR ARBRE --- *)
(* ----------------------------------- *)



(* Calcul l'angle forme par les trois points avec la formule : 
(u|v)/(||u||||v||) = cos(u, v) *)

let calculer_angle points i1 i2 i3 eps = 
  let u = vec points.(i2) points.(i1)
  and v = vec points.(i2) points.(i3) in
  
  let nu = max (norme u) (eps) 
  and nv = max (norme u) (eps) in
  (* ON NE FAIT PAS DE TEST DE NORME ! *)
  acos ((scal u v) /. (nu *. nv))
;;



(* Calcul le modulo 2pi *)
let mod_2pi f = 
  if (f < 0.) then f +. pi
  else if (f > 2. *. pi) then f -. 2. *. pi 
  else f
;;



(* Parcours l'arbre et calcul chaque angle : si TOUS sont a plus de 120 
degres, on arete les calculs *)
let condition_angulaire eps points graphe =
  let rec parcours_voisins eps indPere indPoint = 
    match (graphe.(indPoint)) with
    | [a] -> true
    | a :: b :: [c] -> 
      let [fg; fd] = except indPere [a; b; c] in
      let va = points.(a)
      and vb = points.(b)
      and vpR = points.(indPere)
      and vpt = points.(indPoint) in
    
      (mod_2pi (calculer_angle points a b c eps) >= 2.0944) && 
      (parcours_voisins eps indPoint a) && 
      (parcours_voisins eps indPoint b)    
    | _ -> failwith "Mauvais objet <parcours_voisins <condition_angulaire"
  
  in parcours_voisins eps 0 (hd graphe.(0))
;;


(* Initialise les futur points de Steiner (qui ne doivent pas, par defaut, 
etre superposes *)
let init pts =
  let n = vect_length pts in
  
  let vP = make_vect (2 * n - 2) (0., 0.) in
  
  for i = 0 to n - 1 do
    vP.(i) <- pts.(i)
  done;
  
  for i = n to 2 * n - 3 do
    vP.(i) <- (random__float 500., random__float 500.)
  done;
  
  vP
;;
  


(* R.A.Z. des positions des points de Steiner : deux points ne doivent pas 
etre superposes lors de la resolution du systeme *)
let reset_pos_steiner points nbPtExt = 
  for i = 0 to nbPtExt - 3 do
    points.(nbPtExt + i) <- (random__float 1000., random__float 800.)
  done
;;



(* Calcul de la longueur totale de l'arbre *)  
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



(* Recopie la position des points de Steiner *)
let copier_steiner nP p = 
  let n = vect_length p in
  for i = n/2 + 1 to n - 1 do
    nP.(i) <- p.(i)
  done
;;




(* Parcours toutes les topologies, resout les systemes, et selectionne la 
meilleur *)
let calcul_positions anim pts eps delta iterMax =

  let points = init pts
  and n = vect_length pts 
  and avancement = ref(0) in
  
  let listeFST = lire_repClassesEtq n in
  let nbTotRep = list_length listeFST in
  let fstMin = ref(hd listeFST) in
  
  let ptsMin = copy_vect points in 
  let lgMin = ref(longueur_FST !fstMin points) in
  
  let rec parcours_liste = function 
    | [] -> ()
    | a :: su -> begin
      let nIter = ref(0) in
      reset_pos_steiner points n;
             
      while (!nIter < iterMax) && (not condition_angulaire eps points a) do
        Sys_lin_res__resoudre_systeme a points n (n - 2) delta;
        incr nIter;
        
        if anim then begin
          open_graph "1000x800";
          clear_graph ();
          Sys_lin_res__afficher_FST points a n;

          Sys_lin_res__wait 0.01
        end
        done;
        
        if feedbacks then begin 
          print_int !avancement;
          print_string " / ";
          print_int nbTotRep;
          print_newline();
        end; 
        
        incr avancement;
        
        let lgAct = longueur_FST a points in
        if lgAct < !lgMin 
        then begin
          lgMin := lgAct;
          fstMin := a;
          copier_steiner ptsMin points
        end;
      
        parcours_liste su
      end
  
  in parcours_liste listeFST;
  
  (!lgMin, !fstMin, ptsMin)
;;

let pts = [|(0., 0.); (0., 100.); (200., 100.); (200., 0.); (400., 100.); (400., 0.)|];;