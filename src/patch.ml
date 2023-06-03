open Typegist

type 'a t =
  | Scalar : 'a Type.Gist.scalar * 'a -> 'a t
  | List : [ `Patch of 'a t | `Value of 'a ] list -> 'a list t
  | Record : 'a record -> 'a t
  | Empty

and 'a record = { fields : ('a, 'a) field_patches }

and ('a, 'b) field_patches =
  | Ctor : 'c -> ('a, 'c) field_patches
  | App :
      ('a, 'b) Type.Gist.field * 'b t * ('a, 'b -> 'c) field_patches
      -> ('a, 'c) field_patches

let empty = Empty

(* A notion of equality across all constructors for type gists... maybe? *)
type (_, _) eq =
  | Eq : ('a, 'a) eq

exception Not_equal

let fun_eq : type d1 d2 r1 r2. (d1, d2) eq -> (r1, r2) eq -> (d1 -> r1, d2 -> r2) eq = fun Eq Eq -> Eq
let dom_eq : type a b c d. (a -> b, c -> d) eq -> (a, c) eq -> (b, d) eq = fun Eq Eq -> Eq

let arr_eq : type elt1 elt2. (elt1, elt2) eq -> (elt1 array, elt2 array) eq = fun Eq -> Eq
let ba_eq : type kind1 layout1 elt1 kind2 layout2 elt2.
  (kind1, kind2) eq ->
  (layout1, layout2) eq ->
  (elt1, elt2) eq ->
  ((elt1, kind1, layout1) Bigarray.Array1.t, (elt2, kind2, layout2) Bigarray.Array1.t) eq =
  fun Eq Eq Eq -> Eq

let eq_bigarray_kind : type k k' b b'. (k, b) Bigarray.kind -> (k', b') Bigarray.kind -> (b, b') eq = fun v1 v2 ->
  match v1, v2 with
  | Float32, Float32 -> Eq
  | Float64, Float64 -> Eq
  | Int8_signed , Int8_signed -> Eq
  | Int8_unsigned, Int8_unsigned -> Eq
  | Int16_signed, Int16_signed -> Eq
  | Int16_unsigned, Int16_unsigned -> Eq
  | Int32, Int32 -> Eq
  | Int64, Int64 -> Eq
  | Int, Int -> Eq
  | Nativeint , Nativeint -> Eq
  | Complex32, Complex32 -> Eq
  | Complex64, Complex64 -> Eq
  | Char, Char -> Eq
  | _ -> raise Not_equal

let eq_bigarray_layout : type l l'. l Bigarray.layout -> l' Bigarray.layout -> (l, l') eq = fun v1 v2 ->
  match v1, v2 with
  | C_layout, C_layout -> Eq
  | Fortran_layout, Fortran_layout -> Eq
  | _ -> raise Not_equal

let rec eq_gist : type a b. a Type.Gist.t -> b Type.Gist.t -> (a, b) eq = fun v1 v2 ->
  let open Type.Gist in
  match v1, v2 with
  | Scalar (Int _), Scalar (Int _) -> Eq
  | Scalar (Float _), Scalar (Float _) -> Eq
  | Scalar (Unit _), Scalar (Unit _) -> Eq
  | Scalar (Bool _), Scalar (Bool _) -> Eq
  | Scalar (Char _), Scalar (Char _) -> Eq
  | Scalar (Uchar _), Scalar (Uchar _) -> Eq
  | Scalar (Nativeint _), Scalar (Nativeint _) -> Eq
  | Scalar (Int64 _), Scalar (Int64 _) -> Eq
  | Scalar (Int32 _), Scalar (Int32 _) -> Eq
  | Record r1, Record r2 -> eq_record r1 r2
  | Product p1, Product p2 -> eq_record p1 p2
  | Func f1, Func f2 ->
    let dom_eq = eq_gist (Func.domain f1) (Func.domain f2) in
    let range_eq = eq_gist (Func.range f1) (Func.range f2) in
    fun_eq dom_eq range_eq
  | Arraylike a1, Arraylike a2 ->
    eq_arraylike a1 a2
  | Maplike m1, Maplike m2 ->
    eq_maplike m1 m2
  | Sum s1, Sum s2 -> eq_sum s1 s2
  | Abstract a1, Abstract a2 -> (
      match Abstract.reprs a1, Abstract.reprs a2 with
      | x1 :: _, x2 :: _ -> (
          match x1, x2 with
          | Repr r1, Repr r2 ->
            let g1 = Abstract.Repr.gist r1 in
            let g2 = Abstract.Repr.gist r2 in
            let e = eq_gist g1 g2 in
            (* We've proved the priority representation is the same. *)
            Obj.magic e
        )
      | _ -> raise Not_equal
    )
  | Lazy (_, l1), Lazy (_, l2) ->
    let eq_lazy : type a b. (a, b) eq -> (a lazy_t, b lazy_t) eq = fun Eq -> Eq in
    eq_lazy (eq_gist l1 l2)
  | Ref (_, r1), Ref (_, r2) ->
    let eq_lazy : type a b. (a, b) eq -> (a ref, b ref) eq = fun Eq -> Eq in
    eq_lazy (eq_gist r1 r2)
  | Rec l1, Rec l2 -> eq_gist (Lazy.force l1) (Lazy.force l2)
  | _ -> raise Not_equal


and eq_record : type a b. a Type.Gist.record -> b Type.Gist.record -> (a, b) eq = fun r1 r2 ->
  let open Type.Gist in
  let fields1 = Record.fields r1 in
  let fields2 = Record.fields r2 in
  let rec loop : type a b f g. (a, f) Type.Gist.fields -> (b, g) Type.Gist.fields -> (f, g) eq = fun f1 f2 ->
    match f1, f2 with
    | Ctor _, Ctor _ -> Obj.magic Eq
    | App (next1, f1), App (next2, f2) -> (
        let name_eq = String.equal (Type.Gist.Field.name f1) (Type.Gist.Field.name f2) in
        if not name_eq then raise Not_equal;
        let f = eq_gist (Type.Gist.Field.gist f1) (Type.Gist.Field.gist f2) in
        let f_next = loop next1 next2 in
        dom_eq f_next f
      )
    | _ -> raise Not_equal
  in
  loop fields1 fields2

and eq_arraylike : type elt1 arr1 elt2 arr2. (elt1, arr1) Type.Gist.arraylike ->(elt2, arr2) Type.Gist.arraylike -> (arr1, arr2) eq = fun a1 a2 ->
  match a1, a2 with
  | String _, String _ -> Eq
  | Bytes _, Bytes _ -> Eq
  | Array (_, elt1), Array (_, elt2) -> arr_eq (eq_gist elt1 elt2)
  | Bigarray1 (_, kind1, layout1, gist1), Bigarray1 (_, kind2, layout2, gist2) ->
    let g_eq = eq_gist gist1 gist2 in
    let k_eq = eq_bigarray_kind kind1 kind2 in
    let l_eq = eq_bigarray_layout layout1 layout2 in
    ba_eq k_eq l_eq g_eq
  | Array_module (_, (module A1), elt1), Array_module (_, (module A2), elt2) ->
    let e_eq = eq_gist elt1 elt2 in
    (* No way to actually prove the type constructor is equal :(
       so we just check the name... *)
    let c_eq = String.equal A1.type_gist_name A2.type_gist_name in
    if not c_eq then raise Not_equal;
    Obj.magic e_eq
  | _ -> raise Not_equal

and eq_maplike : type k1 v1 map1 k2 v2 map2. (k1, v1, map1) Type.Gist.maplike -> (k2, v2, map2) Type.Gist.maplike -> (map1, map2) eq = fun a1 a2 ->
  match a1, a2 with
  | Hashtbl (_, k1, v1), Hashtbl (_, k2, v2) ->
    let eq_hashtbl : type k1 v1 k2 v2. (k1, k2) eq -> (v1, v2) eq -> ((k1, v1) Hashtbl.t, (k2, v2) Hashtbl.t) eq = fun Eq Eq -> Eq in
    eq_hashtbl (eq_gist k1 k2) (eq_gist v1 v2)
  | Map_module (_, (module M1), k1, v1), Map_module (_, (module M2), k2, v2) ->
    let Eq = eq_gist k1 k2 in
    let Eq = eq_gist v1 v2 in
    (* No way to actually prove the type constructor is equal :(
        so we just check the name... *)
    let c_eq = String.equal M1.type_gist_name M2.type_gist_name in
    if not c_eq then raise Not_equal;
    Obj.magic c_eq
  | _ -> raise Not_equal

and eq_sum : type s1 s2. s1 Type.Gist.sum -> s2 Type.Gist.sum -> (s1, s2) eq = fun s1 s2 ->
  match s1, s2 with
  | Option (_, o1), Option (_, o2) ->
    let eq_option : type a b. (a, b) eq -> (a option, b option) eq = fun Eq -> Eq in
    eq_option @@ eq_gist o1 o2
  | Result (_, ok1, err1), Result (_, ok2, err2) ->
    let eq_result : type o1 o2 e1 e2. (o1, o2) eq -> (e1, e2) eq -> ((o1, e1) result, (o2, e2) result) eq = fun Eq Eq -> Eq in
    eq_result (eq_gist ok1 ok2) (eq_gist err1 err2)
  | List (_, l1), List (_, l2) ->
    let eq_list : type a b. (a, b) eq -> (a list, b list) eq = fun Eq -> Eq in
    eq_list (eq_gist l1 l2)
  | Variant v1, Variant v2 -> eq_variant v1 v2
  | _ -> assert false

and eq_variant : type v1 v2. v1 Type.Gist.variant -> v2 Type.Gist.variant -> (v1, v2) eq = fun v1 v2 ->
  let open Type.Gist in
  let b = String.equal (Variant.name v1) (Variant.name v2) in
  if not b then raise Not_equal;
  let v1s = Variant.cases v1 in
  let v2s = Variant.cases v2 in
  let rec loop : type a b. a product list -> b product list -> (a, b) eq list -> (a, b) eq list = fun p1 p2 acc -> match p1, p2 with
    | [], [] -> acc
    | p1::p1s, p2::p2s ->
      let e = eq_record p1 p2 in
      loop p1s p2s (e :: acc)
    | _ -> raise Not_equal
  in
  let eq_list : type a b. (a, b) eq list -> (a, b) eq = fun lst -> List.hd lst in
  eq_list @@ loop v1s v2s []

let equal_gist v1 v2 = try Some (eq_gist v1 v2) with Not_equal -> None

let rec join : type a. a t -> a t -> a t =
  fun a b ->
  match (a, b) with
  | a, Empty -> a
  | Empty, b -> b
  | Scalar (Unit m, ()), Scalar (Unit _, ()) -> Scalar (Unit m, ())
  | Scalar (Bool b, _), Scalar (Bool _, b2) -> Scalar (Bool b, b2)
  | Scalar (Char c, _), Scalar (Char _, b2) -> Scalar (Char c, b2)
  | Scalar (Float f, _), Scalar (Float _, f2) -> Scalar (Float f, f2)
  | Scalar (Int i, i1), Scalar (Int _, i2) -> Scalar (Int i, i1 + i2)
  | List l1, List l2 ->
    let rec aux acc a b =
      match (a, b) with
      | [], l2s -> List.rev acc @ l2s
      | l1s, [] -> List.rev acc @ l1s
      | `Patch p1 :: l1s, `Patch p2 :: l2s ->
        aux (`Patch (join p1 p2) :: acc) l1s l2s
      | `Patch _ :: l1s, `Value v2 :: l2s -> aux (`Value v2 :: acc) l1s l2s
      | `Value v1 :: l1s, `Patch _ :: l2s -> aux (`Value v1 :: acc) l1s l2s
      | `Value v1 :: l1s, `Value _ :: l2s -> aux (`Value v1 :: acc) l1s l2s
    in
    List (aux [] l1 l2)
  | Record p1, Record p2 ->
    let rec merge :
      type a b.
      (a, b) field_patches -> (a, b) field_patches -> (a, b) field_patches =
      fun a b ->
        match (a, b) with
        | Ctor c, Ctor _ -> Ctor c
        | App (f1, p1, next1), App (f2, p2, next2) -> (
            match equal_gist (Type.Gist.Field.gist f1) (Type.Gist.Field.gist f2) with
            | Some Eq -> App (f1, join p1 p2, merge next1 next2)
            | None -> failwith "Failed to prove fields equal type!"
          )
        | _ -> assert false
    in
    Record { fields = merge p1.fields p2.fields }
  | _ -> assert false


let rec diff : type a. a Type.Gist.t -> a -> a -> a t =
  fun typ v1 v2 ->
  match typ with
  | Scalar (Unit v) -> Scalar (Unit v, ())
  | Scalar (Int v) -> Scalar (Int v, v2 - v1)
  | Scalar (Int32 v) -> Scalar (Int32 v, Int32.sub v2 v1)
  | Scalar (Int64 v) -> Scalar (Int64 v, Int64.sub v2 v1)
  | Scalar (Char v) -> Scalar (Char v, v2)
  | Scalar (Uchar v) -> Scalar (Uchar v, v2)
  | Scalar (Bool v) -> Scalar (Bool v, v2)
  | Scalar (Nativeint v) -> Scalar (Nativeint v, Nativeint.sub v2 v1)
  (* Probably better off just keeping the second value for floats *)
  | Scalar (Float v) -> Scalar (Float v, v2)
  | Record r -> diff_record r v1 v2
  | _ -> assert false

and diff_record : type a. a Type.Gist.record -> a -> a -> a t =
  fun record v1 v2 ->
  let fields = Type.Gist.Record.fields record in
  let rec loop : type f. (a, f) Type.Gist.fields -> (a, f) field_patches =
    function
    | Ctor c -> Ctor c
    | App (fs, field) ->
      let fpatch = loop fs in
      let ftype = Type.Gist.Field.gist field in
      let p =
        diff ftype
          (Type.Gist.Field.project field v1)
          (Type.Gist.Field.project field v2)
      in
      App (field, p, fpatch)
  in
  Record { fields = loop fields }

and apply : type a. a t -> a -> a =
  fun p v ->
  match p with
  | Scalar (Int _, i) -> v + i
  | Scalar (Bool _, i) -> i
  | List lst ->
    let rec aux acc patches vs =
      match (patches, vs) with
      | `Patch p :: ps, v :: vs -> aux (apply p v :: acc) ps vs
      | `Value v :: ps, [] -> aux (v :: acc) ps []
      | [], vs -> List.rev acc @ vs
      | _, [] -> assert false
      | `Value v :: ps, _ :: _ -> aux (v :: acc) ps []
    in
    aux [] lst v
  | Record re ->
    let rec loop : type f. (a, f) field_patches -> f = function
      | Ctor constructor -> constructor
      | App (field, p, fs) ->
        let f = loop fs in
        let p = apply p (Type.Gist.Field.project field v) in
        f p
    in
    loop re.fields
  | _ -> assert false
