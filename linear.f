sort natsr = {n:int | n >= 0};
type natty = [n:natsr. int(n)];

declare print_float : float -> unit;
declare float_of_int : int -> float;
declare snd : vec * float -> float;

declare read_nat : unit -> natty;
declare read_vec : {a:natsr. int(a) -> vec(a)};
declare read_mat : {a:natsr. {b:natsr. int(a) * int(b) -> mat(a,b)}};

declare make_vec : {a:natsr. int(a) -> float -> vec(a)};
declare append_col : {a:natsr. {b:natsr. mat(a,b) * vec(a) -> mat(a,b+1)}};

declare dim1_mat : {a:natsr. {b:natsr. mat(a,b) -> int(a)}};
declare dim_vec : {a:natsr. vec(a) -> int(a)};

declare sub_vec : {a:natsr. vec(a) * vec(a) -> vec(a)};
declare div_vec : {a:natsr. vec(a) * vec(a) -> vec(a)};
declare dot_vec : {a:natsr. vec(a) * vec(a) -> float};
declare transpose_mat : {a:natsr. {b:natsr. mat(a,b) -> mat(b,a)}};
declare mul_mat_vec : {a:natsr. {b:natsr. mat(a,b) * vec(b) -> vec(a)}};

declare gradient_descent :
  {a:natsr. {b:natsr. mat(a,b) -> vec(a) ->
  (mat(a,b) -> vec(a) -> vec(b) -> float) ->
  (mat(a,b) -> vec(a) -> vec(b) -> vec(b)) ->
  float -> vec(b) * float}};

fun cost {a:natsr} {b:natsr} (x:mat(a,b)) (y:vec(a)) (omega:vec(b)) : float =
  let v = [sub_vec (y,[mul_mat_vec (x,omega)])] in
    [dot_vec (v,v)] /. ([float_of_int [dim1_mat x]] *. 2.0);

fun derive {a:natsr} {b:natsr} (x:mat(a,b)) (y:vec(a)) (omega:vec(b)) : vec(b) =
  [div_vec (
    [mul_mat_vec ([transpose_mat x],[sub_vec ([mul_mat_vec (x,omega)],y)])],
    [make_vec [dim_vec omega] [float_of_int [dim1_mat x]]]
  )];

fun train {a:natsr} {b:natsr} (x:mat(a,b)) (y:vec(a)) (eta:float) : vec(b+1) * float =
  let m = [dim1_mat x] in
  let xx = [append_col (x,[make_vec m 1.0])] in
    [gradient_descent xx y cost derive eta];

let m = [read_nat ()] in
let n = [read_nat ()] in
let x = [read_mat (m,n)] in
let y = [read_vec m] in
let loss = [snd [train x y 0.1]] in
  [print_float loss];
