sort natsr = {n:int | n >= 0};
type natty = [n:natsr. int(n)];
(3 + 4 : natty);
(3 - 4 : natty);
(1 + 2 * 3 : natty);
val a = 1 + 2 * 3;
val b = (a - 5 : natty);
val c = (a - 8 : natty);
fn (n:natty) : natty => n + 1 - 1 end;
fn (n:natty) : natty => n * (0 - 2) * (0 - 2) - 1 + 4 / 2 - 2 + 1 end;
fun fib (n:natty) : natty = if n <= 1 then 1 else [fib (n - 1)] + [fib (n - 2)];
rec fac (n:natty) : natty => if n = 0 then 1 else n * [fac (n - 1)] end;
[fib 20];
val d = 5.0;
val e = 5 > 4;
val f = (if 4 < 5 && 5 < 4 then true else false : bool(false));
sort somesr = {n:int | n >= 0 - 1 && n <= 1 };
fn {a:somesr} (n:int(a)) : [c:somesr. int(c)] => 0 - n end;
val d = 5.0 +. 4.0;
val dd = (if 5.0 +. 4.0 >. 7.9 then 1 else 2 : natty);
declare make_vec : {n:natsr. int(n) -> vec(n)};
declare make_mat : {m:natsr. {n:natsr. int(m) * int(n) -> mat(m,n)}};
declare mul_mat_vec : {m:natsr. {n:natsr. mat(m,n) * vec(n) -> vec(m)}};
declare mul_vec_mat : {m:natsr. {n:natsr. vec(m) * mat(m,n) -> vec(n)}};
declare mul_mat_mat : {m:natsr. {n:natsr. {k:natsr. mat(m,k) * mat(k,n) -> mat(m,n)}}};
val v = [make_vec a];
val m = [make_mat (a - 2,a)];
mul_mat_vec;
val v = [mul_mat_vec (m,v)];
[mul_mat_vec (m,v)];
mul_vec_mat;
[mul_vec_mat (v,m)];
mul_mat_mat;
[mul_mat_mat ([make_mat (1,2)], [make_mat (2,1)])];
[mul_mat_mat ([make_mat (3,4)], [make_mat (3,4)])];
[mul_mat_mat ([make_mat (8,9)], [make_mat (9,7)])];
fun comb (n:natty) (m:natty) : natty =
  if n < m then 0
  else
    if m = 0 then 1
    else
      [comb (n - 1) (m - 1)] + [comb (n - 1) m];
();
declare read_nat : unit -> natty;
let m = [read_nat ()] in
  let n = [read_nat ()] in
    [mul_mat_vec ([make_mat (m,n+1)], [make_vec (n+1)])];
declare not : {b:bool. bool(b) -> bool(~b)};
declare some_b : bool;
let b = some_b in
  (if b then [not b] else b : bool(false));
