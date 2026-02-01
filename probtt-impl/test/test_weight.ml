(* Unit tests for weight algebra *)

let test name cond =
  if cond then
    Printf.printf "PASS: %s\n" name
  else begin
    Printf.printf "FAIL: %s\n" name;
    exit 1
  end

let () =
  let open Probtt_lib.Weight in

  test "zero is absorbing (left)" (equal (mul zero one) zero);
  test "zero is absorbing (right)" (equal (mul one zero) zero);
  test "one is identity (left)" (equal (mul one one) one);
  test "one is identity (right)" (equal (simplify (mul one (var "w"))) (var "w"));

  test "neg zero = one" (equal (neg zero) one);
  test "neg one = zero" (equal (neg one) zero);
  test "double negation" (equal (neg (neg one)) one);
  test "double negation var" (equal (simplify (neg (neg (var "w")))) (var "w"));

  test "zero <= anything" (leq zero one);
  test "zero <= var" (leq zero (var "w"));
  test "anything <= one" (leq (var "w") one);
  test "equal implies leq" (leq one one);

  test "mul simplifies to zero" (equal (simplify (mul (var "w") zero)) zero);
  test "mul simplifies identity" (equal (simplify (mul (var "w") one)) (var "w"));

  Printf.printf "\nAll weight tests passed!\n"
