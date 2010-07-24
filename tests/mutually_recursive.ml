type expr1 = 
  | Plus of expr1 * expr1
  | Minus of expr1 * expr2
  | Mult of expr2

and expr2 = 
  | EndExpr2
  | Expr1 of expr1
 (* with tarzan *)
