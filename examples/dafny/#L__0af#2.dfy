function DfLength(s: seq<int>): int
{if s == [] then 0 else DfLength(s[..|s|-1]) + 1}

function Res(a : seq<bool>): bool
{
  if a == [] then
    false
    else
    (((! a[|a|-1]) && Seen1(a[..|a|-1])) || Res(a[..|a|-1]))
}

function Aux_res3(a : seq<bool>): bool
{
  if a == [] then false else ((! a[|a|-1]) || Aux_res3(a[..|a|-1]))
}

function Seen1(a : seq<bool>): bool
{
  if a == [] then false else (Seen1(a[..|a|-1]) || a[|a|-1])
}

function ResJoin(leftAux_res3 : bool, leftRes : bool, leftSeen1 : bool, rightAux_res3 : bool, rightRes : bool, rightSeen1 : bool): bool
{
  ((rightAux_res3 && leftSeen1) || ((rightAux_res3 && rightRes) || leftRes))
}

function Aux_res3Join(leftAux_res3 : bool, leftSeen1 : bool, rightAux_res3 : bool, rightSeen1 : bool): bool
{
  ((! rightSeen1) || (rightAux_res3 || leftAux_res3))
}

function Seen1Join(leftSeen1 : bool, rightSeen1 : bool): bool
{
  (rightSeen1 || (leftSeen1 || rightSeen1))
}


lemma BaseCaseRes(a : seq<bool>)
  ensures Res(a) == ResJoin(Aux_res3(a), Res(a), Seen1(a), Aux_res3([]), Res([]), Seen1([]))
  {}

lemma HomRes(a : seq<bool>, R_a : seq<bool>)
  ensures Res(a + R_a) == ResJoin(Aux_res3(a), Res(a), Seen1(a), Aux_res3(R_a), Res(R_a), Seen1(R_a))
  {
    if R_a == [] 
    {
    assert(a + [] == a);
    BaseCaseRes(a);
    
     } else {
    calc{
    Res(a + R_a);
    =={
      HomAux_res3(a, R_a[..|R_a| - 1]);
      HomSeen1(a, R_a[..|R_a| - 1]);
      assert(a + R_a[..|R_a|-1]) + [R_a[|R_a|-1]] == a + R_a;
      }
    ResJoin(Aux_res3(a), Res(a), Seen1(a), Aux_res3(R_a), Res(R_a), Seen1(R_a));
    } // End calc.
  } // End else.
} // End lemma.

lemma BaseCaseAux_res3(a : seq<bool>)
  ensures Aux_res3(a) == Aux_res3Join(Aux_res3(a), Seen1(a), Aux_res3([]), Seen1([]))
  {}

lemma HomAux_res3(a : seq<bool>, R_a : seq<bool>)
  ensures Aux_res3(a + R_a) == Aux_res3Join(Aux_res3(a), Seen1(a), Aux_res3(R_a), Seen1(R_a))
  {
    if R_a == [] 
    {
    assert(a + [] == a);
    BaseCaseAux_res3(a);
    
     } else {
    calc{
    Aux_res3(a + R_a);
    =={
      HomSeen1(a, R_a[..|R_a| - 1]);
      assert(a + R_a[..|R_a|-1]) + [R_a[|R_a|-1]] == a + R_a;
      }
    Aux_res3Join(Aux_res3(a), Seen1(a), Aux_res3(R_a), Seen1(R_a));
    } // End calc.
  } // End else.
} // End lemma.

lemma BaseCaseSeen1(a : seq<bool>)
  ensures Seen1(a) == Seen1Join(Seen1(a), Seen1([]))
  {}

lemma HomSeen1(a : seq<bool>, R_a : seq<bool>)
  ensures Seen1(a + R_a) == Seen1Join(Seen1(a), Seen1(R_a))
  {
    if R_a == [] 
    {
    assert(a + [] == a);
    BaseCaseSeen1(a);
    
     } else {
    calc{
    Seen1(a + R_a);
    =={ assert(a + R_a[..|R_a|-1]) + [R_a[|R_a|-1]] == a + R_a; }
    Seen1Join(Seen1(a), Seen1(R_a));
    } // End calc.
  } // End else.
} // End lemma.

