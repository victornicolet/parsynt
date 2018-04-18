function DfLength(s: seq<int>): int
{if s == [] then 0 else DfLength(s[..|s|-1]) + 1}

function Res(a : seq<bool>): bool
{
  if a == [] then
    false
    else
    (((! a[|a|-1]) && Seen1(a[..|a|-1])) || Res(a[..|a|-1]))
}

function Aux_2(a : seq<bool>): bool
{
  if a == [] then false else ((! a[|a|-1]) || Aux_2(a[..|a|-1]))
}

function Seen1(a : seq<bool>): bool
{
  if a == [] then false else (Seen1(a[..|a|-1]) || a[|a|-1])
}

function ResJoin(leftRes : bool, leftSeen1 : bool, leftAux_2 : bool, rightRes : bool, rightSeen1 : bool, rightAux_2 : bool): bool
{
  (((rightAux_2 || rightAux_2) && (leftSeen1 && rightAux_2)) || (rightRes || leftRes))
}

function Aux_2Join(leftAux_2 : bool, rightAux_2 : bool): bool
{
  (leftAux_2 || (rightAux_2 || rightAux_2))
}

function Seen1Join(leftSeen1 : bool, leftAux_2 : bool, rightSeen1 : bool, rightAux_2 : bool): bool
{
  ((! rightAux_2) || (rightSeen1 || leftSeen1))
}


lemma BaseCaseRes(a : seq<bool>)
  ensures Res(a) == ResJoin(Res(a), Seen1(a), Aux_2(a), Res([]), Seen1([]), Aux_2([]))
  {}

lemma HomRes(a : seq<bool>, R_a : seq<bool>)
  ensures Res(a + R_a) == ResJoin(Res(a), Seen1(a), Aux_2(a), Res(R_a), Seen1(R_a), Aux_2(R_a))
  {
    if R_a == [] 
    {
    assert(a + [] == a);
    BaseCaseRes(a);
    
     } else {
    calc{
    Res(a + R_a);
    =={
      HomSeen1(a, R_a[..|R_a| - 1]);
      HomAux_2(a, R_a[..|R_a| - 1]);
      assert(a + R_a[..|R_a|-1]) + [R_a[|R_a|-1]] == a + R_a;
      }
    ResJoin(Res(a), Seen1(a), Aux_2(a), Res(R_a), Seen1(R_a), Aux_2(R_a));
    } // End calc.
  } // End else.
} // End lemma.

lemma BaseCaseAux_2(a : seq<bool>)
  ensures Aux_2(a) == Aux_2Join(Aux_2(a), Aux_2([]))
  {}

lemma HomAux_2(a : seq<bool>, R_a : seq<bool>)
  ensures Aux_2(a + R_a) == Aux_2Join(Aux_2(a), Aux_2(R_a))
  {
    if R_a == [] 
    {
    assert(a + [] == a);
    BaseCaseAux_2(a);
    
     } else {
    calc{
    Aux_2(a + R_a);
    =={ assert(a + R_a[..|R_a|-1]) + [R_a[|R_a|-1]] == a + R_a; }
    Aux_2Join(Aux_2(a), Aux_2(R_a));
    } // End calc.
  } // End else.
} // End lemma.

lemma BaseCaseSeen1(a : seq<bool>)
  ensures Seen1(a) == Seen1Join(Seen1(a), Aux_2(a), Seen1([]), Aux_2([]))
  {}

lemma HomSeen1(a : seq<bool>, R_a : seq<bool>)
  ensures Seen1(a + R_a) == Seen1Join(Seen1(a), Aux_2(a), Seen1(R_a), Aux_2(R_a))
  {
    if R_a == [] 
    {
    assert(a + [] == a);
    BaseCaseSeen1(a);
    
     } else {
    calc{
    Seen1(a + R_a);
    =={
      HomAux_2(a, R_a[..|R_a| - 1]);
      assert(a + R_a[..|R_a|-1]) + [R_a[|R_a|-1]] == a + R_a;
      }
    Seen1Join(Seen1(a), Aux_2(a), Seen1(R_a), Aux_2(R_a));
    } // End calc.
  } // End else.
} // End lemma.

