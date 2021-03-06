function DfLength(s: seq<int>): int
{if s == [] then 0 else DfLength(s[..|s|-1]) + 1}

function Aux_2(a : seq<bool>): bool
{
  if a == [] then false else ((! a[|a|-1]) || Aux_2(a[..|a|-1]))
}

function Seen1(a : seq<bool>): bool
{
  if a == [] then false else (Seen1(a[..|a|-1]) || a[|a|-1])
}

function Res(a : seq<bool>): bool
{
  if a == [] then
    false
    else
    (((! a[|a|-1]) && Seen1(a[..|a|-1])) || Res(a[..|a|-1]))
}

function Aux_2Join(leftAux_2 : bool, rightAux_2 : bool): bool
{
  (leftAux_2 || rightAux_2)
}

function Seen1Join(leftRes : bool, leftSeen1 : bool, rightRes : bool, rightSeen1 : bool): bool
{
  (rightRes || (rightSeen1 || leftSeen1))
}

function ResJoin(leftAux_2 : bool, leftRes : bool, leftSeen1 : bool, rightAux_2 : bool, rightRes : bool, rightSeen1 : bool): bool
{
  ((leftSeen1 && (rightAux_2 && true)) || (leftRes || rightRes))
}


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
  ensures Seen1(a) == Seen1Join(Res(a), Seen1(a), Res([]), Seen1([]))
  {}

lemma HomSeen1(a : seq<bool>, R_a : seq<bool>)
  ensures Seen1(a + R_a) == Seen1Join(Res(a), Seen1(a), Res(R_a), Seen1(R_a))
  {
    if R_a == [] 
    {
    assert(a + [] == a);
    BaseCaseSeen1(a);
    
     } else {
    calc{
    Seen1(a + R_a);
    =={
      HomRes(a, R_a[..|R_a| - 1]);
      assert(a + R_a[..|R_a|-1]) + [R_a[|R_a|-1]] == a + R_a;
      }
    Seen1Join(Res(a), Seen1(a), Res(R_a), Seen1(R_a));
    } // End calc.
  } // End else.
} // End lemma.

lemma BaseCaseRes(a : seq<bool>)
  ensures Res(a) == ResJoin(Aux_2(a), Res(a), Seen1(a), Aux_2([]), Res([]), Seen1([]))
  {}

lemma HomRes(a : seq<bool>, R_a : seq<bool>)
  ensures Res(a + R_a) == ResJoin(Aux_2(a), Res(a), Seen1(a), Aux_2(R_a), Res(R_a), Seen1(R_a))
  {
    if R_a == [] 
    {
    assert(a + [] == a);
    BaseCaseRes(a);
    
     } else {
    calc{
    Res(a + R_a);
    =={
      HomAux_2(a, R_a[..|R_a| - 1]);
      HomSeen1(a, R_a[..|R_a| - 1]);
      assert(a + R_a[..|R_a|-1]) + [R_a[|R_a|-1]] == a + R_a;
      }
    ResJoin(Aux_2(a), Res(a), Seen1(a), Aux_2(R_a), Res(R_a), Seen1(R_a));
    } // End calc.
  } // End else.
} // End lemma.

