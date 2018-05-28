function DfLength(s: seq<int>): int
{if s == [] then 0 else DfLength(s[..|s|-1]) + 1}

function Res(a : seq<bool>): bool
{
  if a == [] then
    false
    else
    (((! a[|a|-1]) && Seen1(a[..|a|-1])) || Res(a[..|a|-1]))
}

function Aux1(a : seq<bool>): bool
{
  if a == [] then false else ((! a[|a|-1]) || Aux1(a[..|a|-1]))
}

function Seen1(a : seq<bool>): bool
{
  if a == [] then false else (Seen1(a[..|a|-1]) || a[|a|-1])
}

function ResJoin(leftAux1 : bool, leftRes : bool, leftSeen1 : bool, rightAux1 : bool, rightRes : bool, rightSeen1 : bool): bool
{
  (((rightAux1 || rightRes) && (rightRes || leftSeen1)) || leftRes)
}

function Aux1Join(leftAux1 : bool, rightAux1 : bool): bool
{
  (rightAux1 || (leftAux1 || rightAux1))
}

function Seen1Join(leftSeen1 : bool, rightSeen1 : bool): bool
{
  (rightSeen1 || (rightSeen1 || (leftSeen1 || leftSeen1)))
}


lemma BaseCaseRes(a : seq<bool>)
  ensures Res(a) == ResJoin(Aux1(a), Res(a), Seen1(a), Aux1([]), Res([]), Seen1([]))
  {}

lemma HomRes(a : seq<bool>, R_a : seq<bool>)
  ensures Res(a + R_a) == ResJoin(Aux1(a), Res(a), Seen1(a), Aux1(R_a), Res(R_a), Seen1(R_a))
  {
    if R_a == [] 
    {
    assert(a + [] == a);
    BaseCaseRes(a);
    
     } else {
    calc{
    Res(a + R_a);
    =={
      HomAux1(a, R_a[..|R_a| - 1]);
      HomSeen1(a, R_a[..|R_a| - 1]);
      assert(a + R_a[..|R_a|-1]) + [R_a[|R_a|-1]] == a + R_a;
      }
    ResJoin(Aux1(a), Res(a), Seen1(a), Aux1(R_a), Res(R_a), Seen1(R_a));
    } // End calc.
  } // End else.
} // End lemma.

lemma BaseCaseAux1(a : seq<bool>)
  ensures Aux1(a) == Aux1Join(Aux1(a), Aux1([]))
  {}

lemma HomAux1(a : seq<bool>, R_a : seq<bool>)
  ensures Aux1(a + R_a) == Aux1Join(Aux1(a), Aux1(R_a))
  {
    if R_a == [] 
    {
    assert(a + [] == a);
    BaseCaseAux1(a);
    
     } else {
    calc{
    Aux1(a + R_a);
    =={ assert(a + R_a[..|R_a|-1]) + [R_a[|R_a|-1]] == a + R_a; }
    Aux1Join(Aux1(a), Aux1(R_a));
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

