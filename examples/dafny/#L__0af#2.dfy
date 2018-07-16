function DfLength(s: seq<int>): int
{if s == [] then 0 else DfLength(s[..|s|-1]) + 1}

function Res(a : seq<bool>): bool
{
  if a == [] then
    false
    else
    (((! a[|a|-1]) && Seen1(a[..|a|-1])) || Res(a[..|a|-1]))
}

function Aux_res12(a : seq<bool>): bool
{
  if a == [] then false else ((! a[|a|-1]) || Aux_res12(a[..|a|-1]))
}

function Seen1(a : seq<bool>): bool
{
  if a == [] then false else (Seen1(a[..|a|-1]) || a[|a|-1])
}

function ResJoin(leftAux_res12 : bool, leftRes : bool, leftSeen1 : bool, rightAux_res12 : bool, rightRes : bool, rightSeen1 : bool): bool
{
  ((rightAux_res12 && leftSeen1) || ((rightAux_res12 && leftRes) || (leftRes || rightRes)))
}

function Aux_res12Join(leftAux_res12 : bool, rightAux_res12 : bool): bool
{
  (leftAux_res12 || rightAux_res12)
}

function Seen1Join(leftSeen1 : bool, rightSeen1 : bool): bool
{
  (leftSeen1 || rightSeen1)
}


lemma BaseCaseRes(a : seq<bool>)
  ensures Res(a) == ResJoin(Aux_res12(a), Res(a), Seen1(a), Aux_res12([]), Res([]), Seen1([]))
  {}

lemma HomRes(a : seq<bool>, R_a : seq<bool>)
  ensures Res(a + R_a) == ResJoin(Aux_res12(a), Res(a), Seen1(a), Aux_res12(R_a), Res(R_a), Seen1(R_a))
  {
    if R_a == [] 
    {
    assert(a + [] == a);
    BaseCaseRes(a);
    
     } else {
    calc{
    Res(a + R_a);
    =={
      HomAux_res12(a, R_a[..|R_a| - 1]);
      HomSeen1(a, R_a[..|R_a| - 1]);
      assert(a + R_a[..|R_a|-1]) + [R_a[|R_a|-1]] == a + R_a;
      }
    ResJoin(Aux_res12(a), Res(a), Seen1(a), Aux_res12(R_a), Res(R_a), Seen1(R_a));
    } // End calc.
  } // End else.
} // End lemma.

lemma BaseCaseAux_res12(a : seq<bool>)
  ensures Aux_res12(a) == Aux_res12Join(Aux_res12(a), Aux_res12([]))
  {}

lemma HomAux_res12(a : seq<bool>, R_a : seq<bool>)
  ensures Aux_res12(a + R_a) == Aux_res12Join(Aux_res12(a), Aux_res12(R_a))
  {
    if R_a == [] 
    {
    assert(a + [] == a);
    BaseCaseAux_res12(a);
    
     } else {
    calc{
    Aux_res12(a + R_a);
    =={ assert(a + R_a[..|R_a|-1]) + [R_a[|R_a|-1]] == a + R_a; }
    Aux_res12Join(Aux_res12(a), Aux_res12(R_a));
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

