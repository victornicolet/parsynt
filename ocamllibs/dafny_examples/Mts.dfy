function DfMax(x: int, y: int): int { if x > y then x else y}

function Mts___0(a : seq<int>): int
{ if a == [] then  0 else  DfMax(0, (Mts___0(a[..|a|-1]) + a[|a|-1])) 
}

function Aux_1(a : seq<int>): int
{ if a == [] then  1 else  (a[|a|-1] + Aux_1(a[..|a|-1])) 
}

function Mts___0Join(leftAux_1 : int, leftMts___0 : int, rightAux_1 : int, rightMts___0 : int): int
{
  DfMax(((leftMts___0 - 1) + rightAux_1), rightMts___0)
}

function Aux_1Join(leftAux_1 : int, rightAux_1 : int): int
{
  ((rightAux_1 - 1) + leftAux_1)
}


lemma BaseCaseMts___0(a : seq<int>)
  ensures Mts___0(a) == Mts___0Join(Aux_1(a), Mts___0(a), Aux_1([]), Mts___0([]))
  {}

lemma HomMts___0(a : seq<int>, R_a : seq<int>)
  ensures Mts___0(a + R_a) == Mts___0Join(Aux_1(a), Mts___0(a), Aux_1(R_a), Mts___0(R_a))
  {
    if R_a == [] 
    {
    assert(a + [] == a);
    BaseCaseMts___0(a);
    } else {
    calc{
    Mts___0(a + R_a);
    =={
      HomAux_1(a, R_a[..|R_a| - 1]);
      assert(a + R_a[..|R_a|-1]) + [R_a[|R_a|-1]] == a + R_a;
      }
    Mts___0Join(Aux_1(a), Mts___0(a), Aux_1(R_a), Mts___0(R_a));
    } // End calc.
  } // End else.
} // End lemma.

lemma BaseCaseAux_1(a : seq<int>)
  ensures Aux_1(a) == Aux_1Join(Aux_1(a), Aux_1([]))
  {}

lemma HomAux_1(a : seq<int>, R_a : seq<int>)
  ensures Aux_1(a + R_a) == Aux_1Join(Aux_1(a), Aux_1(R_a))
  {
    if R_a == [] 
    {
    assert(a + [] == a);
    BaseCaseAux_1(a);
    } else {
    calc{
    Aux_1(a + R_a);
    =={ assert(a + R_a[..|R_a|-1]) + [R_a[|R_a|-1]] == a + R_a; }
    Aux_1Join(Aux_1(a), Aux_1(R_a));
    } // End calc.
  } // End else.
} // End lemma.

