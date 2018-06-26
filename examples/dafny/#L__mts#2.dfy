function DfLength(s: seq<int>): int
{if s == [] then 0 else DfLength(s[..|s|-1]) + 1}

function DfMax(x: int, y: int): int { if x > y then x else y}

function Aux_mts1(a : seq<int>): int
{
  if a == [] then 0 else (Aux_mts1(a[..|a|-1]) + a[|a|-1])
}

function Mts(a : seq<int>): int
{
  if a == [] then 0 else DfMax(0, (Mts(a[..|a|-1]) + a[|a|-1]))
}

function Aux_mts1Join(leftAux_mts1 : int, rightAux_mts1 : int): int
{
  (rightAux_mts1 + leftAux_mts1)
}

function MtsJoin(leftAux_mts1 : int, leftMts : int, rightAux_mts1 : int, rightMts : int): int
{
  DfMax(((1 + leftMts) + (1 + rightAux_mts1)), rightMts)
}


lemma BaseCaseAux_mts1(a : seq<int>)
  ensures Aux_mts1(a) == Aux_mts1Join(Aux_mts1(a), Aux_mts1([]))
  {}

lemma HomAux_mts1(a : seq<int>, R_a : seq<int>)
  ensures Aux_mts1(a + R_a) == Aux_mts1Join(Aux_mts1(a), Aux_mts1(R_a))
  {
    if R_a == [] 
    {
    assert(a + [] == a);
    BaseCaseAux_mts1(a);
    
     } else {
    calc{
    Aux_mts1(a + R_a);
    =={ assert(a + R_a[..|R_a|-1]) + [R_a[|R_a|-1]] == a + R_a; }
    Aux_mts1Join(Aux_mts1(a), Aux_mts1(R_a));
    } // End calc.
  } // End else.
} // End lemma.

lemma BaseCaseMts(a : seq<int>)
  ensures Mts(a) == MtsJoin(Aux_mts1(a), Mts(a), Aux_mts1([]), Mts([]))
  {}

lemma HomMts(a : seq<int>, R_a : seq<int>)
  ensures Mts(a + R_a) == MtsJoin(Aux_mts1(a), Mts(a), Aux_mts1(R_a), Mts(R_a))
  {
    if R_a == [] 
    {
    assert(a + [] == a);
    BaseCaseMts(a);
    
     } else {
    calc{
    Mts(a + R_a);
    =={
      HomAux_mts1(a, R_a[..|R_a| - 1]);
      assert(a + R_a[..|R_a|-1]) + [R_a[|R_a|-1]] == a + R_a;
      }
    MtsJoin(Aux_mts1(a), Mts(a), Aux_mts1(R_a), Mts(R_a));
    } // End calc.
  } // End else.
} // End lemma.

