function DfLength(s: seq<int>): int
{if s == [] then 0 else DfLength(s[..|s|-1]) + 1}

function DfMax(x: int, y: int): int { if x > y then x else y}

function Mps(a : seq<int>): int
{
  if a == [] then 0 else DfMax((Sum(a[..|a|-1]) + a[|a|-1]), Mps(a[..|a|-1]))
}

function Aux_mps5(a : seq<int>): int
{
  if a == [] then
    0
    else
    DfMax((Sum(a[..|a|-1]) + a[|a|-1]), Aux_mps5(a[..|a|-1]))
}

function Sum(a : seq<int>): int
{
  if a == [] then 0 else (Sum(a[..|a|-1]) + a[|a|-1])
}

function MpsJoin(leftAux_mps5 : int, leftSum : int, rightAux_mps5 : int, rightSum : int): int
{
  DfMax((leftSum + rightAux_mps5), leftAux_mps5)
}

function Aux_mps5Join(leftAux_mps5 : int, leftSum : int, rightAux_mps5 : int, rightSum : int): int
{
  DfMax((leftSum + rightAux_mps5), leftAux_mps5)
}

function SumJoin(leftSum : int, rightSum : int): int
{
  (rightSum + leftSum)
}


lemma BaseCaseMps(a : seq<int>)
  ensures Mps(a) == MpsJoin(Aux_mps5(a), Sum(a), Aux_mps5([]), Sum([]))
  {}

lemma HomMps(a : seq<int>, R_a : seq<int>)
  ensures Mps(a + R_a) == MpsJoin(Aux_mps5(a), Sum(a), Aux_mps5(R_a), Sum(R_a))
  {
    if R_a == [] 
    {
    assert(a + [] == a);
    BaseCaseMps(a);
    
     } else {
    calc{
    Mps(a + R_a);
    =={
      HomAux_mps5(a, R_a[..|R_a| - 1]);
      HomSum(a, R_a[..|R_a| - 1]);
      assert(a + R_a[..|R_a|-1]) + [R_a[|R_a|-1]] == a + R_a;
      }
    MpsJoin(Aux_mps5(a), Sum(a), Aux_mps5(R_a), Sum(R_a));
    } // End calc.
  } // End else.
} // End lemma.

lemma BaseCaseAux_mps5(a : seq<int>)
  ensures Aux_mps5(a) == Aux_mps5Join(Aux_mps5(a), Sum(a), Aux_mps5([]), Sum([]))
  {}

lemma HomAux_mps5(a : seq<int>, R_a : seq<int>)
  ensures Aux_mps5(a + R_a) == Aux_mps5Join(Aux_mps5(a), Sum(a), Aux_mps5(R_a), Sum(R_a))
  {
    if R_a == [] 
    {
    assert(a + [] == a);
    BaseCaseAux_mps5(a);
    
     } else {
    calc{
    Aux_mps5(a + R_a);
    =={
      HomSum(a, R_a[..|R_a| - 1]);
      assert(a + R_a[..|R_a|-1]) + [R_a[|R_a|-1]] == a + R_a;
      }
    Aux_mps5Join(Aux_mps5(a), Sum(a), Aux_mps5(R_a), Sum(R_a));
    } // End calc.
  } // End else.
} // End lemma.

lemma BaseCaseSum(a : seq<int>)
  ensures Sum(a) == SumJoin(Sum(a), Sum([]))
  {}

lemma HomSum(a : seq<int>, R_a : seq<int>)
  ensures Sum(a + R_a) == SumJoin(Sum(a), Sum(R_a))
  {
    if R_a == [] 
    {
    assert(a + [] == a);
    BaseCaseSum(a);
    
     } else {
    calc{
    Sum(a + R_a);
    =={ assert(a + R_a[..|R_a|-1]) + [R_a[|R_a|-1]] == a + R_a; }
    SumJoin(Sum(a), Sum(R_a));
    } // End calc.
  } // End else.
} // End lemma.

