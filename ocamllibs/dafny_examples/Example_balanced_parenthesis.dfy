function DfLength(s: seq<int>): int
{if s == [] then 0 else DfLength(s[..|s|-1]) + 1}

function DfMax(x: int, y: int): int { if x > y then x else y}

function DfMin(x: int, y: int): int { if x > y then y else x}

function DfLengthJoin(a: int, b: int): int
{ a + b }
lemma HomDfLength(s: seq<int>, t: seq<int>)
ensures DfLength(s + t) == DfLengthJoin(DfLength(s), DfLength(t))
{
  if t == [] {
  assert(s + t == s);
} else {
        calc {
        DfLength(s + t);
        == {assert (s + t[..|t|-1]) + [t[|t|-1]] == s + t;}
        DfLengthJoin(DfLength(s), DfLength(t));
        }
        }
}

function Aux_3(a : seq<bool>): int
{ if a == [] then
    0
   else
   DfMin((Cnt(a[..|a|-1]) + if a[|a|-1] then 1 else -1), Aux_3(a[..|a|-1]))

}

function Bal(a : seq<bool>): bool
{ if a == [] then
    true
   else
   (Bal(a[..|a|-1]) && ((Cnt(a[..|a|-1]) + if a[|a|-1] then 1 else -1) >= 0))

}

function Cnt(a : seq<bool>): int
{ if a == [] then  0 else  (Cnt(a[..|a|-1]) + if a[|a|-1] then 1 else -1)
}

function Aux_3Join(leftAux_3 : int, leftCnt : int, rightAux_3 : int, rightCnt : int): int
{
  DfMin((rightAux_3 + leftCnt), DfMax(leftAux_3, -6))
}

function BalJoin(leftAux_3 : int, leftCnt : int, leftBal : bool, rightAux_3 : int, rightCnt : int, rightBal : bool): bool
{
  ((if rightBal then ((leftCnt + 1) + 3276) else
      ((leftCnt + 1) + (rightCnt + rightAux_3))) >= (rightCnt + 1)) &&
    (leftBal || leftBal)
}

function CntJoin(leftCnt : int, leftBal : bool, rightCnt : int, rightBal : bool): int
{
  if rightBal then (rightCnt + leftCnt) else (rightCnt + (leftCnt + 0))
}


// lemma BaseCaseAux_3(a : seq<bool>)
//   ensures Aux_3(a) == Aux_3Join(Aux_3(a), Cnt(a), Aux_3([]), Cnt([]))
//   {}

// lemma HomAux_3(a : seq<bool>, R_a : seq<bool>)
//   ensures Aux_3(a + R_a) == Aux_3Join(Aux_3(a), Cnt(a), Aux_3(R_a), Cnt(R_a))
//   {
//     if R_a == []
//     {
//     assert(a + [] == a);
//     BaseCaseAux_3(a);

//      } else {
//     calc{
//     Aux_3(a + R_a);
//     =={
//       HomCnt(a, R_a[..|R_a| - 1]);
//       assert(a + R_a[..|R_a|-1]) + [R_a[|R_a|-1]] == a + R_a;
//       }
//     Aux_3Join(Aux_3(a), Cnt(a), Aux_3(R_a), Cnt(R_a));
//     } // End calc.
//   } // End else.
// } // End lemma.

lemma BaseCaseBal(a : seq<bool>)
  ensures Bal(a) == BalJoin(Aux_3(a), Cnt(a), Bal(a), Aux_3([]), Cnt([]), Bal([]))
  {}

// lemma HomBal(a : seq<bool>, R_a : seq<bool>)
//   ensures Bal(a + R_a) == BalJoin(Aux_3(a), Cnt(a), Bal(a), Aux_3(R_a), Cnt(R_a), Bal(R_a))
//   {
//     if R_a == []
//     {
//     assert(a + [] == a);
//     BaseCaseBal(a);

//      } else {
//     calc{
//     Bal(a + R_a);
//     =={
//       HomCnt(a, R_a[..|R_a| - 1]);
//       assert(a + R_a[..|R_a|-1]) + [R_a[|R_a|-1]] == a + R_a;
//       }
//     BalJoin(Aux_3(a), Cnt(a), Bal(a), Aux_3(R_a), Cnt(R_a), Bal(R_a));
//     } // End calc.
//   } // End else.
// } // End lemma.

lemma BaseCaseCnt(a : seq<bool>)
  ensures Cnt(a) == CntJoin(Cnt(a), Bal(a), Cnt([]), Bal([]))
  {}

lemma HomCnt(a : seq<bool>, R_a : seq<bool>)
  ensures Cnt(a + R_a) == CntJoin(Cnt(a), Bal(a), Cnt(R_a), Bal(R_a))
  {
    if R_a == []
    {
    assert(a + [] == a);
    BaseCaseCnt(a);

     } else {
    calc{
    Cnt(a + R_a);
    =={ assert(a + R_a[..|R_a|-1]) + [R_a[|R_a|-1]] == a + R_a; }
    CntJoin(Cnt(a), Bal(a), Cnt(R_a), Bal(R_a));
    } // End calc.
  } // End else.
} // End lemma.
