function DfLength(s: seq<int>): int
{if s == [] then 0 else DfLength(s[..|s|-1]) + 1}

function Aux_1(ar : seq<bool>): bool
requires |ar| >= 1
{
  if |ar| == 1 then ar[0] else ar[0]
}

function An(ar : seq<bool>): bool
{
  if ar == [] then true else (ar[|ar|-1] && An(ar[..|ar|-1]))
}

function Bn(ar : seq<bool>): bool
{
  if ar == [] then
    true
    else
    (if (! ar[|ar|-1]) then Bn(ar[..|ar|-1]) else
      (An(ar[..|ar|-1]) && Bn(ar[..|ar|-1])))
}

function Aux_1Join(leftAux_1 : bool, rightAux_1 : bool): bool
{
  leftAux_1
}

function AnJoin(leftBn : bool, leftAn : bool, rightBn : bool, rightAn : bool): bool
{
  (leftAn && (rightAn && rightBn))
}

function BnJoin(leftAux_1 : bool, leftBn : bool, leftAn : bool, rightAux_1 : bool, rightBn : bool, rightAn : bool): bool
{
  (leftAn && rightBn) || ((rightBn && (! rightAux_1) && ((! rightAn) && leftBn)))
}


lemma BaseCaseAux_1(ar : seq<bool>, R_ar : seq<bool>)
  requires |ar| >= 1 && |R_ar| >= 1
  ensures Aux_1(ar + [R_ar[0]]) == Aux_1Join(Aux_1(ar), Aux_1([R_ar[0]]))
  {}

lemma HomAux_1(ar : seq<bool>, R_ar : seq<bool>)
  requires |ar| >= 1 && |R_ar| >= 1
  ensures Aux_1(ar + R_ar) == Aux_1Join(Aux_1(ar), Aux_1(R_ar))
  {
    if |R_ar| == 1
    {
    assert(ar + R_ar == ar + [R_ar[0]]);
    BaseCaseAux_1(ar, R_ar);

     } else {
    calc{
    Aux_1(ar + R_ar);
    =={ assert(ar + R_ar[..|R_ar|-1]) + [R_ar[|R_ar|-1]] == ar + R_ar; }
    Aux_1Join(Aux_1(ar), Aux_1(R_ar));
    } // End calc.
  } // End else.
} // End lemma.

lemma HomAn(ar : seq<bool>, R_ar : seq<bool>)
	requires |ar| >= 1 && |R_ar| >= 1
  ensures An(ar + R_ar) == AnJoin(Bn(ar), An(ar), Bn(R_ar), An(R_ar))
  {
    if |R_ar| == 1
    {
			assert(ar + R_ar == ar + [R_ar[0]]);
     } else {
    calc{
    An(ar + R_ar);
    =={
      HomBn(ar, R_ar[..|R_ar| - 1]);
      assert(ar + R_ar[..|R_ar|-1]) + [R_ar[|R_ar|-1]] == ar + R_ar;
      }
    AnJoin(Bn(ar), An(ar), Bn(R_ar), An(R_ar));
    } // End calc.
  } // End else.
} // End lemma.

lemma BaseCaseBn(ar : seq<bool>, R_ar : seq<bool>)
  requires |ar| >= 1 && |R_ar| >= 1
  ensures Bn(ar + [R_ar[0]]) == BnJoin(Aux_1(ar), Bn(ar), An(ar), Aux_1([R_ar[0]]), Bn([R_ar[0]]), An([R_ar[0]]))
  {}

lemma HomBn(ar : seq<bool>, R_ar : seq<bool>)
  requires |ar| >= 1 && |R_ar| >= 1
  ensures Bn(ar + R_ar) == BnJoin(Aux_1(ar), Bn(ar), An(ar), Aux_1(R_ar), Bn(R_ar), An(R_ar))
  {
    if |R_ar| == 1
    {
    assert(ar + R_ar == ar + [R_ar[0]]);
    BaseCaseBn(ar, R_ar);

     } else {
    calc{
    Bn(ar + R_ar);
    =={
      HomAux_1(ar, R_ar[..|R_ar| - 1]);
      HomAn(ar, R_ar[..|R_ar| - 1]);
      assert(ar + R_ar[..|R_ar|-1]) + [R_ar[|R_ar|-1]] == ar + R_ar;
      }
    BnJoin(Aux_1(ar), Bn(ar), An(ar), Aux_1(R_ar), Bn(R_ar), An(R_ar));
    } // End calc.
  } // End else.
} // End lemma.
