function DfLength(s: seq<int>): int
{if s == [] then 0 else DfLength(s[..|s|-1]) + 1}

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

function Aux_1(a : seq<int>): bool
requires |a| >= 1
{
  if |a| == 1 then a[0] else (! (a[0] == 0))
}

function Aux_2(a : seq<int>): bool
requires |a| >= 1
