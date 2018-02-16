// Helper functions
function fst (a : (int, int)) : int {
	a.0
}

function snd (a : (int, int)) : int {
	a.1
}

function fmax(a : int, b : int) : int {
	if (a > b) then a else b
}

function fmin(a : int, b : int) : int {
	if (a < b) then a else b
}

function abs(a : int) : int {
	if a > 0 then a else -a
}

function fminmax(a : (int, int), b : (int, int)) : (int, int) {
	(fmax(a.0, b.0), fmin(a.1, b.1))
}

function switchprod(a : (int, int), c : (int,int)) : (int, int) {
	if c.0 >= 0 then	(a.0 * c.0, a.1 * c.0) else (a.1 * c.0,  a.0 * c.0)
}


function Prod(s : seq<int>) : int {
	if s == [] then 1 else s[|s| - 1] * Prod(s[..|s|-1])
}



// Repair the product to have a distributivity property
// Computes the pos-neg product of the sequence
function SwitchProd(s : seq<int>) : (int, int)
{
	if s == [] then (1,-1) else switchprod(SwitchProd(s[..|s|-1]), (s[|s|-1],-1))
}

function JoinSwitchProd(spl : (int, int), spr : (int,int)) : (int,int)
{
	(spl.0 * spr.0, spl.0 * spr.1)
}

function isPosNegRepr (a : (int, int)) : bool {
	abs(a.0) == abs(a.1) && a.0 >= 0 && a.1 <= 0
}

// SwitchProd is actually computing the same number, with opposite signs.
lemma SwitchProd_Abs_Identity(s : seq<int>)
	ensures isPosNegRepr(SwitchProd(s))
{}
// And one of these numbers is the product
lemma SwitchProd_Computes_Prod(s : seq<int>)
	ensures fst(SwitchProd(s)) == Prod(s) || snd(SwitchProd(s)) == Prod(s)
{}

lemma SwitchProd_Distributes_Minmax(a : (int,int), b: (int,int), c:(int,int))
	ensures
	switchprod(fminmax(a,b),c) ==
	fminmax(switchprod(a,c), switchprod(b,c))
{}

// SwitchProd is an homormorphism
// lemma HomSwitchProd(s: seq<int>, t: seq<int>)
// 	ensures SwitchProd(s + t) == JoinSwitchProd(SwitchProd(s), SwitchProd(t))
// {
// 	if t == [] {
// 		assert(s + t == s);
// 	} else {
// 		calc {
// 			SwitchProd(s + t);
// 			=={assert(s + t[..|t|-1] + [t[|t| -1]] == s + t);}
// 			JoinSwitchProd(SwitchProd(s), SwitchProd(t));
// 		}
// 	}
// }
// ----------------------------------------------------------------------------



function JoinProd(ps : int, pt : int) : int {
	ps * pt
}

lemma HomProd(s: seq<int>, t: seq<int>)
	ensures Prod(s+t) == JoinProd(Prod(s), Prod(t))
{
	if t == [] {
		assert(s + t == s);
	} else {
		calc{
			Prod(s + t);
			=={assert((s + t[..|t| - 1]) + [t[|t|-1]] == s + t); }
			JoinProd(Prod(s), Prod(t));
		}
	}
}


function Mpp(s : seq<int>) : (int, int)
{
	if s == [] then (1,-1) else fminmax(SwitchProd(s), Mpp(s[..|s|-1]))
}

function MppJoin(mppl : (int,int), pl : int, mppr : (int,int), pr : int) :
	(int,int)
{
	fminmax(mppl, switchprod(mppr, (pl,-1)))
}

// lemma HomMpp(s : seq<int>, t: seq<int>)
// 	ensures Mpp(s + t) == MppJoin(Mpp(s), Prod(s), Mpp(t), Prod(t))
// {
// 	if t == [] {
// 		assert(s + t == s);
// 	} else {
// 		calc{
// 			Mpp(s + t);
// 			=={
// 				assert((s + t[..|t| - 1]) + [t[|t|-1]] == s + t);
// 				HomProd(s, t[..|t|-1]);
// 			}
// 			MppJoin(Mpp(s), Prod(s), Mpp(t), Prod(t));
// 		}
// 	}
// }
