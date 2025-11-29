type RR(00) // 00 = nonempty

ghost const Zero: RR
ghost const One: RR

function add(x: RR, y: RR): RR
function mult(x: RR, y: RR): RR

lemma Neutral(x: RR)
	ensures {:axiom} add(x, Zero) == x
	ensures {:axiom} mult(x, One) == x
	ensures {:axiom} One != Zero

lemma Conmutativity(x: RR, y: RR)
	ensures {:axiom} add(x, y) == add(y, x)
	ensures {:axiom} mult(x, y) == mult(y, x)

lemma Associativity(x: RR, y: RR, z: RR)
	ensures {:axiom} add(x, add(y, z)) == add(add(x, y), z)
	ensures {:axiom} mult(x, mult(y, z)) == mult(mult(x, y), z)

lemma Inverse(x: RR)
	ensures {:axiom} exists y: RR :: add(x, y) == Zero
	ensures {:axiom} (x != Zero) ==> exists y: RR :: mult(x, y) == One

lemma Distribuitivity(x: RR, y: RR, z: RR)
	ensures {:axiom} mult(x, add(y, z)) == add(mult(x, y), mult(x, z))


ghost function neg(x: RR): RR
	ensures add(x, neg(x)) == Zero
{
	assert (exists y: RR :: add(x, y) == Zero) by {Inverse(x);}
	var y :| add(x, y) == Zero;
	y
}

ghost function inv(x: RR): RR
	requires x != Zero
	ensures mult(x, inv(x)) == One
{
	assert (exists y: RR :: mult(x, y) == One) by {Inverse(x);}
	var y :| mult(x, y) == One;
	y
}

ghost function sub(x: RR, y: RR): RR {
	add(x, neg(y))
}

ghost function div(x: RR, y: RR): RR
	requires y != Zero
{
	mult(x, inv(y))
}

//// Sample helper, finds the variable automatically. Slow...
//lemma HelperField()
//	ensures One != Zero
//	ensures forall x: RR ::
//		(add(x, Zero) == x)
//		&& mult(x, One) == x
//	ensures forall x: RR, y: RR ::
//		add(x, y) == add(y, x)
//		&& mult(x, y) == mult(y, x)
//	ensures forall x: RR, y: RR, z: RR ::
//		add(x, add(y, z)) == add(add(x, y), z)
//		&& mult(x, mult(y, z)) == mult(mult(x, y), z)
//		&& mult(x, add(y, z)) == add(mult(x, y), mult(x, z))
//{
//	assert One != Zero by {Neutral(Zero);}
//
//	forall x: RR
//		ensures (add(x, Zero) == x)
//	     && (mult(x, One) == x)
//	{
//		assert add(x, Zero) == x && mult(x, One) == x by {Neutral(x);}
//	}
//
//	forall x: RR, y: RR
//		ensures add(x, y) == add(y, x)
//			&& mult(x, y) == mult(y, x)
//	{
//		assert add(x, y) == add(y, x) && mult(x, y) == mult(y, x) by {Conmutativity(x, y);}
//	}
//
//	forall x: RR, y: RR, z: RR
//		ensures add(x, add(y, z)) == add(add(x, y), z)
//			&& mult(x, mult(y, z)) == mult(mult(x, y), z)
//			&& mult(x, add(y, z)) == add(mult(x, y), mult(x, z))
//	{
//		assert add(x, add(y, z)) == add(add(x, y), z)            by {Associativity(x, y, z);}
//		assert mult(x, mult(y, z)) == mult(mult(x, y), z)        by {Associativity(x, y, z);}
//		assert mult(x, add(y, z)) == add(mult(x, y), mult(x, z)) by {Distribuitivity(x, y, z);}
//	}
//}

lemma NegationOfNegation(x: RR)
	ensures neg(neg(x)) == x
{
	assert add(neg(x), neg(neg(x))) == Zero; // (1)
	assert add(x, neg(x)) == Zero;           // (2)

	// (2)
	assert add(Zero, x) == add(x, add(neg(x), x)) by {Associativity(x, neg(x), x);}
	assert add(Zero, x) == add(x, add(x, neg(x))) by {Conmutativity(neg(x), x);}
	assert add(Zero, x) == add(x, Zero);
	assert add(Zero, x) == x                      by {Neutral(x);}

	// (1)
	assert add(Zero, x) == add(add(neg(neg(x)), neg(x)), x) by {Conmutativity(neg(neg(x)), neg(x));}
	assert add(Zero, x) == add(neg(neg(x)), add(neg(x), x)) by {Associativity(neg(neg(x)), neg(x), x);}
	assert add(Zero, x) == add(neg(neg(x)), add(x, neg(x))) by {Conmutativity(neg(x), x);}
	assert add(Zero, x) == add(neg(neg(x)), Zero);
	assert add(Zero, x) == neg(neg(x))                      by {Neutral(neg(neg(x)));}

	assert neg(neg(x)) == x; // (1) + x == (2) + x
}

lemma NegIsUnique(x: RR, y: RR)
	requires add(x, y) == Zero
	ensures y == neg(x)
{
	assert y == add(y, add(x, neg(x))) by {Neutral(y);}
	assert add(y, add(x, neg(x))) == add(add(y, x), neg(x)) by {Associativity(y, x, neg(x));}
	assert add(add(y, x), neg(x)) == add(add(x, y), neg(x)) by {Conmutativity(x, y);}
	assert add(add(x, y), neg(x)) == add(Zero, neg(x));
	assert add(Zero, neg(x)) == add(neg(x), Zero)           by {Conmutativity(Zero, neg(x));}
	assert add(neg(x), Zero) == neg(x)                      by {Neutral(neg(x));}
}

lemma InvIsUnique(x: RR, y: RR)
	requires mult(x, y) == One
	requires x != Zero
	ensures y == inv(x)
{
	assert y == mult(y, mult(x, inv(x))) by {Neutral(y);}
	assert mult(y, mult(x, inv(x))) == mult(mult(y, x), inv(x)) by {Associativity(y, x, inv(x));}
	assert mult(mult(y, x), inv(x)) == mult(mult(x, y), inv(x)) by {Conmutativity(x, y);}
	assert mult(mult(x, y), inv(x)) == mult(One, inv(x));
	assert mult(One, inv(x)) == mult(inv(x), One)               by {Conmutativity(One, inv(x));}
	assert mult(inv(x), One) == inv(x)                          by {Neutral(inv(x));}
}

lemma NegZeroIsZero()
	ensures neg(Zero) == Zero
{
	assert Zero == neg(Zero) by {Neutral(Zero); NegIsUnique(Zero, Zero);}
}


lemma InvOneIsOne()
	ensures One != Zero
	ensures inv(One) == One
{
	assert One != Zero     by {Neutral(One);}
	assert One == inv(One) by {Neutral(One); InvIsUnique(One, One);}
}

//lemma HelperInversesAreUnique()
//	ensures forall x: RR, y: RR ::
//		((add(x, y) == Zero) ==> (y == neg(x)))
//		&& ((x != Zero && mult(x, y) == One) ==> (y == inv(x)))
//{
//	forall x: RR, y: RR
//		ensures ((add(x, y) == Zero) ==> (y == neg(x)))
//			&& ((x != Zero && mult(x, y) == One) ==> (y == inv(x)))
//	{
//		if add(x, y) == Zero {
//			assert y == neg(x) by {NegIsUnique(x, y);}
//		}
//		if x != Zero && mult(x, y) == One {
//			assert y == inv(x) by {InvIsUnique(x, y);}
//		}
//	}
//}

lemma AnythingTimesZeroIsZero(x: RR)
	ensures mult(x, Zero) == Zero
{
	assert mult(x, Zero) == add(mult(x, Zero), Zero)                                     by {Neutral(mult(x, Zero));}
	assert mult(x, Zero) == add(mult(x, Zero), add(mult(x, Zero), neg(mult(x, Zero))));
	assert mult(x, Zero) == add(add(mult(x, Zero), mult(x, Zero)), neg(mult(x, Zero)))   by {Associativity(mult(x, Zero), mult(x, Zero), neg(mult(x, Zero)));}
	assert mult(x, Zero) == add(mult(x, add(Zero, Zero)), neg(mult(x, Zero)))            by {Distribuitivity(x, Zero, Zero);}
	assert mult(x, Zero) == add(mult(x, Zero), neg(mult(x, Zero)))                       by {Neutral(Zero);}
	assert mult(x, Zero) == Zero;
}

lemma InverseIsNeverZero(x: RR)
	requires x != Zero
	ensures inv(x) != Zero
{
	if inv(x) == Zero {
		assert mult(x, inv(x)) == Zero by {AnythingTimesZeroIsZero(x);}
		assert Zero != One             by {Neutral(Zero);}
	}
}

lemma InverseOfInverse(x: RR)
	requires x != Zero
	ensures inv(x) != Zero
	ensures inv(inv(x)) == x
{
	assert inv(x) != Zero by {InverseIsNeverZero(x);}

	assert mult(inv(x), inv(inv(x))) == One; // (1)
	assert mult(x, inv(x)) == One;           // (2)

	// (2)
	assert mult(One, x) == mult(x, mult(inv(x), x)) by {Associativity(x, inv(x), x);}
	assert mult(One, x) == mult(x, mult(x, inv(x))) by {Conmutativity(inv(x), x);}
	assert mult(One, x) == mult(x, One);
	assert mult(One, x) == x                      by {Neutral(x);}

	// (1)
	assert mult(One, x) == mult(mult(inv(inv(x)), inv(x)), x) by {Conmutativity(inv(inv(x)), inv(x));}
	assert mult(One, x) == mult(inv(inv(x)), mult(inv(x), x)) by {Associativity(inv(inv(x)), inv(x), x);}
	assert mult(One, x) == mult(inv(inv(x)), mult(x, inv(x))) by {Conmutativity(inv(x), x);}
	assert mult(One, x) == mult(inv(inv(x)), One);
	assert mult(One, x) == inv(inv(x))                      by {Neutral(inv(inv(x)));}

	assert inv(inv(x)) == x; // (1) * x == (2) * x
}

lemma ZeroIsUnique(x: RR, y: RR)
	requires add(x, y) == x
	ensures y == Zero
{
	assert add(add(x, y), neg(x)) == add(y, add(x, neg(x))) by {Conmutativity(x, y); Associativity(y, x, neg(x));}
	assert add(add(x, y), neg(x)) == y                      by {Neutral(y);}
}

lemma OneIsUnique(x: RR, y: RR)
	requires mult(x, y) == x
	requires x != Zero
	ensures y == One
{
	assert mult(mult(x, y), inv(x)) == mult(y, mult(x, inv(x))) by {Conmutativity(x, y); Associativity(y, x, inv(x));}
	assert mult(mult(x, y), inv(x)) == y                        by {Neutral(y);}
}

lemma AddOnBothSides(x: RR, a: RR, b: RR)
	requires sub(x, a) == b
	ensures x == add(b, a)
{
	assert add(sub(x, a), a) == add(b, a);
	assert add(add(x, neg(a)), a) == add(b, a);
	assert add(x, add(a, neg(a))) == add(b, a) by {Associativity(x, neg(a), a); Conmutativity(a, neg(a));}
	assert x == add(b, a)                        by {Neutral(x);}
}

lemma SubstractOnBothSides(x: RR, a: RR, b: RR)
	requires add(x, a) == b
	ensures x == sub(b, a)
{
	assert sub(add(x, a), a)      == sub(b, a);
	assert add(add(x, a), neg(a)) == sub(b, a);
	assert add(x, add(a, neg(a))) == sub(b, a) by {Associativity(x, a, neg(a));}
	assert x == sub(b, a)                      by {Neutral(x);}
}

lemma MultiplyOnBothSides(x: RR, a: RR, b: RR)
	requires a != Zero
	requires div(x, a) == b
	ensures x == mult(b, a)
{
	assert mult(div(x, a), a) == mult(b, a);
	assert mult(mult(x, inv(a)), a) == mult(b, a);
	assert mult(x, mult(a, inv(a))) == mult(b, a) by {Associativity(x, inv(a), a); Conmutativity(a, inv(a));}
	assert x == mult(b, a)                        by {Neutral(x);}
}

lemma DivideOnBothSides(x: RR, a: RR, b: RR)
	requires mult(x, a) == b
	requires a != Zero
	ensures x == div(b, a)
{
	assert div(mult(x, a), a)       == div(b, a);
	assert mult(mult(x, a), inv(a)) == div(b, a);
	assert mult(x, mult(a, inv(a))) == div(b, a) by {Associativity(x, a, inv(a));}
	assert x == div(b, a)                        by {Neutral(x);}
}

lemma LinearEquationSolution(x: RR, a: RR, b: RR, c: RR)
	requires add(mult(a, x), b) == c
	requires a != Zero
	ensures x == div(sub(c, b), a)
{
	assert mult(a, x) == sub(c, b) by {SubstractOnBothSides(mult(a, x), b, c);}
	assert mult(x, a) == sub(c, b) by {Conmutativity(a, x);}
	assert x == div(sub(c, b), a)  by {DivideOnBothSides(x, a, sub(c, b));}
}
