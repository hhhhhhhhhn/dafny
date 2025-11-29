type RR(00) // 00 = nonempty

ghost const Zero: RR
ghost const One: RR

function add(x: RR, y: RR): RR
function mult(x: RR, y: RR): RR

lemma Neutral(x: RR)
	ensures {:axiom} add(x, Zero) == x
	ensures {:axiom} mult(x, One) == x && One != Zero

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

lemma InversesAreUnique()
	ensures forall x: RR, y: RR ::
		((add(x, y) == Zero) ==> (y == neg(x)))
		&& ((x != Zero && mult(x, y) == One) ==> (y == inv(x)))
{
	forall x: RR, y: RR
		ensures ((add(x, y) == Zero) ==> (y == neg(x)))
			&& ((x != Zero && mult(x, y) == One) ==> (y == inv(x)))
	{
		if add(x, y) == Zero {
			assert y == neg(x) by {NegIsUnique(x, y);}
		}
		if x != Zero && mult(x, y) == One {
			assert y == inv(x) by {InvIsUnique(x, y);}
		}
	}
}

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
