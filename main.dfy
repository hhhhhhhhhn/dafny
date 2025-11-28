type RR(0)

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
	

lemma ZeroIsUnique(x: RR)
	requires H: (forall y: RR :: add(y, x) == Zero)
	ensures x == Zero
{
	assert Zero == add(Zero, x) by {reveal H;}
	assert add(Zero, x) == add(x, Zero) by {Conmutativity(x, Zero);}
	assert add(x, Zero) == x by {Neutral(x);}
}

lemma OneIsUnique(x: RR)
	requires H: (forall y: RR :: mult(y, x) == One)
	ensures x == One
{
	assert One == mult(One, x) by {reveal H;}
	assert mult(One, x) == mult(x, One) by {Conmutativity(x, One);}
	assert mult(x, One) == x by {Neutral(x);}
}
