//////////////////////////// Field axioms  //////////////////////////////////
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


predicate ExactlyOneOf(a: bool, b: bool, c: bool) {
	(a && !b && !c) || (!a && b && !c) || (!a && !b && c)
}

//////////////////////////////// Field Theorems //////////////////////////////////

// Observation: This declaration means that there exists one such function,
// not that it is unique. This is becuase the :| operation
// could in theory pick any real for which the condition holds.
// We then prove that the function is unique (NegIsUnique)
ghost function neg(x: RR): RR
	ensures add(x, neg(x)) == Zero
	ensures add(neg(x), x) == Zero
{
	assert (exists y: RR :: add(x, y) == Zero) by {Inverse(x);}
	var y :| add(x, y) == Zero;
	assert add(y, x) == add(x, y) by {Conmutativity(x, y);}
	y
}

ghost function inv(x: RR): RR
	requires x != Zero
	ensures mult(x, inv(x)) == One
	ensures mult(inv(x), x) == One
{
	assert (exists y: RR :: mult(x, y) == One) by {Inverse(x);}
	var y :| mult(x, y) == One;
	assert mult(x, y) == mult(y, x) by {Conmutativity(x, y);}
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

lemma NegOfNeg(x: RR)
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

lemma NegOfSum(x: RR, y: RR)
	ensures neg(add(x, y)) == add(neg(x), neg(y))
{
	assert add(add(x, y), add(neg(x), neg(y))) == add(add(y, x), add(neg(x), neg(y))) by {Conmutativity(x, y);}
	assert add(add(x, y), add(neg(x), neg(y))) == add(y, add(x, add(neg(x), neg(y)))) by {Associativity(y, x, add(neg(x), neg(y)));}
	assert add(add(x, y), add(neg(x), neg(y))) == add(y, add(add(x, neg(x)), neg(y))) by {Associativity(x, neg(x), neg(y));}
	assert add(add(x, y), add(neg(x), neg(y))) == add(y, add(Zero, neg(y)))           by {Conmutativity(x, neg(x));}
	assert add(add(x, y), add(neg(x), neg(y))) == add(y, neg(y))                      by {Conmutativity(Zero, neg(y)); Neutral(neg(y));}
	assert add(add(x, y), add(neg(x), neg(y))) == Zero;

	assert neg(add(x, y)) == add(neg(x), neg(y)) by {NegIsUnique(add(x, y), add(neg(x), neg(y)));}
}

lemma NegOfSub(x: RR, y: RR)
	ensures neg(sub(x, y)) == sub(y, x)
{
	assert neg(sub(x, y)) == neg(add(x, neg(y)));
	assert neg(sub(x, y)) == add(neg(x), neg(neg(y))) by {NegOfSum(x, neg(y));}
	assert neg(sub(x, y)) == add(neg(x), y)           by {NegOfNeg(y);}
	assert neg(sub(x, y)) == add(y, neg(x))           by {Conmutativity(neg(x), y);}
	assert neg(sub(x, y)) == sub(y, x);
}

lemma NonzeroProductIsNonzero(x: RR, y: RR)
	requires x != Zero
	requires y != Zero
	ensures mult(x, y) != Zero
{
	assert mult(inv(y), mult(x, y)) == mult(mult(x, y), inv(y)) by {Conmutativity(inv(y), mult(x, y));}
	assert mult(inv(y), mult(x, y)) == mult(x, mult(y, inv(y))) by {Associativity(x, y, inv(y));}
	assert mult(inv(y), mult(x, y)) == x                        by {Neutral(x);}

	if mult(x, y) == Zero {
		assert mult(inv(y), mult(x, y)) == Zero by {AnythingTimesZeroIsZero(inv(y));}
		assert false                            by {InverseIsNeverZero(y);}
	}
}

lemma Neutrals(x: RR)
	ensures add(x, Zero) == x
	ensures add(Zero, x) == x
	ensures sub(x, Zero) == x
	ensures sub(Zero, x) == neg(x)
	ensures mult(x, One) == x
	ensures mult(One, x) == x
	ensures One != Zero
	ensures div(x, One) == x
	ensures x != Zero ==> div(One, x) == inv(x)
{
	assert One != Zero                  by {Neutral(Zero);}
	assert add(x, Zero) == x            by {Neutral(x);}
	assert add(Zero, x) == add(x, Zero) by {Conmutativity(x, Zero);}
	assert mult(x, One) == x            by {Neutral(x);}
	assert mult(One, x) == mult(x, One) by {Conmutativity(x, One);}

	assert sub(x, Zero) == add(x, neg(Zero)) == add(x, Zero)                by {NegZeroIsZero();}
	assert sub(Zero, x) == add(Zero, neg(x)) == add(neg(x), Zero) == neg(x) by {Conmutativity(neg(x), Zero); Neutral(neg(x));}

	assert div(x, One) == mult(x, inv(One)) == mult(x, One) by {InvOneIsOne();}

	if x != Zero {
		assert div(One, x) == mult(One, inv(x)) == mult(inv(x), One) == inv(x) by {Conmutativity(inv(x), One); Neutral(inv(x));}
	}
}


lemma InvOfProd(x: RR, y: RR)
	requires x != Zero
	requires y != Zero
	ensures mult(x, y) != Zero
	ensures inv(mult(x, y)) == mult(inv(x), inv(y))
{
	assert mult(x, y) != Zero by {NonzeroProductIsNonzero(x, y);}

	assert mult(mult(x, y), mult(inv(x), inv(y))) == mult(mult(y, x), mult(inv(x), inv(y))) by {Conmutativity(x, y);}
	assert mult(mult(x, y), mult(inv(x), inv(y))) == mult(y, mult(x, mult(inv(x), inv(y)))) by {Associativity(y, x, mult(inv(x), inv(y)));}
	assert mult(mult(x, y), mult(inv(x), inv(y))) == mult(y, mult(mult(x, inv(x)), inv(y))) by {Associativity(x, inv(x), inv(y));}
	assert mult(mult(x, y), mult(inv(x), inv(y))) == mult(y, mult(One, inv(y)))             by {Conmutativity(x, inv(x));}
	assert mult(mult(x, y), mult(inv(x), inv(y))) == mult(y, inv(y))                        by {Conmutativity(One, inv(y)); Neutral(inv(y));}
	assert mult(mult(x, y), mult(inv(x), inv(y))) == One;

	assert inv(mult(x, y)) == mult(inv(x), inv(y)) by {InvIsUnique(mult(x, y), mult(inv(x), inv(y)));}
}

lemma NegOfProdLeft(x: RR, y: RR)
	ensures neg(mult(x, y)) == mult(neg(x), y)
{
	assert add(mult(x, y), mult(neg(x), y)) == add(mult(y, x), mult(y, neg(x))) by {Conmutativity(x, y); Conmutativity(neg(x), y);}
	assert add(mult(x, y), mult(neg(x), y)) == mult(y, add(x, neg(x)))          by {Distribuitivity(y, x, neg(x));}
	assert add(mult(x, y), mult(neg(x), y)) == mult(y, Zero);
	assert add(mult(x, y), mult(neg(x), y)) == Zero                             by {AnythingTimesZeroIsZero(y);}

	assert mult(neg(x), y) == neg(mult(x, y))                                   by {NegIsUnique(mult(x, y), mult(neg(x), y));}
}

lemma NegOfProd(x: RR, y: RR)
	ensures neg(mult(x, y)) == mult(neg(x), y) == mult(x, neg(y))
{
	assert neg(mult(x, y)) == mult(neg(x), y)  by {NegOfProdLeft(x, y);}

	assert neg(mult(x, y)) == neg(mult(y, x))  by {Conmutativity(x, y);}
	assert neg(mult(y, x)) == mult(neg(y), x)  by {NegOfProdLeft(y, x);}
	assert mult(neg(y), x) == mult(x, neg(y))  by {Conmutativity(x, neg(y));}
}

lemma ProdOfNeg(x: RR, y: RR)
	ensures mult(neg(x), neg(y)) == mult(x, y)
{
	assert mult(neg(x), neg(y)) == neg(mult(x, neg(y))) by {NegOfProd(x, neg(y));}
	assert mult(neg(x), neg(y)) == neg(neg(mult(x, y))) by {NegOfProd(x, y);}
	assert mult(neg(x), neg(y)) == mult(x, y)           by {NegOfNeg(mult(x, y));}
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


////////////////////////////////////////// Ordered axioms //////////////////////////////
predicate StrictlyPositive(x: RR)

lemma Trichotomy(x: RR)
	ensures {:axiom} ExactlyOneOf(StrictlyPositive(x), StrictlyPositive(neg(x)), x == Zero)

lemma Closure(x: RR, y: RR)
	requires StrictlyPositive(x)
	requires StrictlyPositive(y)
	ensures {:axiom} StrictlyPositive(add(x, y))
	ensures {:axiom} StrictlyPositive(mult(x, y))


////////////////////////////////////// Ordered Theorems ///////////////////////////////
ghost predicate StrictlyNegative(x: RR) {
	!StrictlyPositive(x) && x != Zero
}

ghost predicate lt(x: RR, y: RR) {
	StrictlyPositive(sub(y, x))
}

ghost predicate gt(x: RR, y: RR) {
	lt(y, x)
}

ghost predicate le(x: RR, y: RR) {
	lt(x, y) || x == y
}

ghost predicate ge(x: RR, y: RR) {
	gt(x, y) || x == y
}

lemma ComparisonTrichotomy(x: RR, y: RR)
	ensures ExactlyOneOf(lt(x, y), gt(x, y), x == y)
{
	assert ExactlyOneOf(StrictlyPositive(sub(y, x)), StrictlyPositive(neg(sub(y, x))), sub(y, x) == Zero) by {Trichotomy(sub(y, x));}

	if StrictlyPositive(sub(y, x)) {
		assert lt(x, y);

		if gt(x, y) {
			assert StrictlyPositive(sub(x, y));
			assert !StrictlyPositive(neg(sub(y, x))) by {Trichotomy(sub(y, x));}
			assert !StrictlyPositive(sub(x, y))      by {NegOfSub(y, x);}
			assert false;
		}
	}
	else if StrictlyPositive(neg(sub(y, x))) {
		assert StrictlyPositive(sub(x, y)) by {NegOfSub(y, x);}
		assert ge(x, y);
	}
	else if sub(y, x) == Zero {
		assert y == add(Zero, x) by {AddOnBothSides(y, x, Zero);}
		assert y == x            by {Conmutativity(Zero, x); Neutral(x);}
	}
}

lemma GreaterThanZero(x: RR)
	requires gt(x, Zero)
	ensures StrictlyPositive(x)
	ensures x != Zero
	ensures StrictlyNegative(neg(x))
	ensures lt(neg(x), Zero)
{
	assert StrictlyPositive(sub(x, Zero));
	assert sub(x, Zero) == x               by {Neutrals(x);}
	assert StrictlyPositive(x);
	assert x != Zero                       by {Trichotomy(x);}

	// Contradiction
	if !StrictlyNegative(neg(x)) {
		assert StrictlyPositive(neg(x)) || neg(x) == Zero;
		if StrictlyPositive(neg(x)) {
			assert !StrictlyPositive(x) by {Trichotomy(x);}
			assert false;
		}
		else if neg(x) == Zero {
			assert neg(neg(x)) == Zero by {NegZeroIsZero();}
			assert x == Zero           by {NegOfNeg(x);}
			assert false;
		}
	}

	assert x == sub(Zero, neg(x)) by {NegOfNeg(x); Neutrals(neg(x));}
	assert StrictlyPositive(sub(Zero, neg(x)));
}

lemma LessThanZero(x: RR)
	requires lt(x, Zero)
	ensures StrictlyNegative(x)
	ensures x != Zero
	ensures StrictlyPositive(neg(x))
	ensures gt(neg(x), Zero)
{
	assert StrictlyPositive(sub(Zero, x));
	assert sub(Zero, x) == neg(x)             by {Neutrals(x);}
	assert StrictlyPositive(neg(x));

	assert x != Zero && !StrictlyPositive(x)  by {Trichotomy(x);}

	assert neg(x) == sub(neg(x), Zero)        by {Neutrals(neg(x));}
	assert StrictlyPositive(sub(neg(x), Zero));
}

lemma ComparisonClosure(x: RR, y: RR)
	requires gt(x, Zero)
	requires gt(y, Zero)
	ensures gt(mult(x, y), Zero)
{
	assert StrictlyPositive(x)                 by {GreaterThanZero(x);}
	assert StrictlyPositive(y)                 by {GreaterThanZero(y);}
	assert StrictlyPositive(mult(x, y))        by {Closure(x, y);}
	assert mult(x, y) == sub(mult(x, y), Zero) by {Neutrals(mult(x, y));}

	assert StrictlyPositive(sub(mult(x, y), Zero));
}

lemma IneqTransitivityLeft(x: RR, y: RR, z: RR)
	requires lt(x, y)
	requires lt(y, z)
	ensures lt(x, z)
{
	assert StrictlyPositive(sub(y, x));
	assert StrictlyPositive(sub(z, y));

	assert StrictlyPositive(add(sub(z, y), sub(y, x)))                       by {Closure(sub(z, y), sub(y, x));}
	assert add(sub(z, y), sub(y, x)) == add(add(z, neg(y)), add(y, neg(x)));
	assert add(sub(z, y), sub(y, x)) == add(z, add(neg(y), add(y, neg(x))))  by {Associativity(z, neg(y), add(y, neg(x)));}
	assert add(sub(z, y), sub(y, x)) == add(z, add(add(neg(y), y), neg(x)))  by {Associativity(neg(y), y, neg(x));}
	assert add(sub(z, y), sub(y, x)) == add(z, neg(x))                       by {Neutrals(neg(x));}
	assert add(sub(z, y), sub(y, x)) == sub(z, x)                            by {Neutrals(neg(x));}
}

lemma IneqTransitivityRight(x: RR, y: RR, z: RR)
	requires gt(x, y)
	requires gt(y, z)
	ensures gt(x, z)
{
	assert StrictlyPositive(sub(x, y));
	assert StrictlyPositive(sub(y, z));

	assert StrictlyPositive(add(sub(x, y), sub(y, z)))                        by {Closure(sub(x, y), sub(y, z));}
	assert add(sub(x, y), sub(y, z)) == add(add(x, neg(y)), add(y, neg(z)));
	assert add(sub(x, y), sub(y, z)) == add(x, add(neg(y), add(y, neg(z))))   by {Associativity(x, neg(y), add(y, neg(z)));}
	assert add(sub(x, y), sub(y, z)) == add(x, add(add(neg(y), y), neg(z)))   by {Associativity(neg(y), y, neg(z));}
	assert add(sub(x, y), sub(y, z)) == add(x, neg(z))                        by {Neutrals(neg(z));}
	assert add(sub(x, y), sub(y, z)) == sub(x, z);
}

lemma IneqTransitivity(x: RR, y: RR, z: RR)
	ensures lt(x, y) && lt(y, z) ==> lt(x, z)
	ensures gt(x, y) && gt(y, z) ==> gt(x, z)

	ensures le(x, y) && le(y, z) ==> le(x, z)
	ensures ge(x, y) && ge(y, z) ==> ge(x, z)
{
	if lt(x, y) && lt(y, z) {
		IneqTransitivityLeft(x, y, z);
	}
	if gt(x, y) && gt(y, z) {
		IneqTransitivityRight(x, y, z);
	}
}

lemma StrictIneqAddOnBothSides(x: RR, y: RR, a: RR)
	requires lt(x, y)
	ensures lt(add(x, a), add(y, a))
{
	assert StrictlyPositive(sub(y, x));

	assert sub(add(y, a), add(x, a)) == add(add(y, a), add(neg(x), neg(a))) by {NegOfSum(x, a);}
	assert sub(add(y, a), add(x, a)) == add(add(y, a), add(neg(a), neg(x))) by {Conmutativity(neg(x), neg(a));}
	assert sub(add(y, a), add(x, a)) == add(y, add(a, add(neg(a), neg(x)))) by {Associativity(y, a, add(neg(a), neg(x)));}
	assert sub(add(y, a), add(x, a)) == add(y, add(add(a, neg(a)), neg(x))) by {Associativity(a, neg(a), neg(x));}
	assert sub(add(y, a), add(x, a)) == add(y, neg(x))                      by {Neutrals(x);}
	assert sub(add(y, a), add(x, a)) == sub(y, x);
}

lemma IneqAddOnBothSides(x: RR, y: RR, a: RR)
	ensures lt(x, y) ==> lt(add(x, a), add(y, a))
	ensures gt(x, y) ==> gt(add(x, a), add(y, a))

	ensures le(x, y) ==> le(add(x, a), add(y, a))
	ensures ge(x, y) ==> ge(add(x, a), add(y, a))
{
	assert ExactlyOneOf(lt(x, y), gt(x, y), x == y) by {ComparisonTrichotomy(x, y);}
	if x == y {
		assert add(x, a) == add(y, a);
	}
	else if lt(x, y) {
		assert lt(add(x, a), add(y, a)) by {StrictIneqAddOnBothSides(x, y, a);}
	}
	else if gt(x, y) {
		assert lt(add(y, a), add(x, a)) by {StrictIneqAddOnBothSides(y, x, a);}
	}
}

lemma IneqSubOnBothSides(x: RR, y: RR, a: RR)
	ensures lt(x, y) ==> lt(sub(x, a), sub(y, a))
	ensures gt(x, y) ==> gt(sub(x, a), sub(y, a))

	ensures le(x, y) ==> le(sub(x, a), sub(y, a))
	ensures ge(x, y) ==> ge(sub(x, a), sub(y, a))
{
	IneqAddOnBothSides(x, y, neg(a));
}

lemma IneqMultOnBothSidesPos(x: RR, a: RR, b: RR)
	requires gt(a, Zero)
	requires a != Zero // TODO: Remove
	requires lt(div(x, a), b)
	ensures lt(x, mult(b, a))
{
	assert StrictlyPositive(sub(b, div(x, a)));
	assert StrictlyPositive(a) by {GreaterThanZero(a);}
	assert StrictlyPositive(mult(sub(b, div(x, a)), a)) by {Closure(sub(b, div(x, a)), a);}

	assert mult(sub(b, div(x, a)), a) == mult(add(b, neg(div(x, a))), a);
	assert mult(sub(b, div(x, a)), a) == mult(a, add(b, neg(div(x, a))))                  by {Conmutativity(a, add(b, neg(div(x, a))));}
	assert mult(sub(b, div(x, a)), a) == add(mult(a, b), mult(a, neg(div(x, a))))         by {Distribuitivity(a, b, neg(div(x,a)));}
	assert mult(sub(b, div(x, a)), a) == add(mult(a, b), neg(mult(a, div(x, a))))         by {NegOfProd(a, div(x, a));}
	assert mult(sub(b, div(x, a)), a) == add(mult(a, b), neg(mult(a, mult(x, inv(a)))));
	assert mult(sub(b, div(x, a)), a) == add(mult(a, b), neg(mult(a, mult(inv(a), x))))   by {Conmutativity(x, inv(a));}
	assert mult(sub(b, div(x, a)), a) == add(mult(a, b), neg(mult(mult(a, inv(a)), x)))   by {Associativity(a, inv(a), x);}
	assert mult(sub(b, div(x, a)), a) == add(mult(a, b), neg(x))                          by {Neutrals(x);}
	assert mult(sub(b, div(x, a)), a) == sub(mult(a, b), x);
	assert mult(sub(b, div(x, a)), a) == sub(mult(b, a), x)                               by {Conmutativity(a, b);}

	assert StrictlyPositive(sub(mult(b, a), x));
}

lemma IneqMultOnBothSidesNeg(x: RR, a: RR, b: RR)
	requires lt(a, Zero)
	requires a != Zero // TODO: Remove
	requires lt(div(x, a), b)
	ensures gt(x, mult(b, a))
{
	assert StrictlyPositive(sub(b, div(x, a)));
	assert StrictlyPositive(neg(a)) by {LessThanZero(a);}
	assert StrictlyPositive(mult(sub(b, div(x, a)), neg(a)))                           by {Closure(sub(b, div(x, a)), neg(a));}

	assert mult(sub(b, div(x, a)), neg(a)) == mult(sub(div(x, a), b), a)               by {NegOfProd(sub(b, div(x, a)), a); NegOfSub(b, div(x, a));}
	assert mult(sub(b, div(x, a)), neg(a)) == mult(a, sub(div(x, a), b))               by {Conmutativity(sub(div(x, a), b), a);}
	assert mult(sub(b, div(x, a)), neg(a)) == add(mult(a, div(x, a)), mult(a, neg(b))) by {Distribuitivity(a, div(x, a), neg(b));}
	assert mult(sub(b, div(x, a)), neg(a)) == add(mult(div(x, a), a), mult(a, neg(b))) by {Conmutativity(a, div(x, a));}
	assert mult(sub(b, div(x, a)), neg(a)) == add(x, mult(a, neg(b)))                  by {Associativity(x, inv(a), a); Neutrals(x);}
	assert mult(sub(b, div(x, a)), neg(a)) == add(x, neg(mult(a, b)))                  by {NegOfProd(a, b);}
	assert mult(sub(b, div(x, a)), neg(a)) == sub(x, mult(a, b));
	assert mult(sub(b, div(x, a)), neg(a)) == sub(x, mult(b, a))                       by {Conmutativity(a, b);}

	assert StrictlyPositive(sub(x, mult(a, b)));
}

function square(x: RR): RR {mult(x, x)}

lemma SquaresNonnegative(x: RR)
	ensures ge(square(x), Zero)
{
	assert ExactlyOneOf(lt(x, Zero), gt(x, Zero), x == Zero) by {ComparisonTrichotomy(x, Zero);}

	if x == Zero {
		assert mult(x, x) == Zero by {AnythingTimesZeroIsZero(Zero);}
		assert ge(Zero, Zero);
	}
	else if gt(x, Zero) {
		assert gt(mult(x, x), Zero) by {ComparisonClosure(x, x);}
	}
	else if le(x, Zero) {
		assert gt(neg(x), Zero)                   by {LessThanZero(x);}
		assert gt(mult(neg(x), neg(x)), Zero)     by {ComparisonClosure(neg(x), neg(x));}
		assert mult(neg(x), neg(x)) == mult(x, x) by {ProdOfNeg(x, x);}
	}
}

lemma OneIsPositive()
	ensures gt(One, Zero)
	ensures StrictlyPositive(One)
{
	assert One == square(One)    by {Neutrals(One);}
	assert ge(square(One), Zero) by {SquaresNonnegative(One);}
	assert One != Zero           by {Neutrals(One);}
	assert gt(One, Zero);

	assert StrictlyPositive(sub(One, Zero));
	assert sub(One, Zero) == One by {Neutrals(One);}
}

ghost function OneAsAPositive(): RR
	ensures StrictlyPositive(One)
{
	assert StrictlyPositive(One) by {OneIsPositive();}
	One
}

ghost function MinusOneAsNegative(): RR
	ensures lt(MinusOneAsNegative(), Zero)
	ensures StrictlyNegative(MinusOneAsNegative())
	ensures MinusOneAsNegative() == sub(Zero, One)
{
	var minusOne := neg(One);
	assert StrictlyPositive(One) by {OneIsPositive();}
	assert !StrictlyPositive(minusOne) by {Trichotomy(One);}
	assert minusOne != Zero by {assert add(One, minusOne) == Zero; Neutrals(One);}
	assert StrictlyNegative(minusOne);

	assert sub(Zero, minusOne) == neg(minusOne) == One by {Neutrals(minusOne); NegOfNeg(One);}
	assert lt(minusOne, Zero);

	assert minusOne == sub(Zero, One) by {Neutrals(One);}

	minusOne
}

ghost const MinusOne := MinusOneAsNegative()

// type RRPA = x: RR | StrictlyPositive(x) ghost witness OneAsAPositive()

///////////////////////////////////// Naturals ////////////////////////////////////
ghost function inc(x: RR): RR {add(x, One)}

ghost function dec(x: RR): RR {sub(x, One)}

ghost predicate IsInductive(s: iset<RR>) {
	Zero in s && (forall x :: (x in s ==> inc(x) in s))
}

ghost predicate IsNatural(n: RR) {
	forall s :: IsInductive(s) ==> n in s
}

lemma ZeroIsNatural()
	ensures IsNatural(Zero)
{
	forall s: iset<RR>
		ensures IsInductive(s) ==> Zero in s
	{
		if IsInductive(s) {
			assert Zero in s; // Definition if IsInductive
		}
	}
}

lemma IncIsNatural(n: RR)
	requires IsNatural(n)
	ensures IsNatural(inc(n))
{
	forall s: iset<RR>
		ensures IsInductive(s) ==> inc(n) in s
	{
		if IsInductive(s) {
			assert n in s;
			assert n in s ==> inc(n) in s; // Def of inductive sets
		}
	}
}

ghost function ZeroAsNatural(): RR
	ensures IsNatural(Zero)
{
	assert IsNatural(Zero) by {ZeroIsNatural();}
	Zero
}

type NN =  n: RR | IsNatural(n) ghost witness ZeroAsNatural()

predicate Xor(a: bool, b: bool) {(a && !b) || (!a && b)}

ghost const setOfNaturals := iset n: NN
lemma NaturalsAreInductive()
	ensures IsInductive(setOfNaturals)
{} // Dafny does this automatically

// TODO: Replace with naturals are nonnegative???
ghost const setOfNonnegatives := iset r: RR | ge(r, Zero)
lemma NonnegativesAreInductive()
	ensures IsInductive(setOfNonnegatives)
{
	assert Zero in setOfNonnegatives;
	forall x: RR ensures x in setOfNonnegatives ==> inc(x) in setOfNonnegatives {
		if x in setOfNonnegatives {
			assert ge(x, Zero);
			assert ge(add(x, One), add(Zero, One)) by {IneqAddOnBothSides(Zero, x, One);}
			assert ge(inc(x), One)                 by {Neutrals(One);}
			assert ge(One, Zero)                   by {OneIsPositive();}
			assert ge(inc(x), Zero)                by {IneqTransitivity(inc(x), One, Zero);}
			assert inc(x) in setOfNonnegatives;
		}
	}
}

lemma NaturalsAreNonnegative(n: NN)
	ensures ge(n, Zero)
{
	assert IsInductive(setOfNonnegatives) by {NonnegativesAreInductive();}
	// Dafny does this by itself
}

ghost function allRealsBut(x: RR): iset<RR> {
	iset y: RR {:trigger} | y != x
}

lemma NaturalCaracterization(n: NN)
	ensures Xor(n == Zero, exists m: NN :: n == inc(m))
{
	if n == Zero {
		assert IsInductive(setOfNonnegatives) by {NonnegativesAreInductive();}

		// Contradiction
		forall m: NN ensures Zero != inc(m) {
			// Prove: m is -1 and -1 is not a part of nonnegatives
			if inc(m) == Zero {
				assert sub(Zero, One) == m        by {SubstractOnBothSides(m, One, Zero);}
				assert sub(Zero, One) == MinusOne by {Neutrals(One);}
				assert m == MinusOne;

				assert lt(MinusOne, Zero);
				assert false by {ComparisonTrichotomy(m, Zero); NaturalsAreNonnegative(m);}
			}
		}
	}
	else if n != Zero {
		// Contradiction
		if !(exists m: NN :: n == inc(m)) {
			// Idea: Create an inductive set of which n is not a part of
			// increment of all naturals union {0}
			ghost var setOfAllIncrements := iset x: RR {:trigger} | x == Zero || (exists y: NN :: x == inc(y));

			assert IsInductive(setOfAllIncrements) by {
				assert Zero in setOfAllIncrements;
				forall x: RR
					ensures x in setOfAllIncrements ==> inc(x) in setOfAllIncrements
				{
					if x in setOfAllIncrements {
						if x == Zero {
							assert IsNatural(Zero) by {ZeroIsNatural();}
							assert inc(Zero) in setOfAllIncrements;
						}
						else if exists y: NN :: x == inc(y) {
							ghost var y: NN :| x == inc(y);
							assert IsNatural(inc(y))      by {IncIsNatural(y);}
							assert IsNatural(inc(inc(y))) by {IncIsNatural(inc(y));}
							assert inc(x) in setOfAllIncrements;
						}
					}
				}
			}

			assert n in setOfAllIncrements by {assert IsInductive(setOfAllIncrements);} // naturals are in all inductive sets
			assert n !in setOfAllIncrements by {assert n != Zero && !(exists m: NN :: n == inc(m));}
			assert false;
		}
	}
}

lemma NaturalDecCaracterization(n: NN)
	ensures Xor(n == Zero, IsNatural(dec(n)))
{
	assert Xor(n == Zero, exists m: NN :: n == inc(m)) by {NaturalCaracterization(n);}

	if n != Zero && exists m: NN :: n == inc(m) {
		ghost var m: NN :| n == inc(m);
		assert dec(n) == m by {SubstractOnBothSides(m, One, n);}
		assert IsNatural(dec(n));
	}
	else if n == Zero && !(exists m: NN :: n == inc(m)) {
		assert dec(n) == MinusOne;
		assert !IsNatural(dec(n)) by {
			// Contradiction
			if IsNatural(dec(n)) {
				assert ge(dec(n), Zero) by {NaturalsAreNonnegative(dec(n));}
				assert lt(dec(n), Zero);
				assert false            by {ComparisonTrichotomy(dec(n), Zero);}
			}
		}
	}
}

lemma WeakInduction(prop: (NN) -> bool)
	requires prop(Zero)
	requires forall n: NN :: prop(n) ==> prop(inc(n))
	ensures forall n: NN :: prop(n)
{
	ghost var setWhereItHolds := iset x: NN | prop(x);
	assert IsInductive(setWhereItHolds);
}

lemma NatClosureAdd(n: NN, m: NN)
	ensures IsNatural(add(n, m))
{
	var addingQIsNatural := (q: NN) => (forall p: NN :: IsNatural(add(p, q)));
	assert addingQIsNatural(Zero) by {
		forall p: NN ensures IsNatural(add(p, Zero)) {
			assert add(p, Zero) == p by {Neutrals(p);}
		}
	}

	forall q: NN ensures addingQIsNatural(q) ==> addingQIsNatural(inc(q)) {
		if addingQIsNatural(q) {
			forall p: NN ensures IsNatural(add(p, inc(q))) {
				assert add(p, inc(q)) == inc(add(p, q)) by {Associativity(p, q, One);}
				assert IsNatural(inc(add(p, q)))        by {IncIsNatural(add(p, q));}
			}
		}
	}

	assert forall q: NN :: addingQIsNatural(q) by {WeakInduction(addingQIsNatural);}
	assert addingQIsNatural(m);
}

lemma NatClosureMult(n: NN, m: NN)
	ensures IsNatural(mult(n, m))
{
	var multiplyingByQIsNatural := (q: NN) => (forall p: NN :: IsNatural(mult(p, q)));
	assert multiplyingByQIsNatural(Zero) by {
		forall p: NN ensures IsNatural(mult(p, Zero)) {
			assert mult(p, Zero) == Zero by {AnythingTimesZeroIsZero(p);}
		}
	}

	forall q: NN ensures multiplyingByQIsNatural(q) ==> multiplyingByQIsNatural(inc(q)) {
		if multiplyingByQIsNatural(q) {
			forall p: NN ensures IsNatural(mult(p, inc(q))) {
				assert mult(p, inc(q)) == add(mult(p, q), mult(p, One)) by {Distribuitivity(p, q, One);}
				assert mult(p, inc(q)) == add(mult(p, q), p)            by {Neutrals(p);}
				assert IsNatural(add(mult(p, q), p))                    by {NatClosureAdd(mult(p, q), p);}
			}
		}
	}

	assert forall q: NN :: multiplyingByQIsNatural(q) by {WeakInduction(multiplyingByQIsNatural);}
	assert multiplyingByQIsNatural(m);
}

lemma NatClosure(n: NN, m: NN)
	ensures IsNatural(add(n, m))
	ensures IsNatural(mult(n, m))
{
	NatClosureAdd(n, m);
	NatClosureMult(n, m);
}

/////////////////////////////////////// Complete axioms ////////////////////////////////
ghost predicate IsAnUpperBound(s: iset<RR>, M: RR) {
	forall x :: x in s ==> le(x, M)
}

ghost predicate UpperBounded(s: iset<RR>) {
	exists M: RR :: IsAnUpperBound(s, M)
}

ghost predicate IsALowerBound(s: iset<RR>, M: RR) {
	forall x :: x in s ==> ge(x, M)
}

ghost predicate LowerBounded(s: iset<RR>) {
	exists M: RR :: IsALowerBound(s, M)
}

ghost predicate IsTheSupremum(s: iset<RR>, M: RR) {
	IsAnUpperBound(s, M) && forall N: RR :: IsAnUpperBound(s, N) ==> ge(N, M)
}

ghost predicate IsTheInfimum(s: iset<RR>, M: RR) {
	IsALowerBound(s, M) && forall N: RR :: IsALowerBound(s, N) ==> le(N, M)
}

lemma SupremumExists(s: iset<RR>)
	requires exists x :: x in s
	requires UpperBounded(s)
	ensures {:axiom} exists M: RR :: IsTheSupremum(s, M)


///////////////////////////////////// Complete Theorems ////////////////////////////////
//lemma SqrtExists(x: RR)
//	requires ge(x, Zero)
//	ensures exists y :: (ge(y, Zero) && square(y) == x)
//{
//	var numbersLessThan := iset r: RR | le(square(r), x);
//
//	assert Zero in numbersLessThan by {
//		assert square(Zero) == Zero by {AnythingTimesZeroIsZero(Zero);}
//		assert le(Zero, x); // <=> ge(x, Zero)
//	}
//
//	assert IsAnUpperBound(numbersLessThan) by {
//	}
//
//	assume {:axiom} exists y :: (ge(y, Zero) && square(y) == x);
//}
