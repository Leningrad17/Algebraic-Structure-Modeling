module ring[elem]

// Signature for a ring, containing the addition operation and multiplicative operation 
private one sig Ring {
	add : elem -> elem -> one elem,
	mult : elem -> elem -> one elem,
	addid : one elem,
	multid : one elem,
	addinv : elem -> one elem 
}
{
	// associative law for addition
	all g1, g2, g3 : elem | add[g1, add[g2, g3]] = add[add[g1, g2], g3]
	// unit laws for addition
	all g : elem | ad[ade, g] = g
	all g : elem | ad[g, ade] = g
	// inverse laws for addition
	all g : elem | ad[adi[g], g] = ade
	all g : elem | ad[g, adi[g]] = ade
	//commutativity for addition
	all g1, g2 : elem | add[g1,g2] = add[g2,g1]
	// associativity for multiplication
	all g1, g2, g3 : elem | mult[g1,mult[g2,g3]] = mult[mult[g1,g2],g3]
	// unit laws for multiplication
	all g: elem | m[e,g] = g
	all g: elem | m[g,e] = g
	// commutativity for multiplication
	all g1,g2 : elem | mult[g1,g2] = mult[g2,g1]
	//distributivity for multiplication
	all g1, g2, g3 : elem | m[g1, ad[g2,g3]] = ad[m[g1,g2],m[g1,g3]]
	all g1, g2, g3 : elem | m[ad[g1,g2],g3] = ad[m[g1,g3],m[g2,g3]]
	//
	
}

fun ad : elem -> elem -> elem { Ring.add }
fun ade : elem { Ring.addid }
fun adi : elem -> elem { Ring.addinv }
fun m : elem -> elem -> elem {Ring.mult}
fun e: elem {Ring.multid}

