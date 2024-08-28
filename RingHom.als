open ring[G] as G
open ring[H] as H

//The two signatures represent rings, where G has a relation f which maps into the ring H
sig G {
	f : H
}

sig H {}

//Checks to make sure that the relation f in the signature G is a ring homomorphism
pred IsHom[f : G->H]{
	f[G/e] = H/e
	all g1, g2 : G | f[G/ad[g1,g2]] = H/ad[f[g1],f[g2]]
	all g1, g2 : G | f[G/m[g1,g2]] = H/m[f[g1],f[g2]]
}

// Displays which elements in the visualizer are the additive identities for G and H
pred showAdditiveIdentities {
	some g: G | g = G/ade
	some h : H | h = H/ade
}

//Displays which elements in the visualizer are the multiplicative identities for G and H
pred showMultiplicativeIdentities {
	some g : G | g = G/e
	some h : H | h = H/e
}

//Displays the elements of G and H which are neither of the identities
pred showNonIdentities {
	some S : set G | all g : G | (not g = G/ade and not g = G/e <=> g in S)
	some S : set H | all h : H | (not h = H/ade and not h = H/e <=> h in S)
} 

//Depicts the homomorphism between G and H and how elements are mapped between the rings
run Picture {
	IsHom[f]
	showAdditiveIdentities
	showMultiplicativeIdentities
	showNonIdentities
} for exactly 2 G, exactly 2 H
