open ring[G] as G
open ring[H] as H
open ring[C] as C

//The two signatures represent rings, where G has a relation f which maps into the ring H
sig G {
	f : H,
	pi : C
}

sig C {
	inc : H
}

sig H {}


//Checks to make sure that the relation f in the signature G is a ring homomorphism
pred IsHomMain[f : G->H]{
	f[G/e] = H/e
	all g1, g2 : G | f[G/ad[g1,g2]] = H/ad[f[g1],f[g2]]
	all g1, g2 : G | f[G/m[g1,g2]] = H/m[f[g1],f[g2]]
}

pred IsHomQuot[f : G->C]{
	f[G/e] = C/e
	all g1, g2 : G | f[G/ad[g1,g2]] = C/ad[f[g1],f[g2]]
	all g1, g2 : G | f[G/m[g1,g2]] = C/m[f[g1],f[g2]]
}

pred IsHomInc[f : C->H]{
	f[C/e] = H/e
	all c1, c2 : C | f[C/ad[c1,c2]] = H/ad[f[c1],f[c2]]
	all c1, c2 : C | f[C/m[c1,c2]] = H/m[f[c1],f[c2]]
}



pred IsSurjective[f : G->C]{
	all c : C | some f.c
}

pred IsInjective[ f: C->H]{
	all h : H | lone f.h
}

// Displays which elements in the visualizer are the additive identities for G and H
pred showAdditiveIdentities {
	some g: G | g = G/ade
	some h : H | h = H/ade
//	some c : C | c = C/ade
}

//Displays which elements in the visualizer are the multiplicative identities for G and H
pred showMultiplicativeIdentities {
	some g : G | g = G/e
	some h : H | h = H/e
	//some c : C | c = C/e
}

//Displays the elements of G and H which are neither of the identities
pred showNonIdentities {
	some S : set G | all g : G | (not g = G/ade and not g = G/e <=> g in S)
	some S : set H | all h : H | (not h = H/ade and not h = H/e <=> h in S)
}

pred DiagramCommutative[f: G -> H, g : G -> C, h : C -> H] {
	all g1 : G | h[g[g1]] = f[g1]
}

//Depicts the homomorphism between G and H and how elements are mapped between the rings
run Picture {
	IsHomMain[f]
	IsHomQuot[pi]
	IsHomInc[inc]
	IsSurjective[pi]
	IsInjective[inc]
	showAdditiveIdentities
	showMultiplicativeIdentities
	showNonIdentities
	DiagramCommutative[f,pi,inc]
	showKernel 
} for exactly 2 G, exactly 4 H, exactly 2 C

pred showKernel {
	some K : set G | K = f.H/ade
}






