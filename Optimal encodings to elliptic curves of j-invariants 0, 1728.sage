/////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
Covers phi: H -> Ea and phiPr: H -> EaPr
/////////////////////////////////////////////////////////////////////////////////////////////////////////////////////



// degree n = 2
F := Rationals();
F<a> := FunctionField(F);
F<c> := FunctionField(F);
PR<t> := PolynomialRing(F);
F<sa> := ext<F | t^2 - a>;

AS<x,y> := AffineSpace(F, 2);
Ea := Curve(AS, y^2 - (x^3 - a*x) );
Eac := Curve(AS, c*y^2 - (x^3 - a*x) );
f := 3*c*sa*(2*c^3*x^6 - 3*c^2*x^4 - 3*c*x^2 + 2);
H := Curve(AS, y^2 - f);

phi := map<H -> Ea | [
    sa*(c*x^2 - 2) / (-3*c*x^2), 
    2*sa*y / (3^2*c^2*x^3) ]>;
phiPr := map<H -> Eac | [
    sa*(2*c*x^2 - 1) / 3, 
    2*sa*y / (3^2*c) ]>;




////////////////////////////////////////////////////////////////////////////




// degree n = 3
F<s3> := QuadraticField(3);
PR<t> := PolynomialRing(F);
F<s> := ext<F | t^2 - 2*s3>;
F<a> := FunctionField(F);

AS<x,y> := AffineSpace(F,2);
Ea := Curve(AS, y^2 - (x^3 - a*x) );
Eaa := Curve(AS, a*y^2 - (x^3 - a*x) );
f := 2*s*a*(2*s3*x^5 - 7*a*x^3 + 2*s3*a^2*x);
H := Curve(AS, y^2 - f);

phi := map<H -> Ea | [
    3*(2*x^3 - s3*a*x) / (s*a), 
    s*(2*s3*x^2 - a)*y / (2^2*a^2) ]>;
phiPr := map<H -> Eaa | [
    s*x^3 / (3*(s3*x^2 - 2*a)),
    (x^3 - 2*s3*a*x)*y / (3*s*a*(s3*x^2 - 2*a)^2) ]>;


///////////////////////////////////////////////////////////////////////



// degree n = 4
F<i> := QuadraticField(-1);
F<a> := FunctionField(F);
AS<x,y> := AffineSpace(F,2);
Ea := Curve(AS, y^2 - (x^3 - a*x) );
Eaa := Curve(AS, a*y^2 - (x^3 - a*x) );
f := 2*3*a*(3^2*x^5 - 2*7*a*x^3 + 3^2*a^2*x);
H := Curve(AS, y^2 - f);

phi := map<H -> Ea | [
    2^4*i*a^2*x / (3*(3*x^2 - a)^2),
    2*(i-1)*a*(3^2*x^2 + a)*y / (3^2*(3*x^2 - a)^3) ]>;
phiPr := map<H -> Eaa | [
    2^4*i*a*x^3 / (3*(x^2 - 3*a)^2),
    2*(i-1)*(x^3 + 3^2*a*x)*y / (3^2*(x^2 - 3*a)^3) ]>;






/////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
Derivation of the last formulas
/////////////////////////////////////////////////////////////////////////////////////////////////////////////////////






// Degree 2 isogenies from Ea and their duals
F<i> := QuadraticField(-1);
F<a> := FunctionField(F);
PR<t> := PolynomialRing(F);
F<sa> := ext<F | t^2 - a>;
PR<x> := PolynomialRing(F);

Ea := EllipticCurve([F | -a, 0]);
Epl, phiPlDual := IsogenyFromKernel(Ea, x - sa);
Emin, phiMinDual := IsogenyFromKernel(Ea, x + sa);
phiPl := Expand(DualIsogeny(phiPlDual));
phiMin := Expand(DualIsogeny(phiMinDual));

Epl;
Emin;
phiPl;
phiMin;

E, phi0Dual := IsogenyFromKernel(Ea, x);
bool, iso := IsIsomorphic(E, Ea);
e := phi0Dual*iso;
e;



////////////////////////////////////////////////////////////////////////////




// Genus 2 curve H as well as covers chiPl: H -> Epl and chiMin: H -> Emin;
F<s2> := QuadraticField(2);
F<a> := FunctionField(F);
PR<t> := PolynomialRing(F);
F<sa> := ext<F | t^2 - a>;

r0 := (1 + 2*s2)*sa;
r1 := (1 - 2*s2)*sa;
s0 := -(1 - 2*s2)*sa;
s1 := -(1 + 2*s2)*sa;
r2 := -(r0 + r1);
s2 := -(s0 + s1);

a4 := r0*r1 + r0*r2 + r1*r2;
a6 := -r0*r1*r2;
b4 := s0*s1 + s0*s2 + s1*s2;
b6 := -s0*s1*s2;

AS<x,y> := AffineSpace(F, 2);
Epl := Curve(AS, y^2 - (x^3 + a4*x + a6) );
Emin := Curve(AS, y^2 - (x^3 + b4*x + b6) );
D := -(4*a4^3 + 27*a6^2);
C := -(4*b4^3 + 27*b6^2);

R0 := (r0-r2)^2/(s0-s2) + (r2-r1)^2/(s2-s1) + (r1-r0)^2/(s1-s0);
S0 := (s0-s2)^2/(r0-r2) + (s2-s1)^2/(r2-r1) + (s1-s0)^2/(r1-r0);
R1 := r0*(s2-s1) + r1*(s0-s2) + r2*(s1-s0);
S1 := s0*(r2-r1) + s1*(r0-r2) + s2*(r1-r0); 
A := C*R0/R1;
B := D*S0/S1;

A0 := A*(r0-r1)*(r1-r2); 
A1 := A*(r1-r2)*(r2-r0);
A2 := A*(r2-r0)*(r0-r1);
B0 := B*(s0-s1)*(s1-s2);
B1 := B*(s1-s2)*(s2-s0);
B2 := B*(s2-s0)*(s0-s1); 

c0 := -B*R1/(A*R0);
d0 := ( r0*(r2-r1)^2/(s2-s1) + r1*(r0-r2)^2/(s0-s2) + 
    r2*(r1-r0)^2/(s1-s0) )/R0;
e0 := C/A^3;
c1 := -A*S1/(B*S0);
d1 := ( s0*(s2-s1)^2/(r2-r1) + s1*(s0-s2)^2/(r0-r2) + 
    s2*(s1-s0)^2/(r1-r0) )/S0;
e1 := D/B^3;

f := -(A0*x^2 + B0)*(A1*x^2 + B1)*(A2*x^2 + B2);
Hpr := Curve(AS, y^2 - f);
chiPlPr := map<Hpr -> Epl | [c0/x^2 + d0, e0*y/x^3]>;
chiMinPr := map<Hpr -> Emin | [c1*x^2 + d1, e1*y]>;

X := x + sa;
Z := x - sa;
f := -(A0*X^2 + B0*Z^2)*(A1*X^2 + B1*Z^2)*(A2*X^2 + B2*Z^2);
H := Curve(AS, y^2 - f);
H;

psi := map<H -> Hpr | [X/Z, y/Z^3]>;
chiPl := Normalization(Expand(psi*chiPlPr));
chiMin := Normalization(Expand(psi*chiMinPr));
chiPl;
chiMin;




///////////////////////////////////////////////////////////////////////




// After simplifying the formulas obtained in the previous steps
F := Rationals();
F<a> := FunctionField(F);
PR<t> := PolynomialRing(F);
F<sa> := ext<F | t^2 - a>;

A2<x,y> := AffineSpace(F, 2);
Ea := Curve(A2, y^2 - (x^3 - a*x) );
Eaa := Curve(A2, a*y^2 - (x^3 - a*x) );
Epl := Curve(A2, y^2 - (x^3 - 11*a*x - 2*7*a*sa) );
Emin := Curve(A2, y^2 - (x^3 - 11*a*x + 2*7*a*sa) );
f := 2*3*a*(3^2*x^5 - 2*7*a*x^3 + 3^2*a^2*x);
H := Curve(A2, y^2 - f);

phiPl := map<Epl -> Ea | [ 
    (x + sa)^2 / (2^2*(x + 2*sa)),
    (x^2 + 2^2*sa*x + 3*a)*y / (2^3*(x + 2*sa)^2) ]>;
phiMin := map<Emin -> Ea | [
    (x - sa)^2 / (2^2*(x - 2*sa)),
    (x^2 - 2^2*sa*x + 3*a)*y / (2^3*(x - 2*sa)^2) ]>;

chiPl := map<H -> Epl | [
    -2*sa*(3*x^2 + 5*sa*x + 3*a) / (3*(x + sa)^2),
    -sa*y / (3^2*(x + sa)^3) ]>;
chiMin := map<H -> Emin | [
    2*sa*(3*x^2 - 5*sa*x + 3*a) / (3*(x - sa)^2),
    sa*y / (3^2*(x - sa)^3) ]>;





///////////////////////////////////////////////////////////////////////////




// Covers phiTilde: H -> Ea and phiPrTilde: H -> Eaa;
F := Rationals();
F<a> := FunctionField(F);
PR<t> := PolynomialRing(F);
F<sa> := ext<F | t^2 - a>;

A2<x,y> := AffineSpace(F, 2);
Ea := Curve(A2, y^2 - (x^3 - a*x) );
Eaa := Curve(A2, a*y^2 - (x^3 - a*x) );
f := 2*3*a*(3^2*x^5 - 2*7*a*x^3 + 3^2*a^2*x);
H := Curve(A2, y^2 - f);

A4<x0,y0,x1,y1> := AffineSpace(F, 4);
Apm := Surface(A4, [
    y0^2 - (x0^3 - 11*a*x0 - 2*7*a*sa),
    y1^2 - (x1^3 - 11*a*x1 + 2*7*a*sa) ]);
A := Surface(A4, [
    y0^2 - (x0^3 - a*x0), 
    y1^2 - (x1^3 - a*x1) ]);
Aa := Surface(A4, [
    y0^2 - (x0^3 - a*x0), 
    a*y1^2 - (x1^3 - a*x1) ]);

chipm := map<H -> Apm | [
    -2*sa*(3*x^2 + 5*sa*x + 3*a) / (3*(x + sa)^2),
    -sa*y / (3^2*(x + sa)^3),
    2*sa*(3*x^2 - 5*sa*x + 3*a) / (3*(x - sa)^2),
    sa*y / (3^2*(x - sa)^3) ]>;

phipm := map<Apm -> A | [
    (x0 + sa)^2 / (2^2*(x0 + 2*sa)), 
    (x0^2 + 2^2*sa*x0 + 3*a)*y0 / (2^3*(x0 + 2*sa)^2), 
    (x1 - sa)^2 / (2^2*(x1 - 2*sa)), 
    (x1^2 - 2^2*sa*x1 + 3*a)*y1 / (2^3*(x1 - 2*sa)^2) ]>;

lamPl := (y0-y1)/(x0-x1);
lamMin := (y0+y1)/(x0-x1);
xpl := lamPl^2 - (x0+x1);
ypl := lamPl*(x1-xpl) - y1;
xmin := lamMin^2 - (x0+x1);
ymin := lamMin*(x1-xmin) + y1;
psipm := map<A -> Aa | [xpl, ypl, xmin, ymin/sa]>;

pr0 := map<Aa -> Ea | [x0,y0]>;
pr1 := map<Aa -> Eaa | [x1,y1]>;

phiTilde := Normalization(Expand(chipm*phipm*psipm*pr0));
phiPrTilde := Normalization(Expand(chipm*phipm*psipm*pr1));
phiTilde;
phiPrTilde;




//////////////////////////////////////////////////////////////////////////




// After simplifying the formulas obtained in the previous step
F := Rationals();
F<a> := FunctionField(F);
AS<x,y> := AffineSpace(F,2);
Ea := Curve(AS, y^2 - (x^3 - a*x) );
Eaa := Curve(AS, a*y^2 - (x^3 - a*x) );
f := 2*3*a*(3^2*x^5 - 2*7*a*x^3 + 3^2*a^2*x);
H := Curve(AS, y^2 - f);

phiTilde := map<H -> Ea | [
    (3^2*x^2 + a)^2 * (3^2*x^4 - 2*7*a*x^2 + 3^2*a^2) / (2^5*3*a*x*(3*x^2 - a)^2),
    (3^6*x^8 - 2^2*3^5*a*x^6 + 2*3^5*a^2*x^4 - 2^2*7*13*a^3*x^2 + 3^2*a^4)*
    (3^2*x^2 + a)*y / (2^8*3^2*a^2*x^2*(3*x^2 - a)^3)]>;
phiPrTilde := map<H -> Eaa | [
    (x^2 + 3^2*a)^2 * (3^2*x^4 - 2*7*a*x^2 + 3^2*a^2) / (2^5*3*x^3*(x^2 - 3*a)^2),
    (3^2*x^8 - 2^2*7*13*a*x^6 + 2*3^5*a^2*x^4 - 2^2*3^5*a^3*x^2 + 3^6*a^4)* 
    (x^2 + 3^2*a)*y / (2^8*3^2*a*x^5*(x^2 - 3*a)^3) ]>;





//////////////////////////////////////////////////////////////////////////////////////////




// Decomposing the functions X0, X1
F := Rationals();
F<a> := FunctionField(F);
// a := 7919; // a prime
F<x> := FunctionField(F);

X0 := (3^2*x^2 + a)^2 * (3^2*x^4 - 2*7*a*x^2 + 3^2*a^2) / (2^5*3*a*x*(3*x^2 - a)^2);
X1 := (x^2 + 3^2*a)^2 * (3^2*x^4 - 2*7*a*x^2 + 3^2*a^2) / (2^5*3*x^3*(x^2 - 3*a)^2);

/* Decomposition(X0);
Decomposition(X1); */

x0 := x/(3*x^2 - a)^2;
X0 eq (2^8*a^3*x0^2 + 3^2)/(2^5*3*a*x0);
x1 := x^3/(x^2 - 3*a)^2;
X1 eq (2^8*a*x1^2 + 3^2)/(2^5*3*x1);





//////////////////////////////////////////////////////////////////////////




// The roots of f, the values of x0, x1 in them, and the polynomials g0, g1
F := Rationals();
PR<t> := PolynomialRing(F);
F<i,s2> := NumberField([t^2 + 1, t^2 - 2]);
F<a> := FunctionField(F);
PR<t> := PolynomialRing(F);
F<sa> := ext<F | t^2 - a>;

PR<x> := PolynomialRing(F);
f := 2*3*a*(3^2*x^5 - 2*7*a*x^3 + 3^2*a^2*x);
Roots(f);
rpl := (i + 2*s2)*sa/3;
rmin := (-i + 2*s2)*sa/3;
rplPr := (i - 2*s2)*sa/3;
rminPr := (-i - 2*s2)*sa/3;
printf"\n";

F<x> := FunctionField(F);
x0 := x/(3*x^2 - a)^2;
Evaluate(x0, 0);
x0rpl := Evaluate(x0, rpl);
x0rmin := Evaluate(x0, rmin);
x0rpl;
x0rmin;
Evaluate(x0, rplPr);
Evaluate(x0, rminPr);

g0 := x*(x - x0rpl)*(x - x0rmin);
g0 eq x^3 + 3^2/(2^8*a^3)*x;
printf"\n";

x1 := x^3/(x^2 - 3*a)^2;
Evaluate(x1, 0);
x1rpl := Evaluate(x1, rpl);
x1rmin := Evaluate(x1, rmin);
x1rpl;
x1rmin;
Evaluate(x1, rplPr);
Evaluate(x1, rminPr);

g1 := x*(x - x1rpl)*(x - x1rmin);
g1 eq x^3 + 3^2/(2^8*a)*x;





///////////////////////////////////////////////////////////////////////





// Square roots of f0, f1 in the function field of the curve H
F := Rationals();
F<a> := FunctionField(F);
F<x> := FunctionField(F);
f := 2*3*a*(3^2*x^5 - 2*7*a*x^3 + 3^2*a^2*x);
PR<t> := PolynomialRing(F);
F<y> := ext<F | t^2 - f>;

x0 := x/(3*x^2 - a)^2;
x1 := x^3/(x^2 - 3*a)^2;
f0 := 2*3*(x0^3 + 3^2/(2^8*a^3)*x0);
f1 := 2*3*(x1^3 + 3^2/(2^8*a)*x1);
PR<t> := PolynomialRing(F);
Roots(t^2 - f0);
Roots(t^2 - f1);





////////////////////////////////////////////////////////////////////////////





// Covers phi: H -> Ea and phiPr: H -> Eaa
F<i> := QuadraticField(-1);
F<a> := FunctionField(F);
AS<x,y> := AffineSpace(F,2);
Ea := Curve(AS, y^2 - (x^3 - a*x) );
Eaa := Curve(AS, a*y^2 - (x^3 - a*x) );
E := Curve(AS, y^2 - 2*3*(x^3 + 3^2/(2^8*a^3)*x) );
Epr := Curve(AS, y^2 - 2*3*(x^3 + 3^2/(2^8*a)*x) );
f := 2*3*a*(3^2*x^5 - 2*7*a*x^3 + 3^2*a^2*x);
H := Curve(AS, y^2 - f);

x0 := x/(3*x^2 - a)^2;
sf0 := (3^2*x^2 + a)*y / (2^4*a^2*(3*x^2 - a)^3);
phiOl := map<H -> E | [x0, sf0]>;
x1 := x^3/(x^2 - 3*a)^2;
sf1 := (x^3 + 3^2*a*x)*y / (2^4*a*(x^2 - 3*a)^3);
phiOlPr := map<H -> Epr | [x1, sf1]>;

eta := map<E -> Ea | [
    (2^4*i*a^2)/3*x, 
    (2^5*(i-1)*a^3)/3^2*y ]>;
phi := Normalization(Expand(phiOl*eta));
phi;

etaPr := map<Epr -> Eaa | [
    (2^4*i*a)/3*x, 
    (2^5*(i-1)*a)/3^2*y ]>;
phiPr := Normalization(Expand(phiOlPr*etaPr));
phiPr;




////////////////////////////////////////////////////////////////////////




// Decomposing the covers phiTilde and phiPrTilde
F<i> := QuadraticField(-1);
F<a> := FunctionField(F);
AS<x,y> := AffineSpace(F,2);
Ea := Curve(AS, y^2 - (x^3 - a*x) );
Eaa := Curve(AS, a*y^2 - (x^3 - a*x) );
f := 2*3*a*(3^2*x^5 - 2*7*a*x^3 + 3^2*a^2*x);
H := Curve(AS, y^2 - f);

phiTilde := map<H -> Ea | [
    (3^2*x^2 + a)^2 * (3^2*x^4 - 2*7*a*x^2 + 3^2*a^2) / (2^5*3*a*x*(3*x^2 - a)^2),
    (3^6*x^8 - 2^2*3^5*a*x^6 + 2*3^5*a^2*x^4 - 2^2*7*13*a^3*x^2 + 3^2*a^4)*
    (3^2*x^2 + a)*y / (2^8*3^2*a^2*x^2*(3*x^2 - a)^3)]>;
phiPrTilde := map<H -> Eaa | [
    (x^2 + 3^2*a)^2 * (3^2*x^4 - 2*7*a*x^2 + 3^2*a^2) / (2^5*3*x^3*(x^2 - 3*a)^2),
    (3^2*x^8 - 2^2*7*13*a*x^6 + 2*3^5*a^2*x^4 - 2^2*3^5*a^3*x^2 + 3^6*a^4)* 
    (x^2 + 3^2*a)*y / (2^8*3^2*a*x^5*(x^2 - 3*a)^3) ]>;

phi := map<H -> Ea | [
    2^4*i*a^2*x / (3*(3*x^2 - a)^2),
    2*(i-1)*a*(3^2*x^2 + a)*y / (3^2*(3*x^2 - a)^3) ]>;
phiPr := map<H -> Eaa | [
    2^4*i*a*x^3 / (3*(x^2 - 3*a)^2),
    2*(i-1)*(x^3 + 3^2*a*x)*y / (3^2*(x^2 - 3*a)^3) ]>;

e := map<Ea -> Ea | [
    i*(x^2 - a) / (2*x),
    (1-i)*(x^2 + a)*y / (2*x)^2 ]>;
auto := map<Ea -> Ea | [-x, i*y]>;
phi*e*auto eq phiTilde;

e := map<Eaa -> Eaa | [
    i*(x^2 - a) / (2*x),
    (1-i)*(x^2 + a)*y / (2*x)^2 ]>;
auto := map<Eaa -> Eaa | [-x, i*y]>;
phiPr*e*auto eq phiPrTilde;







/////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
Covers phi: H -> Eb and phiPr: H -> EbPr
/////////////////////////////////////////////////////////////////////////////////////////////////////////////////////







// degree n = 2
F := Rationals();
F<b> := FunctionField(F);
F<c> := FunctionField(F);
PR<t> := PolynomialRing(F);
F<cb> := ext<F | t^3 - b>;

AS<x,y> := AffineSpace(F, 2);
Eb := Curve(AS, y^2 - (x^3 + b) );
Ebc := Curve(AS, c*y^2 - (x^3 + b) );
f := b*c*(c^3*x^6 + 1);
H := Curve(AS, y^2 - f);
phi := map<H -> Eb | [ cb/(c*x^2), y/(c^2*x^3) ]>;
phiPr := map<H -> Ebc | [ c*cb*x^2, y/c ]>;




////////////////////////////////////////////////////////////////////////////




// degree n = 5
F := Rationals();
AS<x,y> := AffineSpace(F,2);
E10 := Curve(AS, y^2 - (x^3 + 10) );
E105 := Curve(AS, 5*y^2 - (x^3 + 10) );
f := 5*(2*x^6 - 3^2*5*x^3 + 2*5^3);
H := Curve(AS, y^2 - f);

phi := map<H -> E10 | [
    5^2*(x^3 - 2^3) / (x^2*(2*x^3 - 5^2)),
    (2^2*x^6 - 5*11*x^3 + 2^4*5^2)*y / (x^3*(2*x^3 - 5^2)^2) ]>;
phiPr := map<H -> E105 | [
    x^2*(2^3*x^3 - 5^3) / (5^2*(x^3 - 2*5)), 
    (2^4*x^6 - 5^2*11*x^3 + 2^2*5^4)*y / (5^4*(x^3 - 2*5)^2) ]>;