
F := FreeGroup("a","b","c","x","y","z");
AssignGeneratorVariables(F);

RelsRadu :=
    [
        a^2, b^2, c^2, x^2, y^2, z^2,
        a * x * a * x,
        a * y * a * y,
        a * z * b * z,
        b * x * b * x,
        b * y * c * y,
        c * x * c * z
    ];

Radu33 := F/RelsRadu;

pro := GroupHomomorphismByImages(F,Radu33);

Der := Group([(a*b*x*y*x*y)^pro, (b*a)^pro]);
phi := IsomorphismFpGroupByGenerators(Der, GeneratorsOfGroup(Der));
FP := Image(phi);

LiftsElement := function(elm)
    local n, p, x, lifts;
    n := Size(DefaultRing(elm));
    if n<2 then
        n := Size(DefaultField(elm));
    fi;
    p := Factors(n)[1];
    if elm = 0*elm then
        x := 0;
    else
        x := Int(elm);
    fi;
    lifts := List([0..p-1], i->ZmodnZObj(x+n*i, n*p));
    return lifts;
end;

#for 2 by 2 matricess
LiftMatrix := function(mat)
    local l11, l12, l13, l21, l22, l23, l31, l32, l33,
    a11, a12, a13, a21, a22, a23, a31, a32, a33,
    lifts, M;
    l11 := LiftsElement(mat[1][1]);
    l12 := LiftsElement(mat[1][2]);
    l21 := LiftsElement(mat[2][1]);
    l22 := LiftsElement(mat[2][2]);
    lifts := [];
    for a11 in l11 do
        for a12 in l12 do
            for a21 in l21 do   
                for a22 in l22 do
                    M := [
                        [a11, a12],
                        [a21, a22]
                    ];
                    Add(lifts, M);
                od;
            od;
        od;
    od;
    return SSortedList(lifts);
end;

Tietzes := List(RelatorsOfFpGroup(FP), r->TietzeWordAbstractWord(r, FreeGeneratorsOfFpGroup(FP)));

#for 2 by 2 matricess
CheckTietzeRelations := function(a, b)
    local prod, rel, admissible, x, r;
    r := DefaultRing(a[1][1]);
    if Size(r) < 2 then
        r := DefaultField(a[1][1]);
    fi;
    admissible := true;
    for rel in Tietzes do
        prod := DiagonalMat([One(r),One(r)]);
        for x in rel do
            if x = 1 then
                prod := prod * a;
            elif x = -1 then
                prod := prod * a^-1;
            elif x = 2 then
                prod := prod * b;
            elif x = -2 then
                prod := prod * b^-1;
            fi;
        od;
        admissible := DiagonalMat([One(r),One(r)]) = prod;
        if admissible = false then
            return admissible;
        fi;
    od;
    return admissible;
end;

PolyFromCoeffs := function(c)
    local z, p;
    z := Indeterminate(Rationals, "z");
    p := c[1]*z^2 + c[2]*z + c[3]*z^0;
    return p;
end;

all_polys := Concatenation(
    Cartesian([1],[-80..80]*(1/8), [-80..80]*(1/8)),
    Cartesian([0],[1],[-160..160]*(1/16)) 
);

polys := all_polys;

MinimalPolys := function(elm)
    local a, b, k, n,x, p, goods;
    n := Size(DefaultRing(elm));
    if n<2 then
        n := Size(DefaultField(elm));
    fi;
    goods := Filtered(polys, p->(p[1]*elm^2+p[2]*elm+p[3]) = 0*elm);
    goods := Filtered(goods, p-> Size(Factors(PolyFromCoeffs(p))) = 1);
    return goods;
end;

LiftPair := function(a, b)
    local liftsa, liftsb, pairs, x,y,z, pi, i, n, j, m, tau, minpols;
    Print("Lifting a pair...\n\n");
    liftsa := LiftMatrix(a);
    liftsa := Filtered(liftsa, x -> IsUnit(Determinant(x)));
    liftsa := Filtered(liftsa, x -> Determinant(x)^0 = Determinant(x));
    Print("We have ", Size(liftsa), " potential left lifts.\n\n");
    if liftsa = [] then
        Print("checked all pairs...\n\n");
        Print("\n-----------------\n\n");
        return 0;
    else
        liftsb := LiftMatrix(b);
        liftsb := Filtered(liftsb, x -> IsUnit(Determinant(x)));
        liftsb := Filtered(liftsb, x -> Determinant(x)^0 = Determinant(x));
        Print("We have ", Size(liftsb), " potential right lifts.\n\n");
        pairs := [];
        n := Size(liftsa);
        pi := Random(SymmetricGroup(n));
        m := Size(liftsb);
        tau := Random(SymmetricGroup(m));
        for i in [1..n] do
            x := liftsa[i^pi];
            for j in [1..m] do
                y := liftsb[j^tau];
                if CheckTietzeRelations(x,y) then
                    Print("We found an admissible pair:\n");
                    Display(x);
                    minpols := MinimalPolys(Trace(x));
                    if Size(minpols) = 1 then
                        Print("Trace is probably root of ", minpols[1],".\n");
                    fi;
                    Print("\n");
                    Display(y);
                    minpols := MinimalPolys(Trace(y));
                    if Size(minpols) = 1 then
                        Print("Trace is probably root of ", minpols[1],".\n");
                    fi;
                    minpols := MinimalPolys(Trace(x*y));
                    if Size(minpols) = 1 then
                        Print("\n");
                        Print("Trace of product is probably root of ", minpols[1],".\n");
                    fi;
                    Print("\n");
                    z := LiftPair(x,y);
                    if z=0 then
                        break;
                    fi;
                fi;
            od;
        od;
        Print("checked all pairs...\n\n");
        Print("\n-----------------\n\n");
        return 1;
    fi;
end;

# this is not the only choice but one that works well
A13 := [ [ 0*Z(13), Z(13)^2 ], [ Z(13)^4, Z(13)^5 ] ];
B13 := [ [ 0*Z(13), Z(13)^6 ], [ Z(13)^0, Z(13)^10 ] ];

# run LiftPair(A13, B13) to get lifts and minimal polynomials of the traces

# we computed Hensel lifts
A13_hensel :=
    [
        [   590720,  3922260 ],
        [  4437410,  1822684 ]
    ]*ZmodnZObj(1, 4826809);

B13_hensel :=
    [
        [  3527706,  2050255 ],
        [  1690625,  1118855 ]
    ]*ZmodnZObj(1, 4826809);

##################################################
##################################################

# constructing a representation from the traces

t := Indeterminate(Rationals, "t");
poly := t^4 - 4*t^2 + 1024;
K := AlgebraicExtension(Rationals, poly, "zeta");
one := One(K); 
zero := Zero(K);
zeta := RootOfDefiningPolynomial(K);

u := Indeterminate(K, "u");

# the trace of A13_hensel is -1/2
# the traces of B_13_hensel and B_13_hensel*A13_hensel
# both satisfy t^2 + t/2 - 1 = 0
# but these traces are distinct

# we have two roots of t^2 + t/2 + 1 in K
alpha1 := -1/256*zeta^3-7/64*zeta-1/4;
alpha2 :=  1/256*zeta^3+7/64*zeta-1/4;

# we have two roots of t^2 + t/2 - 1 in K
beta1 := -1/256*zeta^3+9/64*zeta-1/4;
beta2 := 1/256*zeta^3-9/64*zeta-1/4;

# we assume that there are lifts A, B of A13 and B13
# A is diagonalizable over K the eigenvalues are alpha1 and alpha2
# we assume that A is diagonal and compute the diagonal entries of B
# by considering the trace of B and of A*B

A := DiagonalMat([alpha1, alpha2]);

M := [[1,1],[alpha1, alpha2]]*one;

# that choice works
TrB := beta1;
TrAB := beta2;

# column vector
v := [[TrB], [TrAB]];

diagonal_entries := Flat(M^-1*v);
b11 := diagonal_entries[1];
b22 := diagonal_entries[2];

B := 
    [
    [b11, 1],
    [b11*b22 - 1, b22]
    ]*one;

# it works
phi := GroupHomomorphismByImages(Der, Group(A,B));

####################################
####################################

sqrt_neg15 := (zeta^3 + 28*zeta)/64;
sqrt_17  := (zeta^3 - 36*zeta)/64;

ComputeT := function()
    local v1,v2,v3,v4,T;
    v1 := ExtRepOfObj(one);
    v2 := ExtRepOfObj(sqrt_neg15);
    v3 := ExtRepOfObj(sqrt_17);
    v4 := ExtRepOfObj(sqrt_neg15*sqrt_17);
    T := [v1,v2,v3,v4];
    T := TransposedMat(T);
    T := T^-1;
    return T;
end;

T := ComputeT();

ConvinientRep := function(s)
    return T*ExtRepOfObj(s);
end;

DisplayMat := function(m)
    local row, x, rep, width, len;
    # determine maximal width
    width := 0;
    for row in m do
        for x in row do
            rep := ConvinientRep(x);
            len := Length(String(rep));
            if len > width then
                width := len;
            fi;
        od;
    od;
    width := width + 2;   # spacing between columns
    # print matrix
    for row in m do
        for x in row do
            rep := ConvinientRep(x);
            len := Length(String(rep));
            Print(rep);
            Print(String(List([1..width-len], i -> ' ')));
        od;
        Print("\n");
    od;
end;

# run DisplayMat(A) and DisplayMat(B) to display the results

####################################
####################################

LoadPackage("kbmag");

rws := KBMAGRewritingSystem(Radu33);
KnuthBendix(rws);

# run the following command to verify the claim about the shortests elements in the finite residual

short_elements_in_finite_residual := function()
    local words;
    words := EnumerateReducedWords(rws, 1, 8);
    words := Filtered(words, w->w^pro in Der);
    return Filtered(words, w-> (w^pro)^phi = One(Group(A,B))); 
end;