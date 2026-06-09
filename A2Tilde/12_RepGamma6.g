
# we assume there is a representation in char 0 mapping e3 to A and g4^-1 to B
# we assume that the characteristic polynomial of A is t^3 - 1/2 t^2 + 1/2 t -1.
# we assume that A is diaogonal, with diagonal entries: 1, (1+sqrt(-15))/4, (1-sqrt(-15))/4,
# we assume that the trace of B is 1/2
# we assume that the trace of AB is 1/2
# we assume that the trace of A^2B is a root of t^2 + 9/4t + 9/2
# we assume that the trace of B^2 is -3/4
# we assume that the trace of AB^2 is a root of t^2 + 9/4t + 9/2
# we assume that the trace of of A^2B^2 is -1/2
# we assume that A,B are element in SL(3,L), with L = Q(sqrt(-15), sqrt(-23))

t_var := Indeterminate(Rationals, "t");

#poly for degree 4 extension 
poly := t_var^4 + 76*t_var^2 + 64;

L := AlgebraicExtension(Rationals, poly, "zeta");
one := One(L);
zero := Zero(L);
zeta := RootOfDefiningPolynomial(L);


u_var := Indeterminate(L, "u");

#(1+sqrt(-15))/2
pol_alpha := u_var^2-u_var+4;
alpha := RootsOfPolynomial(pol_alpha)[1];
#(1+sqrt(-23))/2
pol_beta := u_var^2-u_var+6;
beta := RootsOfPolynomial(pol_beta)[1];

pol_trace_AAB := u_var^2 + 9/4*u_var + 9/2;
traces_AAB := RootsOfPolynomial(pol_trace_AAB);

#eigenvalues of A
lambda2 := -alpha/2;
lambda3 := (alpha-1)/2;

#we get equations in digonal entries of B by considering traces
#of B, A*B, A*A*B

SLE1 := 
[
    [one, one, one],
    [one, lambda2, lambda3],
    [one, lambda2^2, lambda3^2]
];

#two choices since we only know minimal polynomial of trace of A^2*B
v1 :=
    [
        [one/2],
        [one/2],
        [traces_AAB[1]]
    ];
v2 :=
    [   
        [one/2],
        [one/2],
        [traces_AAB[2]]
    ];

diagonal_entries_B1 := Flat(SLE1^-1*v1);
diagonal_entries_B2 := Flat(SLE1^-1*v2);

SLE2 := 
    [
        [2*one, 2*one, 2*one],
        [one+lambda2, one+lambda3, lambda2 + lambda3],
        [one+lambda2^2, one+lambda3^2, lambda2^2 + lambda3^2]
    ];

#trace of A^2*B satisfies t^2 + 9/4 t + 9/2
#trace of A*B^2 satisfies the same polynomial, but it is the other root

#using traces of B^2, A*B^2, A^2*B^2, to get 
#equations in b12*b21, b13*b31, b23*b32

w1 := 
    [
        [-diagonal_entries_B1[1]^2 - diagonal_entries_B1[2]^2 - diagonal_entries_B1[3]^2 - 3/4*one],
        [-diagonal_entries_B1[1]^2 - lambda2*diagonal_entries_B1[2]^2 - lambda3*diagonal_entries_B1[3]^2 + traces_AAB[2]],
        [-diagonal_entries_B1[1]^2 - lambda2^2*diagonal_entries_B1[2]^2 - lambda3^2*diagonal_entries_B1[3]^2 - one/2 ],
    ];

w2 := 
    [
        [-diagonal_entries_B2[1]^2 - diagonal_entries_B2[2]^2 - diagonal_entries_B2[3]^2 - 3/4*one],
        [-diagonal_entries_B2[1]^2 - lambda2*diagonal_entries_B2[2]^2 - lambda3*diagonal_entries_B2[3]^2 + traces_AAB[1]],
        [-diagonal_entries_B2[1]^2 - lambda2^2*diagonal_entries_B2[2]^2 - lambda3^2*diagonal_entries_B2[3]^2 - one/2 ],
    ];

non_diagonal_products1 := Flat(SLE2^-1*w1);
non_diagonal_products2 := Flat(SLE2^-1*w2);

#using determinant = 1 we get

S1 :=
    one
    - (diagonal_entries_B1[1] * diagonal_entries_B1[2] * diagonal_entries_B1[3])
    + diagonal_entries_B1[1]*non_diagonal_products1[3]
    + diagonal_entries_B1[2]*non_diagonal_products1[2]
    + diagonal_entries_B1[3]*non_diagonal_products1[1];

S2 :=
    one
    - (diagonal_entries_B2[1] * diagonal_entries_B2[2] * diagonal_entries_B2[3])
    + diagonal_entries_B2[1]*non_diagonal_products2[3]
    + diagonal_entries_B2[2]*non_diagonal_products2[2]
    + diagonal_entries_B2[3]*non_diagonal_products2[1];

poly_xij1 := u_var^2 - S1*u_var + non_diagonal_products1[1]*non_diagonal_products1[2]*non_diagonal_products1[3];

poly_xij2 := u_var^2 - S2*u_var + non_diagonal_products2[1]*non_diagonal_products2[2]*non_diagonal_products2[3];

gamma := RootsOfPolynomial(poly_xij1)[1];
# gamma := RootsOfPolynomial(poly_xij1)[2];
# gamma := RootsOfPolynomial(poly_xij2)[1];
# gamma := RootsOfPolynomial(poly_xij2)[2];

##################################################
##################################################

ComputeT := function()
    local v1,v2,v3,v4,T;
    v1 := ExtRepOfObj(one);
    v2 := ExtRepOfObj(alpha);
    v3 := ExtRepOfObj(beta);
    v4 := ExtRepOfObj(alpha*beta);
    T := [v1,v2,v3,v4];
    T := TransposedMat(T);
    T := T^-1;
    return T;
end;

T := ComputeT();

ConvinientRep := function(s)
    return T*ExtRepOfObj(s);
end;

#we work with column vectors
DisplayVec := function(v)
    local x;
    for x in v do
        Print(ConvinientRep(x[1]), "\n");
    od;
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

A_alg :=
    [
        [one, zero, zero],
        [zero, lambda2, zero],
        [zero, zero, lambda3]
    ];

B_alg :=
    [
        [diagonal_entries_B1[1], one, one],
        [non_diagonal_products1[1], diagonal_entries_B1[2], gamma/non_diagonal_products1[2]],
        [non_diagonal_products1[2], non_diagonal_products1[2]*non_diagonal_products1[3]/gamma, diagonal_entries_B1[3]]
    ];

#since algebraic_rep is not fail the homomorphism is well defined
algebraic_rep := GroupHomomorphismByImages(gamma6, Group(A_alg,B_alg));
