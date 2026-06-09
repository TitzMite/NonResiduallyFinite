
UOmega := FreeGroup("a", "b", "c");;
a := UOmega.1;; b := UOmega.2;; c := UOmega.3;;

#exotic, A7 quotient, kernel torsionfree
#a->c^2, b->b^2, c->a^2 defines auto
Omega2 := UOmega / [
    [a^3, One(UOmega)],
    [b^3, One(UOmega)],
    [c^3, One(UOmega)],
    [(a * b)^2, b * a],
    [(b * c)^2, c * b],
    [(a * c)^2, c * a]
];;

RelsQ :=
    [
        [a^3, One(UOmega)],
        [b^3, One(UOmega)],
        [c^3, One(UOmega)],
        [(a * b)^2, b * a],
        [(b * c)^2, c * b],
        [(a * c)^2, c * a],
        [c*a*b^-1*c*a*b*c^-1*b*a^-1*b^-1*c^-1*b*a^-1*b,  One(UOmega)]
    ];

Q := UOmega/RelsQ;

psi := GroupHomomorphismByImages(UOmega, Omega2);
phi := GroupHomomorphismByImages(UOmega, Q);

V1 := Group([a^phi, b^phi]);
V2 := Group([b^phi, c^phi]);
V3 := Group([a^phi, c^phi]);

ConstructGAB := function()
    local vertices, rel;
    vertices := Concatenation(RightCosets(Q,V1),RightCosets(Q,V2),RightCosets(Q,V3));
    rel := function(cos1, cos2)
        return Size(Intersection(cos1, cos2)) = 3;
    end;
    return Graph(Q, vertices, OnRight, rel, true);
end;

Reg := Group((b*c*a)^phi, (a*b*c*b)^phi);
RegLift := Group((b*c*a)^psi, (a*b*c*b)^psi);

ConstructRaduGraph := function()
    local e1, e2, e3, vertices1, vertices2, vertices3, rel, iso;
    iso := IsomorphismPermGroup(Q);
    e1 := Group(a^phi);
    e2 := Group(b^phi);
    e3 := Group(c^phi);
    vertices1 := DoubleCosets(Image(iso,Q), Image(iso,e1), Image(iso,Reg));
    vertices2 := DoubleCosets(Image(iso,Q), Image(iso,e2), Image(iso,Reg));
    vertices3 := DoubleCosets(Image(iso,Q), Image(iso,e3), Image(iso,Reg));
    rel := function(v1,v2)
        return Size(Intersection(v1,v2)) = 720;
    end;
    return Graph
        (
            Group(()),
            Concatenation(vertices1, vertices2, vertices3),
            function(x,g) return x; end,
            rel,
            true
        );
end;

radu_graph_induced_by_Reg := ConstructRaduGraph();