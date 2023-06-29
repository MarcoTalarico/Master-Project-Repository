 newPackage(
        "HeckeSpechtPolynomials",
        Version => "1.0",
        Date => "June 25, 2023",
        Authors => {{Name => "Marco Talarico"}},
        Headline => "Hecke Specht Polynomials",
        CacheExampleOutput => true,
        UseCachedExampleOutput => true,
        DebuggingMode => true,
        AuxiliaryFiles => true,
        PackageExports => {
        "SpechtModule",
	"PushForward"
        }
        )

export{"vecToBasis"}
export{"MatToBasis"}
export{"isBasis"}
export{"cLen"}
export{"descent"}
export{"red"}
export{"del"}
export{"act"}
export{"actInv"}
export{"Hecke"}
export{"HeckeInv"}
export{"conjTab"}
export{"qRowStabilizer"}
export{"qColStabilizer"}
export{"permTableaux"}
export{"firstTab"}
export{"lastTab"}
export{"qYoungSymPar"}
export{"qSpechtPolynomial"}
export{"qSpechtFromPartition"}
export{"qSpechtPolynomialSet"}
export{"eleSym"}
export{"Sn"}
export{"parToMat"}

-- Push Forward Function to check if we indeed obtain a basis
vecToBasis = method(TypicalValue => Matrix)
vecToBasis (RingElement,List) := (polVect,polSet) -> (
      if #polSet == 0 then return "Polynomial basis must not be empty";
      phi := map(coefficientRing ring polVect, ring polVect);
      mon := toList set flatten apply(polSet, p -> flatten entries monomials p);
      vSet := {};
      for p in polSet do (
	  vSet = append(vSet, ((coefficients(p, Monomials => mon)))_1);
	  );
      v := vSet_0;  
      for i from 1 to #polSet-1 do (
	  v = v|((vSet)_i);
	  );
      v = phi v;
      pVect := phi (coefficients(polVect, Monomials => mon))_1;
      return solve(v,pVect);     
      )

MatToBasis = method(TypicalValue => Matrix)
MatToBasis (List,List) := (pVectSet,polSet) -> (
    if #polSet == 0 then return "Polynomial basis must not be empty";
    if #pVectSet == 0 then return "Polynomial set must not be empty";
    vList := apply(pVectSet, p->vecToBasis(p,polSet));
    v := vList_0;
    for i from 1 to #vList-1 do (
	 v = v|((vList)_i);
	 );
    return v;
    )

isBasis = method(TypicalValue => Matrix)
isBasis (List,Ring) := (polSet,R) -> (
    (T,TtoR,Tgens) := Sn R;
    pBasis := flatten entries (pushFwd(TtoR))_1;
    ide := ideal Tgens;
    pId := apply(polSet,f->f%ide);
    MAT := MatToBasis(pId,pBasis);
    try (inverse MAT) then (print "Polynomial set is a basis") else (print "Polynomial set is not a basis");
    return MAT;
    )
    

-- length of reduced word of a given permutation:
cLen = method(TypicalValue => ZZ)
cLen (List) := (l) -> (
    len := 0;
    if #l==1 then return len;
    for i from 0 to #l-2 do (
	for j from i+1 to #l-1 do (
	    if l_i > l_j then len=len+1;
	    );
	);
    return len;
    )

-- Descent of a permutation
descent = method(TypicalValue => List)
descent (List) := (l) -> (
    dec := {};
    if #l<=1 then return dec;
    for i from 0 to #l-2 do (
	if l_i > l_(i+1) then dec=append(dec,i);
	);
    return dec;
    )
        
-- Transposition (i,i+1) in Sn
s = (i,n) -> (
    perm := {};
    for j from 0 to n-1 do (
	if (j<i or j>i+1) then perm = append(perm,j);
	if j==i then perm = append(perm,j+1);
	if j==i+1 then perm = append(perm,j-1);
	);
    return perm;
    )


-- reduced word given as a list of indices of transpositions
red = method(TypicalValue => List)
red (List) := (p) -> (
    N := #p;
    D := descent(p);
    reduced := {};
    while cLen(p) > 0 do (
	for i in D do (
	    if cLen(p_(s(i,N))) < cLen(p) then (
		p = p_(s(i,N));
		reduced = append(reduced,i);
		D = descent(p);
		break;
		);
	    );
	);
    return reverse reduced;
    )
    

-- divided difference operator
del = method(TypicalValue => RingElement)
del (RingElement,ZZ) := (f,i) -> (
    R := ring f;
    x := gens R;
    g := permutePolynomial(s(i,#x),f);
    return (f-g)//(x_i-x_(i+1));
    )

-- action of Ti in the polynomial ring
act = method(TypicalValue => RingElement)
act (RingElement,RingElement,ZZ) := (q,f,i) -> (
    R := ring f;
    x :=gens R;
    return(del(x_i*f,i)*(q-1)+permutePolynomial(s(i,#x),f));
    )

actInv = method(TypicalValue => RingElement)
actInv (RingElement,RingElement,ZZ) := (q,f,i) -> (
    q = (map(coefficientRing ring f, ring f)) q;
    return (1/q)*(act(q,f,i)+(1-q)*f);
    )

-- the action defined for any permutation given its reduced word T_p = T_i_1...T_i_k
Hecke = method(TypicalValue => RingElement)
Hecke (RingElement,RingElement,List) := (q,f,p) -> (
    g := f;
    desc := reverse red p;
    for i in desc do (
	g = act(q,g,i);
	);
    return g;
    )

HeckeInv = method(TypicalValue => RingElement)
HeckeInv (RingElement,RingElement,List) := (q,f,p) -> (
    g := f;
    desc := red p;
    for i in desc do (
	g = actInv(q,g,i);
	);
    return g;
    )

------ Some Tableaux functions

-- Conjugate of a Tableaux
conjTab = method(TypicalValue => YoungTableau)
conjTab (YoungTableau) := (tab) -> (
    if (#tab == 0) then (return tab);
    entrie := flatten toList apply(0..numColumns(tab)-1,i->tab_i);
    listPar := apply(0..numColumns(tab)-1, i->#tab_i);
    par := new Partition from listPar;
    tab = youngTableau(par,entrie);
    sortColumnsTableau youngTableau(par,entrie);
    return tab
    )


-- q-row stabilizer defined in dipper and james
qRowStabilizer = method(TypicalValue=>List)
qRowStabilizer (RingElement,YoungTableau) := (q,tab) -> (
    N := size tab;
    rT := rowStabilizer(tab);
    appList := {};
    for r in rT do (
	appList = append(appList,{1,r});
	);
    return appList;
    )

-- q-column stabilizer defined in dipper and james
qColStabilizer = method(TypicalValue => List)
qColStabilizer (RingElement,YoungTableau) := (q,tab) -> (
    N := size tab;
    cT := columnStabilizer(tab);
    appList := {};
    l := 0;
    for c in cT do (
	l = cLen(c);
	appList = append(appList,{(-q)^(-l),c});
	);
    return appList;
    )

permTableaux = method(TypicalValue => List)
permTableaux (YoungTableau,YoungTableau) := (tab1,tab2) -> (
    lis := toList (0..size tab1-1);
    T1 := entries tab1;
    T2 := entries tab2;
    perm := {};
    for i in lis do (
	perm = append(perm, T2_(position(T1,j->j==i)));
	);
    return perm;
    )

firstTab = method(TypicalValue => YoungTableau)
firstTab (Partition) := (par) -> (
    N := sum toList par;
    return youngTableau(par, toList (0..N-1));
    )

lastTab = method(TypicalValue => YoungTableau)
lastTab (Partition) := (par) -> (
    parC := conjugate par;
    return conjTab firstTab parC;
    )

-- q-version of the young symmetrizer also from dipper and james
qYoungSymPar = method(TypicalValue => RingElement)
qYoungSymPar (RingElement,YoungTableau,RingElement) := (q,tab,pol) -> (
     par := tab#partition;
     fT := firstTab par;
     lT := lastTab par;
     Wn := permTableaux(lT,tab);
     Wp := permTableaux(fT,tab);
     qRT := qRowStabilizer(q,fT);
     qCT := qColStabilizer(q,lT);
     SUM := {};
     qYS := {};
     for C in qCT do (
	 for R in qRT do (
	     qYS = append(qYS,{C_0,R_1,C_1});
	     );
	 );
     elt := 1_(ring pol);
     for E in qYS do (
	 elt = pol;
	 elt = HeckeInv(q,elt,Wp);
	 elt = Hecke(q,elt,E_1);
	 elt = Hecke(q,elt,Wp);
	 elt = HeckeInv(q,elt,Wn);
	 elt = Hecke(q,elt,E_2);
	 elt = Hecke(q,elt,Wn);
	 SUM = append(SUM,E_0*elt);
	 );
     return sum SUM;
     )
 
-- Specht Polynomials
qSpechtPolynomial = method(TypicalValue => RingElement)
qSpechtPolynomial (RingElement,YoungTableau,YoungTableau,Ring) := (q,tab1,tab2,rng) -> (
     par := tab1#partition;
     fT := firstTab par;
     mon := indexMonomial(tab2,tab1,rng);
     hsp := qYoungSymPar(q,tab1,mon);
     return hsp;
     )

qSpechtPolynomial (RingElement,YoungTableau,Ring) := (q,tab,rng) -> (
    tabList := toListOfTableaux standardTableaux (tab#partition);
    return apply(tabList, TAB -> qSpechtPolynomial(q,TAB,tab,rng));
    )

qSpechtPolynomial (RingElement,Ring) := (q,rng) -> (
    n := numgens rng;
    return apply(flatten apply(partitions n, i ->  (toListOfTableaux standardTableaux i)), i -> qSpechtPolynomial(q,i,rng));
    )


-- Testing
eleSym = method(TypicalValue => RingElement);
eleSym (List) := (var) -> (
    n := #var;
    elem := toList apply(1..n, i->(sum(apply(subsets(1..n,i), j -> (times(toSequence apply(j, k -> var_(k-1))))))));   
    return elem;
    )

Sn = method(TypicalValue => List);
Sn (Ring) := (rng) -> (
    x := gens rng;
    kk := coefficientRing rng;
    n := numgens rng;
    Tgens := (eleSym(gens rng))_{0..(n-1)};
    f := symbol f;
    T := kk[f_1..f_n,Degrees => {1..n}];
    TtoS := map(rng,T,Tgens);
    return (T,TtoS,Tgens))

parToMat = method(TypicalValue => List)
parToMat (List) := (par) -> (
    p := symbol p;
    rng := frac(QQ[p]);
    n := sum(par);
    x := symbol x;
    R := rng[x_1..x_n];
    use R;use rng;
    par = new Partition from par;
    tab := firstTab par;
    hspList := qSpechtPolynomial(p,tab,R);
    HSPset := apply(toList(0..n-2), i-> apply(flatten hspList, f -> act(p,f,i)));
    MAT := apply(HSPset, L -> MatToBasis(L,hspList));
    for m in MAT do (
	print m;
	print "";
	);
    return (R,hspList,MAT);
    )













