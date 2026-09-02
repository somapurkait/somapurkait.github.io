
//This program compute the space S_{k/2}(N,chi,phi) given a newform phi, level N, quadratic character chi, and k -- 
// the function is shimuraLiftSpaces(chi,k : prec:=8000)






//--------------------------------------------------------------------



//thetaforms is a function which gives the theta functions 
// which generate a space which under Shimura map doesn't go to cusp form of integral weight 
// chi is a quadratic character

thetaforms := function(chi);
		N:=Modulus(chi);  
		assert Order(chi) in [1,2];
		assert IsDivisibleBy(N,4);         
        A:=[* *];
        M:= Integers()!(N/4);
		rtpairs:=[<r,t> : r,t in Divisors(M) | IsDivisibleBy(M, r^2*t)];
		for rt in rtpairs do
			r,t:=Explode(rt);
			Gr := DirichletGroup(r^2);
			EGr:=Elements(Gr);
			for psi in EGr do
				if Order(psi) in [1,2] then
					if (psi(-1) eq -1) and (Conductor(psi) eq r) then
						if &and[ chi(x) eq KroneckerSymbol(-4*t,x)*psi(x)   : x in [1..N] | GCD(x,N) eq 1   ] then
							A:=A cat [* [* psi,r,t *] *];
						end if;
					end if;
				end if;
			end for;
		end for;	
  		return A;
end function;
                     
//------------------------------------------------------

//This function gives first prime which is coprime to a given N                                 

coprime := function(N);
p:=1;
while true do
	   p:=NextPrime(p);
if GCD(p,N) eq 1 then
return p;
end if;
end while;
end function;                  
                     
                  
//-----------------------------------------------------------------

eigenEmbedding:=function(lambdap,j);
	K:=Parent(lambdap);
	if K eq Rationals() then
		return lambdap;
	else
		return RealEmbeddings(lambdap)[j];
	end if;	
end function;



// N level
// Gives primes p_1,...,p_r
// such that to check an element of S_{k/2}(N,\chi) is an eigenform (with \chi quadratic),
// enough to check this for T_{p_1^2},...,T_{p_r^2} 

primeschk:=function(N,k);
	M:=N div 2;
	forms:=[* *];
	for d in Divisors(M) do
		NFs:=Newforms(CuspForms(d, (k-1)));
		for j in [1..#NFs] do
			class:=NFs[j];
                        //print d, #NFs, j, #class;
			forms:=forms cat [* class[1] *];
		end for;
	end for;
        //print forms;
	pairs:=[];
	n:=#forms;
	for i in [1..n] do
		Ki:=Parent(Coefficient(forms[i],0));
		di:=Degree(Ki);
		for j in [1..di] do
			Append(~pairs,<i,j>);
		end for;
	end for;
	//print pairs;
	quads:=[];
	for pair1, pair2 in pairs do
		if (pair1[1] lt pair2[1]) or (pair1[1] eq pair2[1] and pair1[2] lt pair2[2]) then
			Append(~quads,<pair1[1],pair1[2],pair2[1],pair2[2]>);
		end if;
	end for;			
	//print(quads);
	p:=2;
	prs:=[];
	while #quads ne 0 do
		p:=NextPrime(p);	
		//print p;
		if GCD(p,N) eq 1 then
			for quad in quads do
				i1,j1,i2,j2:=Explode(quad);
				lambda1:=eigenEmbedding(Coefficient(forms[i1],p),j1);
				lambda2:=eigenEmbedding(Coefficient(forms[i2],p),j2);
				if AbsoluteValue(lambda1-lambda2) gt 10^(-5) then
					Include(~prs,p);
					Exclude(~quads,quad);
					//print quads;
				end if;
			end for;
		end if;
	end while;
	return prs;
end function;

//--------------------------------------------------------------------

coeff:=function(S,v,n);
    if IsIntegral(n) then
        n:=Integers()!n;
lc:=&+[v[i]*Coefficient(S[i],n) : i in [1..#S]];
        return Parent(v[1])!lc;
    else
        return Parent(v[1])!0;
    end if;
end function;


//---------------------------------------------------------------------

shimuraLiftSpaces:=function(chi, k : prec:=8000);
	N:=Modulus(chi);
	G:=Parent(chi);
	assert chi^2 eq G!1;
	assert IsDivisibleBy(N,4);
     k1:=Integers()!((k-1)/2);
	A:=[* *];
	mults:=[];
	for d in Divisors(N div 2) do
		nfsd:=Newforms(CuspForms(d, (k-1)));
		for c in nfsd do
			A:=A cat [* c[1] *];
			mults:=mults cat [#c];
		end for;
	end for;	
	print mults;
        print A;
	S:=Basis(CuspidalSubspace(HalfIntegralWeightForms(chi,k/2)),prec);
//S:=BaseExtend(S,RationalField());				
        print "dimension is", #S;
	d:=#S;
	d0:=#thetaforms(chi);
        print "dimension of thetaforms is", d0;
	Vs:=[  VectorSpace( Parent(Coefficient(phi,1)) , d)      :  phi in A   ];
	Zs:=[ VectorSpace( Parent(Coefficient(phi,1)) , 1)      :  phi in A   ];
	Us:=Vs;
	pr:=primeschk(N,k);
        if #pr eq 0 then
	   Append(~pr, coprime(N));
        end if;
        print "primes", pr; 

	pairs:=[<p,n> : p in pr, n in [1..(prec-1)] | p^2*n lt prec];
	fn:=func<x,y | x[1]^2*x[2]-y[1]^2*y[2]>;
	Sort(~pairs,fn);
	for pair in pairs do
	    p,n:=Explode(pair);
		chip:=Rationals()!chi(p);
		Usnew:=[* *];
		for i in [1..#A] do
			phi:=A[i];
			V:=Vs[i];
			U:=Us[i];
			Z:=Zs[i];
    		lamp:=Coefficient(phi,p);
        	dimU:=Dimension(U);
			bas:=[Eltseq(V!(U.i)) : i in [1..dimU]];
	        h:=[ (coeff(S,bas[i],p^2*n)+(chip*KroneckerSymbol(((-1)^k1*n),p)*(p^(k1-1))-lamp)*coeff(S,bas[i],n) + chip^2*(p^(k-2))*coeff(S,bas[i],n/p^2))*Z.1 : i in [1..dimU]  ];
    	    hm:=hom<U->Z | h>;
        	Unew:=Kernel(hm);
 	       	U:=sub<V | [V!u: u in Basis(Unew)]  >;
			Usnew:=Usnew cat [* U *];
		end for;
		Us:=Usnew;

		dims:=[d0] cat [Dimension(Us[i])*mults[i] : i in [1..#A]];
		dsum:=&+dims;
		print pair, dims,dsum;
		assert dsum ge d;
		if dsum eq d then
			return S, A, [*  [ Eltseq(Vs[i]!u)  : u in Basis(Us[i])  ]   : i in [1..#A]  *];
		end if;	
	end for;
	// precision insufficient
	prec0:=2*prec;
	print "doubling precision to", prec0;
        return $$(chi,k : prec:=prec0);
end function;
















