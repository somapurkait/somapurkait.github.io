


// solutions to ax^2+bx+c \equiv 0 mod p^r

RootsModPrimePower:=function(a,b,c,p,r);
	if r eq 1 then
		Fp:=GF(p);
		Fx<x>:=PolynomialRing(Fp);
		f:=a*x^2+b*x+c;
		if f eq 0 then
			rts:=[0..(p-1)];
		else
			rts:=Roots(a*x^2+b*x+c);
			rts:=[Integers()!r[1] : r in rts];
		end if;
		return rts;
	else
		rts:=$$(a,b,c,p,r-1);
		rtsnew:=[];
		for y in rts do
			anew:=(a*p^(r-1)) mod p;
			bnew:=(2*a*y+b) mod p;
			cnew:=((a*y^2+b*y+c) div p^(r-1)) mod p;
			zs:=$$(anew,bnew,cnew,p,1);
			rtsnew:=rtsnew cat [(y+z*p^(r-1)) mod p^r : z in zs];
		end for;	
		return rtsnew;
	end if;
end function;

// solutions to ax^2+bx+c \equiv 0 mod N
RootsMod:=function(a,b,c,N);
	assert N gt 1;
	facts:=Factorisation(N);
	M:=1;
	rts:=[0];
	for fact in facts do
		p:=fact[1];
		r:=fact[2];
		rtsNew:=RootsModPrimePower(a,b,c,p,r);
		rtsCRT:=[];
		for R1 in rts do
			for R2 in rtsNew do
				R:=ChineseRemainderTheorem([R1,R2],[M,p^r]);
				Append(~rtsCRT,R);
			end for;
		end for;
		M:=M*p^r;
		rts:=rtsCRT;
	end for;
	return rtsCRT;
end function;
